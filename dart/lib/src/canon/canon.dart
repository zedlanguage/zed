/// The canonicalizer (DESIGN.md sec:ir, "Identity", fixed by step M0.7): the rewrite rules
/// that bring a definition to its normal form, and the content address, the BLAKE3-256 hash
/// of the normal form's serialization.
///
/// Four rules, each with a rank that it decreases and that no later rule raises, so every
/// sequence of rewrites ends; and the rules commute, so it ends at one normal form:
///
/// 1. `binders`: rename the first local binder in preorder that carries its written name to
///    its de Bruijn level, and record the written name as a hint facet;
/// 2. `hints`: drop a hint facet, a facet that names but does not mean;
/// 3. `facets`: swap two neighboring facets out of order, or drop one of two equal ones;
/// 4. `domain`: replace the domain by its normal form.
///
/// [canonicalize] computes the normal form in one pass, linear in the size of the definition
/// plus a sort of its facets; the step tests check that it agrees with the rules applied one
/// at a time in any order. [version] tags the rule set: the address of a definition depends on
/// it, so a change to a rule is a new version and never silently a new address.
library;

import 'dart:convert';
import 'dart:typed_data';

import '../../address.dart';
import '../kernel/term.dart';
import '../kernel/text.dart';
import '../kernel/value.dart';
import 'binders.dart' as binders;
import 'blake3.dart';
import 'domain.dart';
import 'serial.dart';

/// The version of the rule set and the serialization.
const version = 2;

/// A facet of a definition: a kind and a value. A hint names something (a written binder name,
/// a doc string) and never changes the meaning, so the normal form drops it. Facets are
/// ordered by hint, then kind, then value.
final class Facet implements Comparable<Facet> {
  final bool hint;
  final String kind;
  final Value value;

  const Facet(this.kind, this.value, {this.hint = false});

  @override
  int compareTo(Facet other) {
    if (hint != other.hint) return hint ? 1 : -1;
    final c = compareUtf8(kind, other.kind);
    return c != 0 ? c : value.compareTo(other.value);
  }

  @override
  bool operator ==(Object other) => other is Facet && compareTo(other) == 0;

  @override
  int get hashCode => Object.hash(hint, kind, value);

  @override
  String toString() => '${hint ? 'hint ' : ''}$kind $value';
}

/// A definition: its name, the integer facts of its declared type if it has any, its facets,
/// and its body.
final class Def {
  final String name;
  Domain? domain;
  final List<Facet> facets;
  Term body;

  Def(this.name, this.body, {this.domain, List<Facet>? facets}) : facets = facets ?? [];

  /// A copy whose facet list the rules may change apart from this one's.
  Def copy() => Def(name, body, domain: domain, facets: [...facets]);

  @override
  bool operator ==(Object other) =>
      other is Def &&
      other.name == name &&
      other.domain == domain &&
      _sameList(other.facets, facets, (a, b) => a == b) &&
      sameTerm(other.body, body);

  @override
  int get hashCode => Object.hash(name, domain, Object.hashAll(facets));

  @override
  String toString() => 'Def($name, $domain, $facets)';
}

/// A rewrite rule: `apply` rewrites the definition in place once and says whether it applied;
/// `rank` is the measure it decreases.
final class Rule {
  final String name;
  final bool Function(Def) apply;
  final int Function(Def) rank;

  const Rule(this.name, this.apply, this.rank);
}

/// The rules, in the order of the ranks: a rule never raises the rank of an earlier one.
final rules = <Rule>[
  Rule('binders', (d) {
    final (body, index, written) = binders.step(d.body) ?? (null, 0, '');
    if (body == null) return false;
    d.body = body;
    d.facets.add(Facet('binder', Tuple([Int(index), Str(written)]), hint: true));
    return true;
  }, (d) => binders.written(d.body)),
  Rule('hints', (d) {
    final i = d.facets.indexWhere((f) => f.hint);
    if (i < 0) return false;
    d.facets.removeAt(i);
    return true;
  }, (d) => d.facets.where((f) => f.hint).length),
  Rule('facets', (d) {
    final f = d.facets;
    for (var i = 0; i + 1 < f.length; i++) {
      final c = f[i].compareTo(f[i + 1]);
      if (c == 0) {
        f.removeAt(i);
        return true;
      }
      if (c > 0) {
        final t = f[i];
        f[i] = f[i + 1];
        f[i + 1] = t;
        return true;
      }
    }
    return false;
  }, (d) => _inversions([...d.facets]) + d.facets.length),
  Rule('domain', (d) {
    final dom = d.domain;
    if (dom == null || dom.rank == 0) return false;
    d.domain = dom.normal();
    return true;
  }, (d) => d.domain?.rank ?? 0),
];

/// The pairs of `f` out of order, equal facets not counted, by merge sort; sorts `f`.
int _inversions(List<Facet> f) {
  if (f.length < 2) return 0;
  final mid = f.length ~/ 2;
  final (left, right) = (f.sublist(0, mid), f.sublist(mid));
  var n = _inversions(left) + _inversions(right);
  var (i, j, k) = (0, 0, 0);
  while (i < left.length && j < right.length) {
    if (right[j].compareTo(left[i]) < 0) {
      n += left.length - i;
      f[k++] = right[j++];
    } else {
      f[k++] = left[i++];
    }
  }
  while (i < left.length) {
    f[k++] = left[i++];
  }
  while (j < right.length) {
    f[k++] = right[j++];
  }
  return n;
}

/// The rank of every rule, in order.
List<int> ranks(Def d) => [for (final r in rules) r.rank(d)];

/// The normal form of `d`: the definition no rule rewrites, reached from `d` in one pass.
Def canonicalize(Def d) {
  final facets = [
    for (final f in d.facets)
      if (!f.hint) f,
  ]..sort();
  return Def(
    d.name,
    binders.canonical(d.body),
    domain: d.domain?.normal(),
    facets: [
      for (var i = 0; i < facets.length; i++)
        if (i == 0 || facets[i] != facets[i - 1]) facets[i],
    ],
  );
}

/// The content address of `d` under the current [version]. `refs` gives the address of each
/// free variable that names a definition.
ContentAddress address(Def d, Refs refs) => addressAt(version, d, refs);

/// The content address of `d` under the rule set `version`.
ContentAddress addressAt(int version, Def d, Refs refs) => ContentAddress(
  blake3(
    (BytesBuilder(copy: false)
          ..add(utf8.encode('zed-canon\u0000'))
          ..add(_u32(version))
          ..add(serialize(canonicalize(d), refs)))
        .takeBytes(),
  ),
);

/// The serialization of `d`, which should be in normal form.
Uint8List serialize(Def d, Refs refs) => serializeDef(d, refs);

/// The address of a unit: the hash of its exports, each a name and the address of its
/// definition, in name order.
ContentAddress unitAddress(List<(String, ContentAddress)> exports) {
  final sorted = [...exports]
    ..sort((a, b) {
      final c = compareUtf8(a.$1, b.$1);
      return c != 0 ? c : a.$2.compareTo(b.$2);
    });
  final b = BytesBuilder(copy: false)
    ..add(utf8.encode('zed-unit\u0000'))
    ..add(_u32(version))
    ..add(_u64(sorted.length));
  for (final (name, address) in sorted) {
    final bytes = utf8.encode(name);
    b
      ..add(_u64(bytes.length))
      ..add(bytes)
      ..add(address.bytes);
  }
  return ContentAddress(blake3(b.takeBytes()));
}

Uint8List _u32(int n) => (ByteData(4)..setUint32(0, n, Endian.little)).buffer.asUint8List();

Uint8List _u64(int n) => (ByteData(8)..setInt64(0, n, Endian.little)).buffer.asUint8List();

bool _sameList<T>(List<T> a, List<T> b, bool Function(T, T) same) {
  if (a.length != b.length) return false;
  for (var i = 0; i < a.length; i++) {
    if (!same(a[i], b[i])) return false;
  }
  return true;
}

bool _sameEvidence(Evidence a, Evidence b) =>
    a.length == b.length && a.entries.every((e) => b[e.key] == e.value);

bool _samePattern(Pattern a, Pattern b) => switch ((a, b)) {
  (WildP(), WildP()) || (AnyAtomP(), AnyAtomP()) => true,
  (BindP(name: final x), BindP(name: final y)) => x == y,
  (LitP(value: final x), LitP(value: final y)) => x == y,
  (AtomP(name: final m, args: final p), AtomP(name: final n, args: final q)) =>
    m == n && _sameList(p, q, _samePattern),
  (TupleP(items: final p), TupleP(items: final q)) => _sameList(p, q, _samePattern),
  (FieldsP(name: final m, fields: final p), FieldsP(name: final n, fields: final q)) =>
    m == n && _sameList(p, q, (x, y) => x.$1 == y.$1 && _samePattern(x.$2, y.$2)),
  _ => false,
};

/// Whether two terms are the same tree, names included.
bool sameTerm(Term a, Term b) {
  bool all(List<Term> p, List<Term> q) => _sameList(p, q, sameTerm);
  return switch ((a, b)) {
    (Lit(value: final x), Lit(value: final y)) => x == y,
    (Var(name: final x), Var(name: final y)) => x == y,
    (Lam(params: final p, body: final s), Lam(params: final q, body: final t)) =>
      _sameList(p, q, (x, y) => x == y) && sameTerm(s, t),
    (App(f: final f, args: final p), App(f: final g, args: final q)) => sameTerm(f, g) && all(p, q),
    (PrimApp(prim: final f, args: final p), PrimApp(prim: final g, args: final q)) =>
      f == g && all(p, q),
    (PrimFn(prim: final f), PrimFn(prim: final g)) => f == g,
    (Let(), Let()) && (final Let x, final Let y) =>
      x.name == y.name && sameTerm(x.value, y.value) && sameTerm(x.body, y.body),
    (If(), If()) && (final If x, final If y) => all(
      [x.cond, x.then, x.orElse],
      [y.cond, y.then, y.orElse],
    ),
    (Match(), Match()) && (final Match x, final Match y) =>
      sameTerm(x.scrutinee, y.scrutinee) &&
          _sameList(x.arms, y.arms, (p, q) => _samePattern(p.$1, q.$1) && sameTerm(p.$2, q.$2)),
    (Fam(), Fam()) && (final Fam x, final Fam y) =>
      x.variable == y.variable && sameTerm(x.domain, y.domain) && sameTerm(x.body, y.body),
    (Reindex(), Reindex()) && (final Reindex x, final Reindex y) =>
      all([x.family, x.kf, x.vf], [y.family, y.kf, y.vf]) &&
          switch ((x.witness, y.witness)) {
            (Residue(), Residue()) => true,
            (Catalog(law: final l), Catalog(law: final m)) => l == m,
            _ => false,
          },
    (Discard(), Discard()) && (final Discard x, final Discard y) => all(
      [x.family, x.sel],
      [y.family, y.sel],
    ),
    (Fold(), Fold()) && (final Fold x, final Fold y) =>
      all([x.family, x.op], [y.family, y.op]) &&
          switch ((x.identity, y.identity)) {
            (null, null) => true,
            (final Term i?, final Term j?) => sameTerm(i, j),
            _ => false,
          } &&
          x.depth == y.depth &&
          _sameEvidence(x.ev, y.ev),
    (Fix(), Fix()) && (final Fix x, final Fix y) =>
      all([x.init, x.step], [y.init, y.step]) &&
          x.self == y.self &&
          x.key == y.key &&
          switch ((x.kind, y.kind)) {
            (Lattice(join: final j), Lattice(join: final k)) => sameTerm(j, k),
            (Definedness(), Definedness()) => true,
            _ => false,
          } &&
          _sameEvidence(x.ev, y.ev),
    (Gen(), Gen()) && (final Gen x, final Gen y) =>
      all([x.init, x.step, x.guard], [y.init, y.step, y.guard]) && x.pos == y.pos,
    (Read(port: final p), Read(port: final q)) => p == q,
    (Push(port: final p, value: final s), Push(port: final q, value: final t)) =>
      p == q && sameTerm(s, t),
    _ => false,
  };
}
