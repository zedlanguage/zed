/// The reduced product (DESIGN.md sec:domains and sec:constraints; step L1.39).
///
/// A name in scope holds a [Product]: the cell of step L1.24, the name's type and its binding
/// time. A [Scope] holds one product per name, the linear relation among them (step L1.38) and
/// the written constraints, each a kernel term that holds in the scope. [Scope.reduce] passes
/// information between the domains until nothing changes:
///
/// - the interval and the congruence narrow each other, and a single value fixes both;
/// - the projection of the linear relation onto a name meets its interval;
/// - a finite set and the interval narrow each other;
/// - the type loses `int` when the interval or the congruence is empty, keeps only the literals
///   of a finite interval or a finite set, and gives its literals back to the finite set and
///   the interval;
/// - enumeration: a name of type within `int` whose finite set lists its integers keeps only
///   the members at which each written constraint on it holds, the constraint's other names
///   static and its form shown to end ([ends]); a constraint whose form does not show it ends
///   removes nothing. A range is left to the interval, congruence and relation reasoning
///   (docs/thresholds.md, replacement 8). In a scope under `@exact` ([Scope.exact]) the scope is
///   bottom exactly when no point of its bounded integer names' intervals and classes meets
///   their written constraints. The constraints are taken in groups that share names, each
///   group searched for one point ([witness]); the point is kept, and the group is searched
///   again only when a name's interval or class no longer holds it. Nothing lists the points,
///   so the scope stays the size of the source, and a question about the exact set is a test
///   assumed in the scope: whether `p == 4` can hold is whether the scope assuming it is bottom.
///
/// A product is empty when its type is, and a scope with an empty product is bottom: the arm it
/// describes is unreachable. [Scope.assume] narrows a scope by a test and its outcome: `!`, `&&`
/// and `||` (an `if` with a boolean arm) are taken apart, a false `&&` and a true `||` joining
/// the scopes of their cases, and each atom narrows by the preimage of its outcome, by its
/// linear relation, by the congruence `x mod c == r`, and by an equality with a literal, whose
/// negation excludes the literal by complement where the element is exact (types, intervals,
/// finite sets). [arms] walks a body and gives the scope of each `if` arm.
///
/// A binding time is [Time.build] for a value known when the program is built and [Time.run]
/// for one known only when it runs; a meet takes the earlier and a join the later.
///
/// A scope's fields are persistent maps and immutable values, so a copy of a scope takes
/// constant time and shares everything with the original. A product in a scope is never
/// changed in place: a change copies it, narrows the copy, and puts the copy back only when it
/// changed. So a scope's names are the same map exactly when no product changed, and a
/// product read from a scope may be shared and must be copied before it is changed.
library;

import 'dart:collection';

import '../../elab.dart' show free;
import '../../stage.dart' show ends;
import '../kernel/error.dart';
import '../kernel/eval.dart';
import '../kernel/pmap.dart';
import '../kernel/term.dart' hide Lattice;
import '../kernel/types.dart';
import '../kernel/value.dart' hide Atom;
import 'affine.dart' show Bounds;
import 'cell.dart';
import 'hull.dart';
import 'interval.dart';
import 'lattice.dart';
import 'preimage.dart';
import 'presburger.dart' hide Product;
import 'presburger.dart' as pb show Product;
import 'revision.dart' as revision show forward;
import 'revision.dart' show Op, reduceCongruence;

/// When a value is known.
enum Time with Lattice<Time> {
  /// No value: the bottom.
  never,

  /// When the program is built.
  build,

  /// When the program runs: the top.
  run;

  @override
  Time join(Time other) => index >= other.index ? this : other;

  @override
  Time meet(Time other) => index <= other.index ? this : other;

  @override
  Time widen(Time next, Landmarks marks) => join(next);

  @override
  Time narrow(Time next, Landmarks marks) => next;

  @override
  String toString() => name;
}

/// The base types whose part a widening of a type takes whole once it grows.
final _bases = [Type.boolean, Type.integer, Type.rational, Type.f64, Type.string];

/// The parts a widening takes whole and a narrowing leaves whole: each base type, and the rest
/// of each universe. They cover every value.
final _parts = [
  ..._bases,
  for (final u in Universe.values) Type.universe(u) - Type.unionAll(_bases),
];

/// A type as an element of the store's lattices.
final class TypeElement with Lattice<TypeElement> {
  final Type type;

  const TypeElement(this.type);

  @override
  TypeElement join(TypeElement other) => TypeElement(type | other.type);

  @override
  TypeElement meet(TypeElement other) => TypeElement(type & other.type);

  /// The join, and the whole of each base type, and of the rest of each universe, in which
  /// `next` has a value `this` has not. Each such part is taken at most once, so every chain of
  /// widenings is finite.
  @override
  TypeElement widen(TypeElement next, Landmarks marks) {
    var out = type | next.type;
    for (final p in _parts) {
      if (!(next.type & p).subtype(type)) out = out | p;
    }
    return TypeElement(out);
  }

  /// `next` in each part that `this` holds whole, and `this` in the others: each part leaves
  /// the whole at most once and is then fixed, so every chain of narrowings is finite.
  @override
  TypeElement narrow(TypeElement next, Landmarks marks) => TypeElement(
    Type.unionAll([for (final p in _parts) p.subtype(type) ? next.type & p : type & p]),
  );

  @override
  bool leq(TypeElement other) => type.subtype(other.type);

  @override
  bool operator ==(Object other) => other is TypeElement && other.type == type;

  @override
  int get hashCode => type.hashCode;

  @override
  String toString() => '$type';
}

/// The interval of the integers `vs`, one piece each.
IntervalSet _points(Iterable<int> vs) =>
    IntervalSet.fromPieces([for (final n in vs) (Fin(n), Fin(n))]);

/// The element of the reduced product for one name.
final class Product {
  /// The domains of step L1.24.
  final Cell cell;

  /// The type.
  final Entry<TypeElement> ty;

  /// The binding time.
  final Entry<Time> time;

  Product(this.cell, this.ty, this.time);

  /// No information: any value, known when the program runs.
  Product.top() : this(Cell.top(), Entry(TypeElement(Type.top)), Entry(Time.run));

  /// No value.
  factory Product.bottom() {
    final p = Product.top();
    p.cell.ints.element = Bounds.ints(const IntervalSet.empty());
    p.cell.congruence.element = Congruence.bottom;
    p.cell.finite.element = FiniteSet<Value>.bottom();
    p.ty.element = TypeElement(Type.empty);
    p.time.element = Time.never;
    return p;
  }

  /// Any value of `ty`, known when the program runs.
  factory Product.ofType(Type ty) {
    final p = Product.top()..ty.element = TypeElement(ty);
    p.reduceDomains();
    return p;
  }

  /// The value `v`, known when the program is built.
  Product.literal(Value v)
    : this(Cell.literal(v), Entry(TypeElement(Type.lit(v) ?? Type.top)), Entry(Time.build));

  /// A copy, whose entries change apart from this product's.
  Product copy() =>
      Product(cell.copy(), Entry(ty.element, ty.premises), Entry(time.element, time.premises));

  /// The type.
  Type get type => ty.element.type;

  /// Whether every domain of `this` is below the same domain of `other`: the order in which
  /// the reduction only descends.
  bool leq(Product other) {
    final (a, b) = (cell, other.cell);
    return a.ints.element.leq(b.ints.element) &&
        a.congruence.element.leq(b.congruence.element) &&
        a.finite.element.leq(b.finite.element) &&
        a.float.element.leq(b.float.element) &&
        a.length.element.leq(b.length.element) &&
        ty.element.leq(other.ty.element) &&
        time.element.leq(other.time.element);
  }

  /// Whether no value has this element.
  bool get isEmpty => type.isEmpty;

  /// The integers of the interval domain.
  IntervalSet get ints => cell.ints.element.concrete;

  /// The one value, when the finite set holds exactly one.
  Value? get value => switch (cell.finite.element.members) {
    final s? when s.length == 1 => s.first,
    _ => null,
  };

  /// Whether `v` is a value of this element: of its type, in its finite set, and an integer in
  /// its interval and its congruence.
  bool contains(Value v) {
    final inInts = switch (v) {
      Int(value: final n) => ints.contains(n) && cell.congruence.element.contains(n),
      _ => true,
    };
    final inFinite = cell.finite.element.members?.contains(v) ?? true;
    return inInts && inFinite && type.contains(v);
  }

  /// The premises of every entry.
  Premises get premises => cell.premises.union(ty.premises).union(time.premises);

  /// Joins `other` into `this`; whether an element changed.
  bool join(Product other) =>
      [cell.join(other.cell), ty.join(other.ty), time.join(other.time)].contains(true);

  /// Widens `this` by `other` at the component head `head`; whether an element changed.
  bool widen(Product other, FactAddress head, Landmarks marks) => [
    cell.widen(other.cell, head, marks),
    ty.widen(other.ty, head, marks),
    time.widen(other.time, head, marks),
  ].contains(true);

  /// Meets the interval domain with `x`; whether it changed.
  bool meetInts(IntervalSet x, Premises premises) => cell.ints.meet(Bounds.ints(x), premises);

  /// The reductions between this product's own domains, once each; whether any changed.
  bool reduceDomains() {
    final prem = premises;
    final int = Type.integer;
    var changed = false;
    final (x, c) = reduceCongruence(ints, cell.congruence.element);
    changed |= meetInts(x, prem);
    changed |= cell.congruence.meet(c, prem);
    // A finite set against the interval: an integer member outside it goes.
    if (cell.finite.element.members case final vs?) {
      final x = ints;
      final kept = [
        for (final v in vs)
          if (!(v is Int && !x.contains(v.value))) v,
      ];
      if (vs.every((v) => v is Int)) {
        changed |= meetInts(_points([for (final v in kept) (v as Int).value]), prem);
      }
      changed |= cell.finite.meet(FiniteSet.of(kept), prem);
    }
    // The type from the other domains.
    if (ints.isEmpty || cell.congruence.element.isBottom) {
      changed |= ty.meet(TypeElement(~int), prem);
    } else {
      // The type's integers narrowed to the interval, listed only when the list is no longer
      // than what is listed from: the type's own integer literals, or an interval with no
      // more members than its two endpoints a piece.
      final x = ints;
      final List<Value>? vs;
      if ((type & int).listed case final listed?) {
        vs = [
          for (final v in listed)
            if (!(v is Int && !x.contains(v.value))) v,
        ];
      } else {
        final most = BigInt.from(2 * x.pieces.length);
        BigInt? size = BigInt.zero;
        for (final p in x.pieces) {
          if (p case (Fin(v: final a), Fin(v: final b))) {
            size = size! + BigInt.from(b) - BigInt.from(a) + BigInt.one;
          } else {
            size = null;
            break;
          }
        }
        vs = size == null || size > most
            ? null
            : [
                for (final p in x.pieces)
                  for (var n = (p.$1 as Fin).v; n <= (p.$2 as Fin).v; n++) Int(n),
              ];
      }
      if (vs != null) {
        final lits = Type.unionAll([for (final v in vs) ?Type.lit(v)]);
        changed |= ty.meet(TypeElement(~int | lits), prem);
      }
    }
    if (cell.finite.element.members case final vs?) {
      final lits = [for (final v in vs) Type.lit(v)];
      if (!lits.contains(null)) {
        changed |= ty.meet(TypeElement(Type.unionAll([for (final t in lits) t!])), prem);
      }
    }
    // The other domains from the type.
    if (type.listed case final vs?) {
      changed |= cell.finite.meet(FiniteSet.of(vs), prem);
    }
    if ((type & int).listed case final vs? when vs.isNotEmpty && type.subtype(int)) {
      changed |= meetInts(_points([for (final v in vs) ?(v is Int ? v.value : null)]), prem);
    }
    return changed;
  }

  @override
  bool operator ==(Object other) =>
      other is Product && other.cell == cell && other.ty == ty && other.time == time;

  @override
  int get hashCode => Object.hash(cell, ty, time);

  /// The cell's lines, then the type and the binding time when they are not the top.
  @override
  String toString() {
    final out = StringBuffer('$cell');
    if (type != Type.top) out.writeln('type $type');
    if (time.element != Time.run) out.writeln('time ${time.element}');
    return out.toString();
  }
}

/// The integers of `p` when its finite set lists them: every member an integer. The finite set
/// holds the literals the source lists, and an interval's members only where they are no more
/// than its endpoints, so the list is no longer than what it is read from.
List<int>? _listed(Product p) {
  final vs = p.cell.finite.element.members;
  if (vs == null || !vs.every((v) => v is Int)) return null;
  return [for (final v in vs) (v as Int).value];
}

int _byString(String a, String b) => a.compareTo(b);

int _byInt(int a, int b) => a - b;

int _byCon(Con a, Con b) => a.compareTo(b);

/// The serials of the parts that mention each name.
typedef _Uses = PMap<String, PMap<int, bool>>;

_Uses _use(_Uses uses, Iterable<String> names, int serial, bool add) {
  for (final n in names) {
    final m = uses[n] ?? const PMap.empty(_byInt);
    final m2 = add ? m.put(serial, true) : m.remove(serial);
    uses = m2.isEmpty ? uses.remove(n) : uses.put(n, m2);
  }
  return uses;
}

/// The names `f` mentions, alone or in a product.
List<String> _symbols(Formula f) => {
  for (final a in f.atoms)
    ...switch (a) {
      Sym(:final name) => [name],
      pb.Product(:final a, :final b) => [a, b],
      _ => <String>[],
    },
}.toList();

/// A conjunction of linear formulas, kept in persistent maps by the order its conjuncts were
/// added: a conjunct is added, replaced or removed in O(log n), and two conjunctions made from
/// one by a few changes are compared in time near the number of changes ([PMap.diff]). Of two
/// constraints on one term only the tighter is kept, in the place of the first, as
/// [Formula.and] keeps them.
final class _Conjunction {
  static int _next = 0;

  /// The conjuncts other than constraints, each with the names it mentions.
  final PMap<int, (Formula, List<String>)> parts;

  /// The constraints.
  final PMap<int, Con> cons;

  /// The serial of each constraint by its term, the constant zero, and its comparison.
  final PMap<Con, int> byTerm;

  /// The serials of the parts, and of the constraints, that mention each name.
  final _Uses uses, consUses;

  /// Whether the conjunction is `false`; it then has no conjunct.
  final bool isBottom;

  _Conjunction(this.parts, this.cons, this.byTerm, this.uses, this.consUses, this.isBottom);

  static final top = _Conjunction(
    PMap.empty(_byInt),
    PMap.empty(_byInt),
    PMap.empty(_byCon),
    PMap.empty(_byString),
    PMap.empty(_byString),
    false,
  );

  static final bottom = _Conjunction(
    PMap.empty(_byInt),
    PMap.empty(_byInt),
    PMap.empty(_byCon),
    PMap.empty(_byString),
    PMap.empty(_byString),
    true,
  );

  bool get isTop => !isBottom && parts.isEmpty && cons.isEmpty;

  /// The conjunction of `f`'s top-level conjuncts.
  static _Conjunction of(Formula f) => top.add(f);

  /// The conjunction as a formula, its conjuncts in the order they were added.
  late final Formula formula = isBottom
      ? Formula.bottom
      : Formula.and([
          for (final (_, g) in _merge(parts.entries.map((e) => (e.$1, e.$2.$1)), cons.entries)) g,
        ]);

  /// The constraints together.
  late final Formula base = Formula.and([...cons.values]);

  _Conjunction _with({
    PMap<int, (Formula, List<String>)>? parts,
    PMap<int, Con>? cons,
    PMap<Con, int>? byTerm,
    _Uses? uses,
    _Uses? consUses,
  }) => _Conjunction(
    parts ?? this.parts,
    cons ?? this.cons,
    byTerm ?? this.byTerm,
    uses ?? this.uses,
    consUses ?? this.consUses,
    false,
  );

  /// This conjunction and `f`; `serial` places a conjunct other than a constraint.
  _Conjunction add(Formula f, [int? serial]) {
    if (isBottom) return this;
    switch (f) {
      case And(:final items):
        return items.fold(this, (c, g) => c.add(g));
      case Or(:final items) when items.isEmpty:
        return bottom;
      case Con(:final lin, :final rel):
        final key = Con(lin.minus(Lin.constant(lin.constant)), rel);
        if (byTerm[key] case final s?) {
          final old = cons[s]!;
          if (rel == Rel.ge && lin.constant < old.lin.constant) return _with(cons: cons.put(s, f));
          if (rel == Rel.eq && lin.constant != old.lin.constant) return bottom;
          return this;
        }
        final s = _next++;
        return _with(
          cons: cons.put(s, f),
          byTerm: byTerm.put(key, s),
          consUses: _use(consUses, _symbols(f), s, true),
        );
      default:
        final s = serial ?? _next++;
        final names = _symbols(f);
        return _with(parts: parts.put(s, (f, names)), uses: _use(uses, names, s, true));
    }
  }

  /// This conjunction without the part, or the constraint, `s`.
  _Conjunction _remove(int s) {
    if (parts[s] case (_, final names)) {
      return _with(parts: parts.remove(s), uses: _use(uses, names, s, false));
    }
    final c = cons[s]!;
    return _with(
      cons: cons.remove(s),
      byTerm: byTerm.remove(Con(c.lin.minus(Lin.constant(c.lin.constant)), c.rel)),
      consUses: _use(consUses, _symbols(c), s, false),
    );
  }

  /// [Formula.forget] of `sym`, applied to the conjuncts that mention it alone.
  _Conjunction forget(String sym) {
    var out = this;
    for (final s in [...?consUses[sym]?.keys]) {
      out = out._remove(s);
    }
    for (final s in [...?uses[sym]?.keys]) {
      final g = parts[s]!.$1;
      out = out._remove(s).add(g.forget(sym), s);
    }
    return out;
  }

  /// [Formula.either] of the two, each constraint of the rest of each side replaced by `rest` of
  /// it: the conjuncts both hold, and the disjunction of the rest of each. The conjuncts at one
  /// serial in both are found by [PMap.diff], so a join of two scopes narrowed apart from one
  /// costs near the number of conjuncts each added.
  static _Conjunction either(_Conjunction a, _Conjunction b, Formula Function(Con) rest) {
    if (a.isBottom || b.isBottom) return a.isBottom ? b : a;
    List<(int, Formula)> only(_Conjunction x, List<int> ps, List<int> cs) => _merge(
      [
        for (final s in ps)
          if (x.parts[s] case (final g, _)) (s, g),
      ],
      [
        for (final s in cs)
          if (x.cons[s] case final c?) (s, c),
      ],
    );
    final (dp, dc) = (a.parts.diff(b.parts), a.cons.diff(b.cons));
    final onlyA = only(a, dp, dc), onlyB = only(b, dp, dc);
    final inB = {for (final (_, g) in onlyB) g};
    final inA = {for (final (_, g) in onlyA) g};
    var out = a;
    final restA = <Formula>[];
    for (final (s, g) in onlyA) {
      if (!inB.contains(g)) {
        restA.add(g.mapCons(rest));
        out = out._remove(s);
      }
    }
    final restB = [
      for (final (_, g) in onlyB)
        if (!inA.contains(g)) g.mapCons(rest),
    ];
    final left = Formula.or([Formula.and(restA), Formula.and(restB)]);
    return left == Formula.top ? out : out.add(left);
  }
}

/// Two runs of serials and conjuncts, each in serial order, merged.
List<(int, Formula)> _merge(Iterable<(int, Formula)> a, Iterable<(int, Formula)> b) {
  final out = [...a, ...b];
  out.sort((x, y) => x.$1 - y.$1);
  return out;
}

/// The intervals and classes of a part's names when it was last projected.
typedef _Projected = List<(String, IntervalSet, Congruence)>;

/// Whether `a` is the record `b`.
bool _sameAt(_Projected? a, _Projected b) {
  if (a == null || a.length != b.length) return false;
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

/// The names a formula mentions.
List<String> _syms(Formula f) => [
  for (final a in f.atoms)
    if (a case Sym(:final name)) name,
];

/// Each of `conjuncts` that is not a constraint, with the constraints, and the constraints alone
/// when there are any; each part with the conjunct it is projected for, or the constraints for
/// theirs.
List<(Formula, Formula)> _split(Iterable<Formula> conjuncts) {
  final cons = <Formula>[], others = <Formula>[];
  for (final g in conjuncts) {
    (g is Con ? cons : others).add(g);
  }
  final base = Formula.and(cons);
  return [
    for (final g in others) (g, Formula.and([g, base])),
    if (base != Formula.top) (base, base),
  ];
}

/// Top-level conjuncts of a relation projected together.
final class _Block {
  /// What is projected: each conjunct that is not a constraint, with the constraints, and the
  /// constraints alone, each with the conjunct it is projected for ([_split]). A new conjunct
  /// then costs its own part, not the block's.
  final List<(Formula, Formula)> parts;

  /// The conjuncts, by their places.
  final List<int> conjuncts;

  /// The names they mention.
  final List<String> names;

  /// The tree of blocks it lies in.
  final int tree;

  _Block(this.parts, this.conjuncts, this.names, this.tree);
}

/// The blocks of `conjuncts`, each tree's in preorder from a root. Conjuncts that share an atom
/// other than a name are first put together; the blocks are then the biconnected components of
/// the graph whose vertices are these groups and the names, with an edge from a group to each
/// name it mentions, where components that share a group are one block (Tarjan's algorithm,
/// with a stack in place of recursion). In linear time but for the sorting of atoms.
List<_Block> _blocks(List<Formula> conjuncts) {
  final n = conjuncts.length;
  final up = List.generate(n, (i) => i);
  int find(int i) {
    while (up[i] != i) {
      up[i] = up[up[i]];
      i = up[i];
    }
    return i;
  }

  final nameOf = <String>[];
  final index = <String, int>{};
  // Each conjunct's names, numbered, and the first conjunct of each other atom.
  final mentions = List.generate(n, (_) => <int>[]);
  final other = <Atom, int>{};
  for (var i = 0; i < n; i++) {
    for (final a in conjuncts[i].atoms) {
      if (a case Sym(:final name)) {
        mentions[i].add(index.putIfAbsent(name, () => (nameOf..add(name)).length - 1));
      } else if (other[a] case final k?) {
        up[find(i)] = find(k);
      } else {
        other[a] = i;
      }
    }
  }
  // A group's vertex is its root conjunct's, with the edges of all of its conjuncts; name `j`
  // is vertex `n + j`.
  var adj = List.generate(n + nameOf.length, (_) => <int>[]);
  for (var i = 0; i < n; i++) {
    final r = find(i);
    for (final j in mentions[i]) {
      adj[r].add(n + j);
      adj[n + j].add(r);
    }
  }
  adj = [for (final es in adj) es.toSet().toList()..sort()];
  final disc = List.filled(adj.length, -1), low = List.filled(adj.length, 0);
  var time = 0;
  final edges = <(int, int)>[];
  for (var s = 0; s < n; s++) {
    if (disc[s] != -1 || find(s) != s) continue;
    disc[s] = low[s] = time++;
    // The path from `s`: each vertex, its parent and the place of its next edge.
    final vs = [s], parents = [-1], next = [0];
    while (vs.isNotEmpty) {
      final top = vs.length - 1, v = vs[top];
      if (next[top] < adj[v].length) {
        final w = adj[v][next[top]++];
        if (disc[w] == -1) {
          edges.add((v, w));
          disc[w] = low[w] = time++;
          vs.add(w);
          parents.add(v);
          next.add(0);
        } else if (w != parents[top] && disc[w] < disc[v]) {
          edges.add((v, w));
          if (disc[w] < low[v]) low[v] = disc[w];
        }
        continue;
      }
      vs.removeLast();
      parents.removeLast();
      next.removeLast();
      if (vs.isEmpty) continue;
      final u = vs.last;
      if (low[v] < low[u]) low[u] = low[v];
      if (low[v] >= disc[u]) {
        // A component: its groups are one block.
        int? first;
        while (edges.isNotEmpty) {
          final (a, b) = edges.removeLast();
          for (final x in [a, b]) {
            if (x >= n) continue;
            if (first == null) {
              first = find(x);
            } else {
              up[find(x)] = first;
            }
          }
          if (a == u && b == v) break;
        }
      }
    }
  }
  // The blocks, and the blocks that mention each name.
  final place = <int, int>{};
  final members = <List<int>>[];
  for (var i = 0; i < n; i++) {
    members[place.putIfAbsent(find(i), () => (members..add([])).length - 1)].add(i);
  }
  final names = <List<int>>[];
  final at = List.generate(nameOf.length, (_) => <int>[]);
  for (var b = 0; b < members.length; b++) {
    final js = {for (final i in members[b]) ...mentions[i]}.toList()..sort();
    for (final j in js) {
      at[j].add(b);
    }
    names.add(js);
  }
  // Each tree in preorder.
  final out = <_Block>[];
  final seen = List.filled(members.length, false), crossed = List.filled(nameOf.length, false);
  for (var root = 0; root < members.length; root++) {
    if (seen[root]) continue;
    seen[root] = true;
    final work = [root];
    while (work.isNotEmpty) {
      final b = work.removeLast();
      for (final j in names[b]) {
        if (crossed[j]) continue;
        crossed[j] = true;
        for (final c in at[j]) {
          if (!seen[c]) {
            seen[c] = true;
            work.add(c);
          }
        }
      }
      out.add(
        _Block(_split([for (final i in members[b]) conjuncts[i]]), members[b], [
          for (final j in names[b]) nameOf[j],
        ], root),
      );
    }
  }
  return out;
}

/// The names in scope with their products, the linear relation among them, and the written
/// constraints that hold.
final class Scope {
  /// One product per name.
  PMap<String, Product> names;

  /// The relation the integer names meet, with no auxiliary variable.
  _Conjunction _relation;

  Formula get relation => _relation.formula;

  set relation(Formula f) => _relation = _Conjunction.of(f);

  /// The written constraints that hold, a test and its negations by printed text, each with its
  /// free names.
  PMap<String, (Term, List<String>)> written;

  /// The texts of the written constraints that mention each name.
  PMap<String, PMap<String, bool>> _mentions;

  /// The products and written constraints at the start of the last enumeration; an
  /// enumeration reads a constraint again only when it is new or a name it mentions has
  /// changed since.
  (PMap<String, Product>, PMap<String, (Term, List<String>)>)? _enumeratedAt;

  /// Whether no state reaches this scope.
  bool bottom;

  /// The written constraints already enumerated, each as its text with the values of its static
  /// names. A second enumeration removes nothing more: the members a constraint holds at do not
  /// depend on the interval, which already lies within them.
  PMap<String, bool> enumerated;

  /// The top-level parts of the relation already projected: its constraints together, and each
  /// other conjunct with them, each with the intervals and classes of the names it mentions at
  /// that projection, which are all a projection reads of them. A part is projected again only
  /// when one of these has changed since (docs/thresholds.md, replacement 4). The map is
  /// replaced, never changed, while a copy of the scope may share it.
  Map<Formula, _Projected> _projected;

  /// Whether the scope is under `@exact`.
  bool exact;

  /// Under `@exact`, each group of written constraints that share names, by their texts with
  /// the static values substituted, sorted and joined, with a point that meets them all.
  PMap<String, Point> exactly;

  Scope._(
    this.names,
    this._relation,
    this.written,
    this._mentions,
    this._enumeratedAt,
    this.bottom,
    this.enumerated,
    this._projected,
    this.exact,
    this.exactly,
  );

  /// The scope of `names`, reduced.
  factory Scope(Iterable<(String, Product)> names) => Scope._of(names, false);

  /// The scope of `names` in a declaration annotated `@exact`, reduced: its written
  /// constraints narrow their names exactly (DESIGN.md sec:constraints).
  factory Scope.exact(Iterable<(String, Product)> names) => Scope._of(names, true);

  factory Scope._of(Iterable<(String, Product)> names, bool exact) => Scope._(
    names.fold(const PMap.empty(_byString), (m, e) => m.put(e.$1, e.$2)),
    _Conjunction.top,
    const PMap.empty(_byString),
    const PMap.empty(_byString),
    null,
    false,
    const PMap.empty(_byString),
    const {},
    exact,
    const PMap.empty(_byString),
  )..reduce();

  /// A copy, in constant time: the two share every field until one is replaced.
  Scope copy() => Scope._(
    names,
    _relation,
    written,
    _mentions,
    _enumeratedAt,
    bottom,
    enumerated,
    _projected,
    exact,
    exactly,
  );

  void _become(Scope s) {
    names = s.names;
    _relation = s._relation;
    written = s.written;
    _mentions = s._mentions;
    _enumeratedAt = s._enumeratedAt;
    bottom = s.bottom;
    enumerated = s.enumerated;
    _projected = s._projected;
    exact = s.exact;
    exactly = s.exactly;
  }

  /// Changes the product of `x`, if in scope, by `change` on a copy, kept only when `change`
  /// reports a change.
  void _update(String x, bool Function(Product) change) {
    final p = names[x]?.copy();
    if (p != null && change(p)) names = names.put(x, p);
  }

  /// The scope of a `let` body that binds `x` to `p`. A name already in scope is forgotten
  /// first: the relation is weakened to say nothing of it and the written constraints on it go,
  /// since they hold of the value it shadows. Nothing else in the scope then mentions `x`, so
  /// `p`'s own reductions are the whole reduction. This scope is left as it was.
  Scope bind(String x, Product p) {
    final q = p.copy();
    while (true) {
      final before = q.copy();
      if (!q.reduceDomains()) break;
      assert(q.leq(before), 'a reduction rose: $before to $q');
    }
    final s = copy();
    if (bottom) return s;
    if (names.containsKey(x)) {
      s._relation = _relation.forget(x);
      for (final k in [...?_mentions[x]?.keys]) {
        s._unwrite(k);
      }
    }
    s.names = names.put(x, q);
    if (q.isEmpty) s._toBottom();
    return s;
  }

  void _toBottom() {
    bottom = true;
    final b = Product.bottom();
    names = PMap.sorted([for (final n in names.keys) (n, b)], _byString);
  }

  /// Records `t` as a written constraint that holds.
  void write(Term t) {
    final k = '$t';
    if (written.containsKey(k)) return;
    final fr = free(t).toList();
    written = written.put(k, (t, fr));
    for (final n in fr) {
      _mentions = _mentions.put(n, (_mentions[n] ?? const PMap.empty(_byString)).put(k, true));
    }
  }

  void _unwrite(String k) {
    final (_, fr) = written[k]!;
    written = written.remove(k);
    for (final n in fr) {
      final m = _mentions[n]!.remove(k);
      _mentions = m.isEmpty ? _mentions.remove(n) : _mentions.put(n, m);
    }
  }

  /// The static names among `names`, and their values.
  SplayTreeMap<String, Value> staticsOf(Iterable<String> names) =>
      SplayTreeMap.of({for (final n in names) n: ?this.names[n]?.value});

  /// The product of `name`, shared with this scope; the top for a name not in scope.
  Product get(String name) => names[name] ?? Product.top();

  /// The names with one value each, and their values.
  SplayTreeMap<String, Value> get statics =>
      SplayTreeMap.of({for (final (n, p) in names.entries) n: ?p.value});

  /// Whether the state `env`, a value for each of some names, is in this scope: each value in
  /// its name's product and the integers meeting the relation. A name `env` does not give is
  /// not checked; the relation is checked only when `env` gives each of its names.
  bool contains(Map<String, Value> env) {
    if (bottom) return false;
    if (!env.entries.every((e) => get(e.key).contains(e.value))) return false;
    final point = <Atom, BigInt>{};
    for (final a in relation.atoms) {
      if (a case Sym(:final name)) {
        if (env[name] case Int(value: final v)) {
          point[a] = BigInt.from(v);
          continue;
        }
      }
      return true;
    }
    return relation.holds(point);
  }

  /// A scope above both: each name's product is the join of its two products, and the relation
  /// is the disjunction of the two. It is not always the least, since the products are joined
  /// one name at a time, and a relation the sides hold only through single values of their
  /// names is lost.
  Scope join(Scope other) {
    if (bottom) return other.copy();
    if (other.bottom) return copy();
    final joined = <(String, Product)>[
      for (final (n, p) in names.entries)
        if (p.copy() case final q) (n, q.join(other.get(n)) ? q : p),
      for (final n in other.names.keys)
        if (!names.containsKey(n)) (n, Product.top()),
    ]..sort((a, b) => a.$1.compareTo(b.$1));
    final ns = PMap.sorted(joined, _byString);
    var exactly = this.exactly;
    for (final (k, v) in other.exactly.entries) {
      if (!exactly.containsKey(k)) exactly = exactly.put(k, v);
    }
    // The equalities of two or more atoms that hold on both sides (Karr's join), which the
    // disjunction of the relations holds but no projection of one of its parts finds. Each side
    // implies them, so each side's rest holds where they do as it holds with their pivots
    // replaced; the disjunction then mentions no pivot, and a join of sides that fix `k` names
    // leaves a disjunction of one name and `k - 1` equalities of two.
    final hull = _hull().join(other._hull());
    final relation = _Conjunction.either(_relation, other._relation, hull.reduce).add(
      Formula.and([
        for (final t in hull.rows)
          if (t.terms.length > 1) Con(t, Rel.eq),
      ]),
    );
    // The constraints written on both sides, and enumerated on both, found among the entries
    // that differ.
    final w = copy();
    for (final k in written.diff(other.written)) {
      if (written.containsKey(k) && !other.written.containsKey(k)) w._unwrite(k);
    }
    var enumerated = this.enumerated;
    for (final k in this.enumerated.diff(other.enumerated)) {
      if (!other.enumerated.containsKey(k)) enumerated = enumerated.remove(k);
    }
    return Scope._(
      ns,
      relation,
      w.written,
      w._mentions,
      // The join's constraints are this scope's, so they are enumerated again only when one is
      // new or a name it mentions has changed since this scope's last enumeration.
      _enumeratedAt,
      false,
      enumerated,
      // A part projected on both sides is projected within the join: each side's intervals lie
      // within its projection, and the join's within their union.
      {
        for (final MapEntry(:key, :value) in _projected.entries)
          if (other._projected.containsKey(key))
            key: [
              for (final (n, _, _) in value)
                if (ns[n] ?? Product.top() case final p) (n, p.ints, p.cell.congruence.element),
            ],
      },
      exact,
      // A point of either side is a point of the join; it is checked again when read.
      exactly,
    );
  }

  /// The affine hull of the scope's points: the equalities among the relation's top-level
  /// conjuncts, and each name of one integer value.
  Hull _hull() => bottom
      ? Hull.empty
      : Hull.of([
          for (final c in _relation.cons.values)
            if (c.rel == Rel.eq) c.lin,
          for (final (n, p) in names.entries)
            if (p.value case Int(value: final v))
              Lin.atom(Sym(n)).minus(Lin.constant(BigInt.from(v))),
        ]);

  /// This scope where `test` gave `outcome`, reduced.
  Scope assume(Term test, bool outcome, Premises premises) {
    final s = copy();
    s._narrow(test, outcome, premises);
    s.reduce();
    return s;
  }

  void _narrow(Term test, bool outcome, Premises prem) {
    if (bottom) return;
    switch (test) {
      case Lit(value: Bool(value: final b)):
        if (b != outcome) bottom = true;
      case PrimApp(prim: Prim.not, args: [final a]):
        _narrow(a, !outcome, prem);
      case PrimApp(prim: final p && (Prim.and || Prim.or), args: [final a, final b]):
        // Both sides hold when the connective's outcome forces them; otherwise the cases join.
        if ((p == Prim.and) == outcome) {
          _narrow(a, outcome, prem);
          _narrow(b, outcome, prem);
        } else {
          final l = copy()
            .._narrow(a, outcome, prem)
            ..reduce();
          final r = copy()
            .._narrow(a, !outcome, prem)
            .._narrow(b, outcome, prem)
            ..reduce();
          _become(l.join(r));
        }
      case If(cond: final c, then: final a, orElse: final b)
          when _isBoolLit(a) || _isBoolLit(b) || (_isTest(a) && _isTest(b)):
        final t = copy()
          .._narrow(c, true, prem)
          ..reduce()
          .._narrow(a, outcome, prem)
          ..reduce();
        final f = copy()
          .._narrow(c, false, prem)
          ..reduce()
          .._narrow(b, outcome, prem)
          ..reduce();
        _become(t.join(f));
      default:
        _atom(test, outcome, prem);
    }
  }

  /// Narrows by one atomic test.
  void _atom(Term test, bool outcome, Premises prem) {
    final t = _substitute(test, staticsOf(free(test)));
    // A bare name of bool type.
    if (t case Var(:final name)) {
      final v = Bool(outcome);
      _update(
        name,
        (p) => [
          p.ty.meet(TypeElement(Type.lit(v)!), prem),
          p.cell.finite.meet(FiniteSet.of([v]), prem),
        ].contains(true),
      );
    }
    // An equality with a literal, and the congruence of `x mod c == r`.
    if (t case PrimApp(prim: final op && (Prim.eq || Prim.ne), args: [final a0, final a1])) {
      final equal = (op == Prim.eq) == outcome;
      for (final (l, r) in [(a0, a1), (a1, a0)]) {
        switch ((l, r)) {
          case (Var(:final name), Lit(:final value)):
            _update(name, (p) => _equality(p, value, equal, prem));
          case (
                PrimApp(prim: Prim.mod, args: [Var(:final name), Lit(value: Int(value: final c))]),
                Lit(value: Int(value: final r)),
              )
              when equal && c != 0:
            final k = c.abs();
            _update(
              name,
              (p) => r < 0 || r >= k
                  ? p.ty.meet(TypeElement(~Type.integer), prem)
                  : p.cell.congruence.meet(Congruence(k, r), prem),
            );
          default:
        }
      }
    }
    final int = Type.integer;
    final fr = free(t);
    final inputs = [
      for (final n in fr)
        if (names[n]?.type.subtype(int) ?? false) n,
    ];
    // The preimage of the outcome.
    var exact = false;
    if (inputs.isNotEmpty) {
      final pre = preimage(t, {for (final n in inputs) n: get(n).ints}, BoolDemand(outcome));
      exact = pre.exact;
      for (final MapEntry(key: n, value: d) in pre.domains.entries) {
        _update(n, (p) => p.meetInts(d, prem));
      }
    }
    // The linear relation, when the test needs no auxiliary variable and says more than the
    // intervals: a test of one name whose preimage is exact is the interval itself.
    if (inputs.isNotEmpty && inputs.length == fr.length && (inputs.length > 1 || !exact)) {
      if (relations([t], inputs, false)?.firstOrNull case final r? when r.defs.isEmpty) {
        _relation = _relation.add(outcome ? r.body : Formula.negate(r.body));
      }
    }
    // The written constraint, unless it is a test of one integer name whose preimage is exact:
    // the name's interval then holds exactly the values that meet it, and enumeration would
    // remove none of them.
    if (!(exact && inputs.length == 1 && fr.length == 1)) {
      write(outcome ? test : PrimApp(Prim.not, [test]));
    }
  }

  /// Passes information between the domains of every product, the relation and the written
  /// constraints until nothing changes. This ends with no bound on the rounds
  /// (docs/thresholds.md, replacement 3). Every pass only narrows. The relation is projected
  /// again only when another reduction has changed a product since its last projection, and
  /// the others change only finitely often: a class narrows only to one value or none, a finite
  /// set or a type's literals only lose members, enumeration runs once per constraint, and an
  /// interval is narrowed only by these and by the class, whose rounding moves no endpoint the
  /// projection gave, since the projection reads every congruence and so its hulls end at
  /// members of each class.
  void reduce() => _reduce(false);

  /// [reduce] with every tree of blocks projected as a whole, for the control of the test that
  /// the blocks scale.
  void reduceWhole() => _reduce(true);

  void _reduce(bool whole) {
    PMap<String, Product>? projectedAt;
    bool empty() => bottom || names.values.any((p) => p.isEmpty);
    while (!empty()) {
      final before = names;
      if (projectedAt == null || !projectedAt.sameAs(names)) {
        _project(whole);
        projectedAt = names;
      }
      for (final (n, p) in names.entries) {
        final q = p.copy();
        if (q.reduceDomains()) names = names.put(n, q);
      }
      _enumerate();
      assert(names.entries.every((e) => e.$2.leq(before[e.$1]!)), 'a reduction rose');
      if (names.sameAs(before)) break;
    }
    if (empty()) _toBottom();
  }

  /// The projection of the relation, within every interval, onto each name it mentions, by
  /// blocks. The top-level conjuncts that share an atom other than a name, or a cycle through
  /// names, form one block, so two blocks share at most one name and the blocks and the names
  /// they share form a forest (docs/thresholds.md, replacement 4). Each block is projected from
  /// the leaves of its tree to the root and back, which carries every bound across the tree, and
  /// each only when one of its parts is new or an interval or class of a name it mentions has
  /// changed since its last projection: a test that narrows nothing costs its own blocks alone.
  /// A tree some block of which is due after the two passes has a block whose projection lost
  /// points the interval holds, and its conjuncts are then projected as a whole: its constraints
  /// together, and each other conjunct with them; with `whole`, every tree is.
  void _project(bool whole) {
    final c = _relation;
    if (c.isTop || c.isBottom) {
      _projected = const {};
      return;
    }
    final conjuncts = c.formula.conjuncts;
    final blocks = _blocks(conjuncts);
    _projected = Map.of(_projected);
    if (!whole) {
      for (final b in [...blocks.reversed, ...blocks]) {
        _projectBlock(b);
      }
    }
    final used = <Formula>{};
    // A tree's blocks are together, and no two trees share a name, so projecting one tree
    // leaves the others as they were.
    for (var i = 0; i < blocks.length;) {
      var j = i + 1;
      while (j < blocks.length && blocks[j].tree == blocks[i].tree) {
        j++;
      }
      final tree = blocks.sublist(i, j);
      i = j;
      final due =
          whole ||
          tree.any((b) {
            final at = _snapshot(b.names);
            return b.parts.any((p) => !_sameAt(_projected[p.$1], at));
          });
      if (!due) continue;
      // Keyed by the whole part, apart from the blocks' parts; with `whole`, which projects no
      // block, by its conjunct as a block's part is.
      for (final (key, g) in _split([
        for (final b in tree)
          for (final k in b.conjuncts) conjuncts[k],
      ])) {
        final k = whole ? key : g;
        _projectDue(k, g, _syms(g));
        used.add(k);
      }
    }
    for (final b in blocks) {
      for (final (key, _) in b.parts) {
        used.add(key);
      }
    }
    _projected.removeWhere((g, _) => !used.contains(g));
  }

  /// Projects the parts of `b` that are due, then marks every part of `b` projected: a bound one
  /// part gives another in the block waits for the next narrowing, so that a narrowing costs the
  /// block's due parts and not every part again.
  void _projectBlock(_Block b) {
    final at = _snapshot(b.names);
    final due = [
      for (final (key, g) in b.parts)
        if (!_sameAt(_projected[key], at)) g,
    ];
    if (due.isEmpty) return;
    due.forEach(_projectPart);
    final now = _snapshot(b.names);
    for (final (key, _) in b.parts) {
      _projected[key] = now;
    }
  }

  /// Projects `part`, which mentions `names`, when `key` is new or one of their intervals or
  /// classes has changed since its last projection. A part keyed by its conjunct alone is not
  /// projected again when only the constraints it is projected with have grown.
  void _projectDue(Formula key, Formula part, List<String> names) {
    if (_sameAt(_projected[key], _snapshot(names))) return;
    _projectPart(part);
    _projected[key] = _snapshot(names);
  }

  /// The interval and class of each of `names`.
  _Projected _snapshot(List<String> names) => [
    for (final n in names)
      if (get(n) case final p) (n, p.ints, p.cell.congruence.element),
  ];

  /// Meets each name `part` mentions with its projection, within every interval.
  void _projectPart(Formula part) {
    final syms = part.atoms.whereType<Sym>().toList();
    final parts = <Formula>[for (final a in syms) member(a, get(a.name).ints)];
    // Each name's congruence, `x == m * k + r` with `k` free, so that the projection already
    // lies in the class: otherwise the class moves an endpoint, the relation moves another
    // name's to match, and the two pass a bound back and forth without end.
    for (final a in syms) {
      final c = get(a.name).cell.congruence.element;
      if (c.modulus case final m? when m > 1) {
        final k = Lin.atom(Sym('${a.name} mod'));
        final rhs = k.times(BigInt.from(m)).plus(Lin.constant(BigInt.from(c.residue)));
        parts.add(Con.eq(Lin.atom(a), rhs));
      }
    }
    parts.add(part);
    final List<IntervalSet?> each;
    try {
      each = projectEach(Formula.and(parts), syms);
    } on Over {
      return;
    }
    for (var i = 0; i < syms.length; i++) {
      if (each[i] case final x?) _update(syms[i].name, (p) => p.meetInts(x, p.premises));
    }
  }

  /// Enumeration: the written constraints on each small integer name, and those on static
  /// names only. Each constraint is enumerated once for its static names.
  void _enumerate() {
    if (exact) _enumerateExactly();
    final pending = <(Term, List<String>, String)>[];
    final Iterable<String> due;
    if (_enumeratedAt case (final ns, final ws)) {
      due = SplayTreeSet.of([
        for (final k in written.diff(ws))
          if (written.containsKey(k)) k,
        for (final n in names.diff(ns)) ...?_mentions[n]?.keys,
      ]);
    } else {
      due = written.keys;
    }
    _enumeratedAt = (names, written);
    for (final text in due) {
      final (c, fr) = written[text]!;
      if (!fr.every(names.containsKey)) continue;
      final statics = staticsOf(fr);
      final open = [
        for (final n in fr)
          if (!statics.containsKey(n)) n,
      ];
      final key = [
        text,
        for (final MapEntry(:key, :value) in statics.entries) '$key=$value',
      ].join('\u0000');
      if (open.length > 1 || enumerated.containsKey(key)) continue;
      final cs = _substitute(c, statics);
      if (ends(cs)) pending.add((cs, open, key));
    }
    final int = Type.integer;
    for (final (c, open, key) in pending) {
      switch (open) {
        case []:
          if (_run(c) case final v? when v != const Bool(true)) {
            bottom = true;
            return;
          }
        case [final n]:
          final p = names[n];
          if (p == null || !p.type.subtype(int)) continue;
          final vs = _listed(p);
          if (vs == null) continue;
          final kept = [
            for (final v in vs)
              if (_run(Let(n, Lit(Int(v)), c)) == const Bool(true)) v,
          ];
          if (kept.length < vs.length) {
            _update(n, (p) => p.meetInts(_points(kept), p.premises));
          }
        default:
          continue;
      }
      enumerated = enumerated.put(key, true);
    }
  }

  /// Under `@exact`: each group of written constraints that share names, their static names
  /// substituted and their other names all bounded integers, searched for a point at which they
  /// all hold. The groups are the classes of a union of the names each constraint mentions. A
  /// group is searched again only when an interval or class of its names no longer holds its
  /// point; with no point, the scope is bottom.
  void _enumerateExactly() {
    final int = Type.integer;
    bool bounded(Product p) => p.ints.bounds is (Fin, Fin);
    // Each written constraint over open integer names, all bounded, with its statics
    // substituted.
    final eligible = <(Term, List<String>)>[];
    for (final (c, fr) in written.values) {
      if (!fr.every(names.containsKey)) continue;
      final statics = staticsOf(fr);
      final open = [
        for (final n in fr)
          if (!statics.containsKey(n)) n,
      ];
      if (open.isEmpty || !open.every((n) => get(n).type.subtype(int) && bounded(get(n)))) {
        continue;
      }
      eligible.add((_substitute(c, statics), open));
    }
    // The groups: the names joined by a union-find, each constraint in its first name's class.
    final parent = <String, String>{};
    String root(String n) {
      var r = n;
      while (parent[r] != r) {
        r = parent[r]!;
      }
      // Path compression.
      while (parent[n] != r) {
        final up = parent[n]!;
        parent[n] = r;
        n = up;
      }
      return r;
    }

    for (final (_, open) in eligible) {
      for (final n in open) {
        parent.putIfAbsent(n, () => n);
      }
      for (final n in open.skip(1)) {
        final (a, b) = (root(open.first), root(n));
        if (a != b) parent[b] = a;
      }
    }
    final groups = <String, (List<Term>, SplayTreeSet<String>)>{};
    for (final (c, open) in eligible) {
      final g = groups.putIfAbsent(root(open.first), () => ([], SplayTreeSet()));
      g.$1.add(c);
      g.$2.addAll(open);
    }
    for (final (cs, open) in groups.values) {
      final key = ([for (final c in cs) '$c']..sort()).join('\u0000');
      bool holds(Point w) => open.every((n) => w[n] != null && get(n).contains(Int(w[n]!)));
      if (exactly[key] case final w? when holds(w)) continue;
      final all = cs.reduce((a, b) => PrimApp(Prim.and, [a, b]));
      final dom = {for (final n in open) n: get(n).ints};
      final classes = {for (final n in open) n: get(n).cell.congruence.element};
      switch (witness(all, dom, classes, const BoolDemand(true))) {
        case (point: final w?):
          exactly = exactly.put(key, w);
        case (point: null):
          bottom = true;
          return;
        case null:
      }
    }
  }

  /// The element of `e`'s value in this scope: a literal, a value computed from static names,
  /// the revision table's forward transfer over integers, or the join of an `if`'s reachable
  /// arms. The product may be shared with the scope.
  Product forward(Term e) {
    if (bottom) return Product.bottom();
    switch (e) {
      case Lit(:final value):
        return Product.literal(value);
      case Var(:final name):
        return get(name);
      case Let(:final name, :final value, :final body):
        return bind(name, forward(value)).forward(body);
      case If(cond: final c, then: final a, orElse: final b):
        return assume(c, true, Premises.empty).forward(a).copy()
          ..join(assume(c, false, Premises.empty).forward(b));
      case PrimApp(:final prim, :final args):
        return _forwardPrim(prim, args);
      default:
    }
    // `forward` does not recurse below this node, so its free names are found once.
    final fr = free(e);
    final time = fr.map((n) => get(n).time.element).fold(Time.build, (a, b) => a.join(b));
    final statics = staticsOf(fr);
    if (e is! Lam && fr.every(statics.containsKey)) {
      if (_runStatic(_substitute(e, statics)) case final p?) return p;
    }
    return Product.top()..time.element = time;
  }

  /// [forward] of a primitive: its value when every argument has one, else the revision table's
  /// transfer over integers. Each argument is visited once.
  Product _forwardPrim(Prim op, List<Term> args) {
    final xs = [for (final a in args) forward(a)];
    final vs = [for (final x in xs) x.value];
    if (!vs.contains(null)) {
      if (_runStatic(PrimApp(op, [for (final v in vs) Lit(v!)])) case final p?) return p;
    }
    final p = Product.top()
      ..time.element = xs.map((x) => x.time.element).fold(Time.build, (a, b) => a.join(b));
    if (_intOp(op) case final o?
        when xs.isNotEmpty && xs.length <= 2 && xs.every((x) => x.type.subtype(Type.integer))) {
      final y = xs.length > 1 ? xs[1].ints : IntervalSet.top();
      p.ty.element = TypeElement(Type.integer);
      p.cell.ints.element = Bounds.ints(revision.forward(o, xs[0].ints, y));
      p.reduceDomains();
    }
    return p;
  }

  /// `unreachable`, or each name not at the top with its product's lines indented, then the
  /// relation when there is one.
  @override
  String toString() {
    if (bottom) return 'unreachable\n';
    final out = StringBuffer();
    for (final (n, p) in names.entries) {
      final s = '$p';
      if (s.isEmpty) continue;
      out.writeln('$n:');
      for (final l in s.split('\n')) {
        if (l.isNotEmpty) out.writeln('  $l');
      }
    }
    if (relation != Formula.top) out.writeln('relation $relation');
    return out.toString();
  }
}

/// Whether `t` is a boolean literal.
bool _isBoolLit(Term t) => t is Lit && t.value is Bool;

/// Whether `t` is a comparison, a connective or a boolean literal.
bool _isTest(Term t) =>
    _isBoolLit(t) ||
    t is PrimApp &&
        const {
          Prim.eq,
          Prim.ne,
          Prim.lt,
          Prim.le,
          Prim.gt,
          Prim.ge,
          Prim.and,
          Prim.or,
          Prim.not,
        }.contains(t.prim);

/// Narrows `p` by the outcome of a literal equality: the literal itself, or every value but it,
/// excluded by complement in the type, the interval and the finite set. Whether `p` changed.
bool _equality(Product p, Value v, bool equal, Premises prem) {
  var changed = false;
  if (equal) {
    final lit = Product.literal(v);
    changed |= p.ty.meet(lit.ty.element, prem);
    changed |= p.cell.finite.meet(lit.cell.finite.element, prem);
    if (v case Int(value: final n)) {
      changed |= p.meetInts(IntervalSet.single(n), prem);
      changed |= p.cell.congruence.meet(Congruence.single(n), prem);
    }
    return changed;
  }
  if (Type.lit(v) case final lit?) changed |= p.ty.meet(TypeElement(~lit), prem);
  if (v case Int(value: final n)) {
    changed |= p.meetInts(IntervalSet.single(n).complementIn(p.ints), prem);
  }
  if (p.cell.finite.element.members case final vs?) {
    changed |= p.cell.finite.meet(FiniteSet.of(vs.where((m) => m != v)), prem);
  }
  return changed;
}

/// `t` with each of `env`'s names that it reads bound to its value.
Term _substitute(Term t, Map<String, Value> env) {
  final fr = free(t);
  for (final MapEntry(key: n, value: v) in env.entries) {
    if (fr.contains(n)) t = Let(n, Lit(v), t);
  }
  return t;
}

/// The value of `t`, or null when its run fails.
Value? _run(Term t) {
  try {
    return eval(t);
  } on KernelError {
    return null;
  }
}

/// The element of a value computed at build time, if `t`'s form shows it ends ([ends]) and it
/// evaluates to data.
Product? _runStatic(Term t) {
  if (!ends(t)) return null;
  return switch (_run(t)) {
    final v? when v is! Family => Product.literal(v),
    _ => null,
  };
}

/// The revision table's operator for an integer primitive.
Op? _intOp(Prim p) => switch (p) {
  Prim.add => Op.add,
  Prim.sub => Op.sub,
  Prim.mul => Op.mul,
  Prim.intDiv => Op.div,
  Prim.mod => Op.mod,
  Prim.neg => Op.neg,
  Prim.abs => Op.abs,
  Prim.min => Op.min,
  Prim.max => Op.max,
  _ => null,
};

/// One arm of an `if`: its test, the outcome that takes it, and the scope in it.
final class Arm {
  /// The test, as the kernel prints it.
  final String guard;

  /// The outcome of the test that takes this arm.
  final bool outcome;

  /// The scope in the arm; bottom when no state reaches it.
  final Scope scope;

  Arm(this.guard, this.outcome, this.scope);

  /// Whether some state may reach the arm.
  bool get reachable => !scope.bottom;
}

/// Each `if` arm of `term` with its scope, `term`'s free names in `scope`, in the order the
/// arms are written. The walk enters `let` bindings, `if` arms and primitive and call
/// arguments; it does not enter a function body or a construct that binds names by pattern.
/// The premise of each test is its position in the walk.
List<Arm> arms(Term term, Scope scope) {
  final out = <Arm>[];
  var count = 0;
  // The work left, the next last: a nest of `if`s thousands deep would overflow the call stack.
  // Each step pushes its parts in reverse, so they run in the order they are written.
  final todo = <void Function()>[];
  void walk(Term t, Scope scope) {
    switch (t) {
      case Let(:final name, :final value, :final body):
        todo.add(() => walk(body, scope.bind(name, scope.forward(value))));
        todo.add(() => walk(value, scope));
      case If(cond: final c, then: final a, orElse: final b):
        final prem = Premises.one(Premise.constraint(FactAddress.of(NodeAddress.of([count++]))));
        for (final (o, arm) in [(false, b), (true, a)]) {
          todo.add(() {
            final s = scope.assume(c, o, prem);
            out.add(Arm('$c', o, s));
            walk(arm, s);
          });
        }
      case PrimApp(:final args):
        for (final a in args.reversed) {
          todo.add(() => walk(a, scope));
        }
      case App(:final f, :final args):
        for (final a in args.reversed) {
          todo.add(() => walk(a, scope));
        }
        todo.add(() => walk(f, scope));
      default:
    }
  }

  walk(term, scope);
  while (todo.isNotEmpty) {
    todo.removeLast()();
  }
  return out;
}
