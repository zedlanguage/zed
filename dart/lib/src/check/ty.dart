/// The checker's types (step L1.26): a kernel type for the scalars and atoms, structured
/// tuples, function signatures, type variables, and the unknown type `_` of a value no rule
/// has typed yet (a port's lines, a pattern's bound names).
///
/// A type is a union of pieces: the values of one scalar carrier, the atoms, one tuple shape,
/// one function, one type variable, or the unknown. An operator or a function applies to each
/// combination of its arguments' pieces, so `int | f64` plus `int` is checked as `int + int`
/// and `f64 + int`.
library;

import 'dart:collection';

import '../../resolve.dart' show Binder;
import '../kernel/types.dart';
import '../kernel/value.dart';

/// A scalar carrier, declared in the order a class of values holding a literal tries them;
/// its bit in a mask is `1 << index`.
enum Carrier {
  integer('int'),
  f64('f64'),
  rational('rat'),
  string('String'),
  boolean('bool');

  /// Its name.
  final String label;

  const Carrier(this.label);

  /// Every value of the carrier.
  Type get ty => switch (this) {
    boolean => Type.boolean,
    integer => Type.integer,
    rational => Type.rational,
    f64 => Type.f64,
    string => Type.string,
  };

  /// Whether it is a number.
  bool get numeric => this == integer || this == rational || this == f64;

  /// Its bit in a mask.
  int get bit => 1 << index;

  /// The carriers of the mask `m`, in declaration order.
  static Iterable<Carrier> ofMask(int m) => values.where((c) => m & c.bit != 0);
}

/// The bit of a mask that stands for every value that is not of a carrier: a tuple, a
/// function, an atom.
const other = 1 << 5;

/// The mask of every value.
const every = (1 << 6) - 1;

/// The mask `m` as a type: its carriers joined by `|`, and "other values" for [other].
String maskText(int m) {
  final out = [for (final c in Carrier.ofMask(m)) c.label, if (m & other != 0) 'other values'];
  return out.isEmpty ? 'no type' : out.join(' | ');
}

/// Every atom.
final Type atoms = Type.universe(Universe.scalar) - Type.unionAll(Carrier.values.map((c) => c.ty));

/// The atom `#errs` that two distinct failures merge into, with any payload.
final Type errs = Type.atomWith('errs', Type.top);

/// A piece of a type.
sealed class Piece {
  const Piece();

  /// The carrier of a scalar piece.
  Carrier? get carrier => switch (this) {
    PSet(:final s) => Carrier.values.where((c) => s.subtype(c.ty)).firstOrNull,
    _ => null,
  };

  /// Whether it is a piece of atoms.
  bool get isAtoms => switch (this) {
    PSet(:final s) => s.subtype(atoms),
    _ => false,
  };

  /// The type of this piece alone.
  Ty get ty => switch (this) {
    PSet(:final s) => Ty.of(s),
    PTuple(:final cs) => Ty.tuple(cs),
    PFn(:final s) => Ty.func(s),
    PVar(:final v) => Ty.variable(v),
    PDyn() => Ty.dynamic,
  };
}

/// Scalars: the values of one carrier, the atoms, or what is neither.
final class PSet extends Piece {
  final Type s;

  const PSet(this.s);

  @override
  bool operator ==(Object other) => other is PSet && other.s == s;

  @override
  int get hashCode => s.hashCode;
}

/// A tuple shape.
final class PTuple extends Piece {
  final List<Ty> cs;

  const PTuple(this.cs);

  @override
  bool operator ==(Object other) => other is PTuple && listEq(other.cs, cs);

  @override
  int get hashCode => Object.hashAll(cs);
}

/// A function.
final class PFn extends Piece {
  final Sig s;

  const PFn(this.s);

  @override
  bool operator ==(Object other) => other is PFn && other.s == s;

  @override
  int get hashCode => s.hashCode;
}

/// A type variable.
final class PVar extends Piece {
  final String v;

  const PVar(this.v);

  @override
  bool operator ==(Object other) => other is PVar && other.v == v;

  @override
  int get hashCode => v.hashCode;
}

/// The unknown.
final class PDyn extends Piece {
  const PDyn();

  @override
  bool operator ==(Object other) => other is PDyn;

  @override
  int get hashCode => 0;
}

/// The binding of type variables made while applying an arrow, in the variables' order.
typedef Binds = SplayTreeMap<String, Ty>;

/// Type variables, each once, in order of first appearance.
final class Vars {
  final _seen = <String>{};

  /// The variables, in order.
  final order = <String>[];

  void add(String v) {
    if (_seen.add(v)) order.add(v);
  }
}

/// Whether two lists of types are equal, item by item.
bool listEq<T>(List<T> a, List<T> b) {
  if (identical(a, b)) return true;
  if (a.length != b.length) return false;
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

/// A set of lists of types, by value.
HashSet<List<T>> listSet<T>() => HashSet(equals: listEq, hashCode: Object.hashAll);

/// A type.
final class Ty {
  /// The scalars and atoms, never a tuple or a function.
  final Type set;

  /// The tuple shapes, each with its components.
  final List<List<Ty>> tuples;

  /// The functions.
  final List<Sig> fns;

  /// The type variables, in order.
  final SplayTreeSet<String> vars;

  /// Whether the type holds the unknown `_`.
  final bool isDynamic;

  /// The atoms of `set` that are members of a named atom family: data, which `else` keeps
  /// and an operator rejects (sec:failure). The other atoms are loose.
  final Type family;

  Ty._(this.set, this.tuples, this.fns, this.vars, this.isDynamic, this.family);

  Ty _with({Type? set, List<List<Ty>>? tuples, List<Sig>? fns, Type? family}) => Ty._(
    set ?? this.set,
    tuples ?? this.tuples,
    fns ?? this.fns,
    vars,
    isDynamic,
    family ?? this.family,
  );

  /// No value.
  static final Ty empty = Ty._(Type.empty, const [], const [], SplayTreeSet(), false, Type.empty);

  /// The scalars and atoms of `s`.
  factory Ty.of(Type s) => Ty._(s, const [], const [], SplayTreeSet(), false, Type.empty);

  /// Every value of `c`.
  factory Ty.carrier(Carrier c) => Ty.of(c.ty);

  /// The type of a scalar literal.
  factory Ty.lit(Value v) => Ty.of(Type.lit(v)!);

  /// The tuple shape `(cs…)`.
  factory Ty.tuple(List<Ty> cs) =>
      Ty._(Type.empty, [cs], const [], SplayTreeSet(), false, Type.empty);

  /// The function `s`.
  factory Ty.func(Sig s) => Ty._(Type.empty, const [], [s], SplayTreeSet(), false, Type.empty);

  /// The type variable `v`.
  factory Ty.variable(String v) =>
      Ty._(Type.empty, const [], const [], SplayTreeSet()..add(v), false, Type.empty);

  /// The unknown.
  static final Ty dynamic = Ty._(Type.empty, const [], const [], SplayTreeSet(), true, Type.empty);

  /// Whether no value is in it.
  bool get isEmpty => set.isEmpty && tuples.isEmpty && fns.isEmpty && vars.isEmpty && !isDynamic;

  /// The union.
  Ty union(Ty other) => unionAll([this, other]);

  /// The union of `ts`, built once: joining them one at a time copied the union so far each
  /// time, `O(n²)` in the tuple shapes.
  static Ty unionAll(Iterable<Ty> ts) {
    final all = ts.toList();
    if (all.length == 1) return all[0];
    final tuples = <List<Ty>>[], fns = <Sig>[];
    final seenT = listSet<Ty>(), seenF = <Sig>{};
    final vars = SplayTreeSet<String>();
    var dyn = false;
    for (final t in all) {
      tuples.addAll(t.tuples.where(seenT.add));
      fns.addAll(t.fns.where(seenF.add));
      vars.addAll(t.vars);
      dyn |= t.isDynamic;
    }
    return Ty._(
      Type.unionAll(all.map((t) => t.set)),
      tuples,
      fns,
      vars,
      dyn,
      Type.unionAll(all.map((t) => t.family)),
    );
  }

  /// Its atoms.
  Type get atomSet => set & atoms;

  /// It without its atoms.
  Ty get withoutAtoms => _with(set: set - atoms, family: Type.empty);

  /// It with every atom it holds made a member of a named family, as a `type` declaration
  /// names a union.
  Ty get named => _with(family: atomSet);

  /// It as a written type reads it: every atom loose, the ascription being the visible act
  /// of re-classifying (sec:failure).
  Ty get written => _with(family: Type.empty);

  /// Its loose atoms: those of no named family.
  Type get loose => atomSet - family;

  /// It without its loose atoms, as `e else d` narrows `e`.
  Ty get withoutLoose => _with(set: set - loose);

  /// Its pieces: the scalars split by carrier, then the atoms and the other scalars, the
  /// tuples, the functions, the variables and the unknown.
  List<Piece> get pieces {
    final out = <Piece>[];
    var rest = set;
    for (final c in Carrier.values) {
      final part = set & c.ty;
      if (!part.isEmpty) {
        rest = rest - c.ty;
        out.add(PSet(part));
      }
    }
    final a = rest & atoms;
    if (!a.isEmpty) {
      out.add(PSet(a));
      rest = rest - a;
    }
    if (!rest.isEmpty) out.add(PSet(rest));
    out
      ..addAll(tuples.map(PTuple.new))
      ..addAll(fns.map(PFn.new))
      ..addAll(vars.map(PVar.new));
    if (isDynamic) out.add(const PDyn());
    return out;
  }

  /// The one numeric carrier its numbers are of, when they are of one and it holds nothing
  /// but those numbers and atoms.
  Carrier? get numericCarrier {
    if (tuples.isNotEmpty || fns.isNotEmpty || vars.isNotEmpty || isDynamic) return null;
    final nums = set - atoms;
    if (nums.isEmpty) return null;
    for (final c in const [Carrier.integer, Carrier.rational, Carrier.f64]) {
      if (nums.subtype(c.ty)) return c;
    }
    return null;
  }

  /// Whether it holds no variable and no unknown, at any depth.
  bool get closed => vars.isEmpty && !isDynamic && tuples.every((cs) => cs.every((c) => c.closed));

  /// Whether it holds no function at any depth (a variable or the unknown may still stand
  /// for one): a type whose values the differential oracle compares (step L1.37).
  bool get firstOrder => fns.isEmpty && tuples.every((cs) => cs.every((c) => c.firstOrder));

  /// Whether every value of `this` is in `other`, binding `other`'s variables as needed.
  bool sub(Ty other, Binds binds) => pieces.every((p) => _accepts(other, p, binds));

  /// Whether every value of `this` is in `other`, with no variable bound.
  bool subtype(Ty other) {
    final b = Binds();
    return sub(other, b) && b.isEmpty;
  }

  /// The meet with `t`, as an `is` test narrows: what of `this` is also in `t`.
  Ty meet(Ty t) {
    if (t.isDynamic) return this;
    final s = set & t.set;
    final tuples = <List<Ty>>[];
    final have = listSet<Ty>();
    for (final a in this.tuples) {
      for (final b in t.tuples) {
        if (a.length != b.length) continue;
        final cs = [for (var i = 0; i < a.length; i++) a[i].meet(b[i])];
        if (cs.every((c) => !c.isEmpty) && have.add(cs)) tuples.add(cs);
      }
    }
    final out = Ty._(
      s,
      tuples,
      t.fns.isNotEmpty ? fns : const [],
      SplayTreeSet(),
      false,
      family & s,
    );
    return isDynamic || vars.isNotEmpty ? out.union(t) : out;
  }

  /// What of `this` is not in `t`, as `is not` narrows: scalars are subtracted, tuples
  /// wholly inside `t` dropped, and the rest kept.
  Ty diff(Ty t) {
    final rest = t._with(set: Type.empty);
    return _with(
      set: set - t.set,
      family: family - t.set,
      tuples: [
        for (final a in tuples)
          if (!Ty.tuple(a).subtype(rest)) a,
      ],
    );
  }

  /// `this` with its variables replaced by their bindings.
  Ty subst(Map<String, Ty> binds) {
    if (binds.isEmpty) return this;
    var out = Ty._(
      set,
      [
        for (final cs in tuples) [for (final c in cs) c.subst(binds)],
      ],
      fns,
      SplayTreeSet(),
      isDynamic,
      family,
    );
    final kept = SplayTreeSet<String>();
    for (final v in vars) {
      if (binds[v] case final t?) {
        out = out.union(t);
      } else {
        kept.add(v);
      }
    }
    return kept.isEmpty
        ? out
        : out.union(Ty._(Type.empty, const [], const [], kept, false, Type.empty));
  }

  /// `this` with its variables replaced by `binds` at every depth, inside the functions it
  /// holds too.
  Ty replace(Map<String, Ty> binds) {
    if (binds.isEmpty) return this;
    final out = subst(binds);
    return out._with(
      tuples: [
        for (final cs in out.tuples) [for (final c in cs) c.replace(binds)],
      ],
      fns: [for (final s in out.fns) s.replace(binds)],
    );
  }

  /// Every variable in it, in order of first appearance.
  void varsIn(Vars out) {
    vars.forEach(out.add);
    for (final cs in tuples) {
      for (final c in cs) {
        c.varsIn(out);
      }
    }
    for (final s in fns) {
      for (final a in s.arrows) {
        for (final p in a.params) {
          p.varsIn(out);
        }
        a.result.varsIn(out);
      }
    }
  }

  /// Whether the value `v` is in it; a variable or the unknown holds every value.
  bool contains(Value v) {
    if (isDynamic || vars.isNotEmpty) return true;
    return switch (v) {
      Tuple(:final items) => tuples.any(
        (cs) =>
            cs.length == items.length &&
            [for (var i = 0; i < cs.length; i++) i].every((i) => cs[i].contains(items[i])),
      ),
      Family() || Path() => fns.isNotEmpty,
      _ => set.contains(v),
    };
  }

  /// Whether `this` and `other` may share a value.
  bool meets(Ty other) {
    if (!closed || !other.closed) return true;
    bool shapes(List<Ty> a, List<Ty> b) {
      if (a.length != b.length) return false;
      for (var i = 0; i < a.length; i++) {
        if (!a[i].meets(b[i])) return false;
      }
      return true;
    }

    return !(set & other.set).isEmpty ||
        tuples.any((a) => other.tuples.any((b) => shapes(a, b))) ||
        (fns.isNotEmpty && other.fns.isNotEmpty);
  }

  @override
  bool operator ==(Object other) {
    if (identical(this, other)) return true;
    if (other is! Ty || other.hashCode != hashCode) return false;
    if (other.set != set || other.isDynamic != isDynamic || other.family != family) return false;
    if (other.tuples.length != tuples.length || !listEq(other.fns, fns)) return false;
    for (var i = 0; i < tuples.length; i++) {
      if (!listEq(other.tuples[i], tuples[i])) return false;
    }
    return other.vars.length == vars.length && listEq(other.vars.toList(), vars.toList());
  }

  @override
  late final int hashCode = Object.hash(
    set,
    Object.hashAll(tuples.map(Object.hashAll)),
    Object.hashAll(fns),
    Object.hashAll(vars),
    isDynamic,
    family,
  );

  @override
  String toString() {
    final items = <String>[
      if (!set.isEmpty) surface(set.toString()),
      for (final cs in tuples) cs.length == 1 ? '(${cs[0]},)' : '(${cs.join(', ')})',
      for (final s in fns) '($s)',
      ...vars,
      if (isDynamic) '_',
    ];
    return items.isEmpty ? '!_' : items.join(' | ');
  }
}

/// Whether the piece `p` is in `t`, binding a variable of `t` to it when nothing else of
/// `t` holds it.
bool _accepts(Ty t, Piece p, Binds binds) {
  if (t.isDynamic) return true;
  final ok = switch (p) {
    PDyn() => true,
    PSet(:final s) => s.subtype(t.set),
    PTuple(:final cs) => t.tuples.any((ds) {
      if (ds.length != cs.length) return false;
      final b = Binds.of(binds);
      for (var i = 0; i < cs.length; i++) {
        if (!cs[i].sub(ds[i], b)) return false;
      }
      binds
        ..clear()
        ..addAll(b);
      return true;
    }),
    PFn(:final s) => t.fns.any((q) => fitsSig(s, q)),
    PVar(:final v) => t.vars.contains(v),
  };
  if (ok) return true;
  if (t.vars.isEmpty) return false;
  final v = t.vars.first;
  binds[v] = (binds[v] ?? Ty.empty).union(p.ty);
  return true;
}

/// Whether a function of signature `s` is a function of signature `q`: the same parameter
/// names and kinds, and on each arrow of `q`, an arrow of `s` that takes its parameters and
/// returns within its result.
bool fitsSig(Sig s, Sig q) {
  if (s.params.length != q.params.length) return false;
  for (var i = 0; i < s.params.length; i++) {
    final (a, b) = (s.params[i], q.params[i]);
    if (a.positional != b.positional || !(a.positional || a.name == b.name)) return false;
  }
  return q.arrows.every(
    (qa) => s.arrows.any((sa) {
      final b = Binds();
      for (var i = 0; i < qa.params.length; i++) {
        if (!qa.params[i].sub(sa.params[i], b)) return false;
      }
      for (final MapEntry(key: v, value: m) in s.bounds.entries) {
        final t = b[v];
        if (t != null && !t.pieces.every((p) => m & (p.carrier?.bit ?? 0) != 0)) {
          return false;
        }
      }
      return sa.result.subst(b).subtype(qa.result);
    }),
  );
}

/// A parameter of a signature.
final class SParam {
  /// Its name.
  final String name;

  /// Whether it is passed by position.
  final bool positional;

  /// Its default, if it has one: the declaring function's binder, the parameter's index,
  /// and whether the default reads no name of the unit, so a call through a value can fill
  /// it.
  final ({Binder fn, int index, bool closed})? fallback;

  const SParam(this.name, this.positional, [this.fallback]);

  @override
  bool operator ==(Object other) =>
      other is SParam &&
      other.name == name &&
      other.positional == positional &&
      other.fallback == fallback;

  @override
  int get hashCode => Object.hash(name, positional, fallback);
}

/// One arrow: a type for each parameter, and the result.
final class Arrow {
  /// The parameters' types.
  final List<Ty> params;

  /// The result.
  final Ty result;

  const Arrow(this.params, this.result);

  @override
  bool operator ==(Object other) =>
      other is Arrow && other.result == result && listEq(other.params, params);

  @override
  int get hashCode => Object.hash(Object.hashAll(params), result);
}

/// A function's signature: its parameters' names and kinds, shared by its arrows, which
/// together are an intersection, and the carriers each bounded type variable ranges over.
final class Sig {
  /// The parameters.
  final List<SParam> params;

  /// The arrows.
  final List<Arrow> arrows;

  /// Each bounded type variable, with the mask of the carriers it ranges over: one carrier,
  /// the same at each place the variable stands.
  final SplayTreeMap<String, int> bounds;

  Sig(this.params, this.arrows, [SplayTreeMap<String, int>? bounds])
    : bounds = bounds ?? SplayTreeMap();

  /// One arrow over `params` and `result`, with no bounded variable.
  factory Sig.one(List<SParam> params, List<Ty> tys, Ty result) =>
      Sig(params, [Arrow(tys, result)]);

  /// It with its variables replaced by `binds` at every depth; a bounded variable replaced
  /// by another variable keeps its bound under the new name.
  Sig replace(Map<String, Ty> binds) {
    final out = SplayTreeMap<String, int>();
    for (final MapEntry(key: v, value: m) in bounds.entries) {
      if (binds[v] case final t?) {
        for (final w in t.vars) {
          out[w] = m;
        }
      } else {
        out[v] = m;
      }
    }
    return Sig(params, [
      for (final a in arrows)
        Arrow([for (final p in a.params) p.replace(binds)], a.result.replace(binds)),
    ], out);
  }

  /// Its arrows with each bounded variable fixed to each carrier of its bound: the product
  /// of the bounds, as long as that product is.
  List<Arrow> expand() {
    var out = arrows;
    for (final MapEntry(key: v, value: m) in bounds.entries) {
      out = [
        for (final a in out)
          for (final c in Carrier.ofMask(m))
            for (final b in [
              {v: Ty.carrier(c)},
            ])
              Arrow([for (final p in a.params) p.replace(b)], a.result.replace(b)),
      ];
    }
    return out;
  }

  /// Whether it has the same parameter names and kinds as `other`.
  bool sameKinds(Sig other) {
    if (params.length != other.params.length) return false;
    for (var i = 0; i < params.length; i++) {
      final (a, b) = (params[i], other.params[i]);
      if (a.positional != b.positional || a.name != b.name) return false;
    }
    return true;
  }

  @override
  bool operator ==(Object other) {
    if (identical(this, other)) return true;
    if (other is! Sig || other.hashCode != hashCode) return false;
    if (!listEq(other.params, params) || !listEq(other.arrows, arrows)) return false;
    if (other.bounds.length != bounds.length) return false;
    for (final MapEntry(key: v, value: m) in bounds.entries) {
      if (other.bounds[v] != m) return false;
    }
    return true;
  }

  @override
  late final int hashCode = Object.hash(
    Object.hashAll(params),
    Object.hashAll(arrows),
    Object.hashAll(bounds.entries.map((e) => Object.hash(e.key, e.value))),
  );

  @override
  String toString() {
    final shown = [
      for (final a in arrows)
        '(${[for (var i = 0; i < params.length; i++) params[i].positional ? '${a.params[i]}' : '${params[i].name}: ${a.params[i]}'].join(', ')}) -> ${a.result}',
    ];
    final out = StringBuffer(shown.length == 1 ? shown[0] : shown.map((a) => '($a)').join(' & '));
    if (bounds.isNotEmpty) {
      out.write(' for ');
      out.write(
        [for (final MapEntry(key: v, value: m) in bounds.entries) '$v in ${maskText(m)}']
            .join(', '),
      );
    }
    return out.toString();
  }
}

/// A kernel type's prefix form, in surface syntax: `(| a b)` is `a | b`, `(\ int 3)` is
/// `int \ 3`, `(#a _)` is `#a(_)`, `(tuple A B)` is `(A, B)`, `(! X)` is `!X`, `(& X Y)` is
/// `X & Y`.
String surface(String prefix) {
  final toks = _tokens(prefix);
  var i = 0;
  // The s-expression: a token, or a list of them.
  Object sexpr() {
    final t = toks[i++];
    if (t != '(') return t;
    final items = <Object>[];
    while (i < toks.length && toks[i] != ')') {
      items.add(sexpr());
    }
    i++;
    return items;
  }

  return _show(sexpr(), 0);
}

List<String> _tokens(String s) {
  final out = <String>[];
  var i = 0;
  while (i < s.length) {
    switch (s[i]) {
      case ' ':
        i++;
      case '(' || ')':
        out.add(s[i++]);
      case '"':
        final start = i++;
        while (i < s.length && s[i] != '"') {
          i += s[i] == r'\' ? 2 : 1;
        }
        i++;
        out.add(s.substring(start, i < s.length ? i : s.length));
      default:
        final start = i;
        while (i < s.length && !' ()'.contains(s[i])) {
          i++;
        }
        out.add(s.substring(start, i));
    }
  }
  return out;
}

/// `s` in surface syntax, parenthesized when its operator binds looser than `prec`: 0 for
/// `|`, 1 for `&`, 2 for `\`, 3 for an operand.
String _show(Object s, int prec) {
  if (s is String) return s;
  final items = s as List<Object>;
  if (items.isEmpty || items[0] is! String) return '!_';
  final head = items[0] as String, rest = items.sublist(1);
  String wrap(int p, String text) => prec > p ? '($text)' : text;
  return switch (head) {
    '|' when rest.isEmpty => '!_',
    '|' => wrap(0, rest.map((r) => _show(r, 1)).join(' | ')),
    '&' => wrap(1, rest.map((r) => _show(r, 2)).join(' & ')),
    r'\' => wrap(2, '${_show(rest[0], 3)} \\ ${_taken(rest.sublist(1))}'),
    '!' => '!${_show(rest[0], 3)}',
    'tuple' => switch (rest.map((r) => _show(r, 0)).toList()) {
      [final c] => '($c,)',
      final cs => '(${cs.join(', ')})',
    },
    _ when head.startsWith('#') => '$head(${_show(rest[0], 0)})',
    _ => '($head ${rest.map((r) => _show(r, 3)).join(' ')})',
  };
}

String _taken(List<Object> rest) => switch (rest.map((r) => _show(r, 3)).toList()) {
  [final t] => t,
  final ts => '(${ts.join(' | ')})',
};
