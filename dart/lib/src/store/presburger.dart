/// The linear-relation domain (DESIGN.md sec:domains, "linear-integer relations among in-scope
/// keys and cardinalities (Presburger)", and sec:verification, rung 2; step L1.38).
///
/// A relation is a quantifier-free formula over linear constraints with integer coefficients,
/// `t >= 0` and `t == 0`, joined by `&&`, `||` and `!`. A constraint's term is a sum of atoms,
/// each times a coefficient, plus a constant. An atom is a symbol, the product of two symbols,
/// or an auxiliary variable that names a quotient or a remainder by a constant; the formula
/// that defines an auxiliary variable is kept apart from the body, since it fixes the variable
/// for each value of the symbols, so that negating the body never negates a definition.
///
/// Satisfiability is decided by the Omega test [Omega] on the fragment it settles in
/// polynomial time, with no budget (docs/thresholds.md, replacement 4). Equalities are
/// solved, with Pugh's symmetric remainder where no coefficient is a unit. An
/// inequality-only problem eliminates one variable at a time, and only while the system
/// holds no more rows than it was given: each step removes a variable and the rows never
/// pass the input's count. An elimination is exact when every lower or every upper
/// coefficient of the variable is a unit; otherwise a point of the dark shadow is a point of
/// the problem and an empty real shadow, read over the rationals, shows the problem empty, and
/// between the two the question is undecided. A satisfiable problem yields a model: each
/// eliminated variable takes the value nearest zero that its bounds allow under the values of
/// the variables eliminated after it.
///
/// A formula with disjunctions is not split into all its conjunctions. Its top-level
/// constraints are the base; a disjunct whose own top-level constraints meet the base nowhere
/// is removed, and a disjunction with one disjunct left adds it to the base, until nothing is
/// removed: each round removes a disjunct, so the rounds are at most the disjuncts. No
/// disjunct left is no point. A point is then sought by taking, for each disjunction in turn,
/// the first disjunct that meets the base with the disjuncts already taken. Where none does,
/// each disjunct whose addition to the base empties it by the rule above is removed, until
/// none is, and the search runs again; where it fails again, the question is undecided. A
/// projection is the meet, over the disjunctions, of the union over each one's disjuncts of
/// the projection of the base with that disjunct; with two disjunctions or more left, each
/// finite bound is then moved inward by halving the step, only where the formula with the
/// value past it is shown empty. Each loop removes a disjunct or halves a step, so each ends.
///
/// Entailment from premises to a goal is the unsatisfiability of the premises with the negated
/// goal. A product of two symbols is an atom of its own, so the test still decides linear
/// facts; before it, for each product the formulas mention, the premises on its factors are
/// multiplied in pairs, once: a premise on a symbol is a top-level linear inequality of the
/// premises that mentions it, or a bound on the symbol that the linear premises imply.
///
/// Coefficients are integers of any size, so no arithmetic overflows. An undecided question
/// throws [Over], and leaves the relation unused, which is sound: the written constraint is
/// kept.
library;

import 'dart:collection';

import 'interval.dart';

/// A variable of a relation, ordered symbols first, then products, then auxiliary variables.
sealed class Atom implements Comparable<Atom> {
  const Atom();

  /// The product of two symbols.
  static Atom product(String a, String b) => a.compareTo(b) <= 0 ? Product(a, b) : Product(b, a);

  int get _rank;

  @override
  int compareTo(Atom other) {
    final r = _rank - other._rank;
    if (r != 0) return r;
    return switch ((this, other)) {
      (Sym(:final name), Sym(name: final o)) => name.compareTo(o),
      (Product(:final a, :final b), Product(a: final c, b: final d)) =>
        a.compareTo(c) != 0 ? a.compareTo(c) : b.compareTo(d),
      (Aux(:final n), Aux(n: final m)) => n - m,
      _ => 0,
    };
  }
}

/// A symbol: an input, a parameter, a key.
final class Sym extends Atom {
  final String name;

  const Sym(this.name);

  @override
  int get _rank => 0;

  @override
  bool operator ==(Object other) => other is Sym && other.name == name;

  @override
  int get hashCode => name.hashCode;

  @override
  String toString() => name;
}

/// The product of two symbols, in name order.
final class Product extends Atom {
  final String a, b;

  const Product(this.a, this.b);

  @override
  int get _rank => 1;

  @override
  bool operator ==(Object other) => other is Product && other.a == a && other.b == b;

  @override
  int get hashCode => Object.hash(a, b);

  @override
  String toString() => '$a * $b';
}

/// An auxiliary variable, defined by the relation's definitions.
final class Aux extends Atom {
  final int n;

  const Aux(this.n);

  @override
  int get _rank => 2;

  @override
  bool operator ==(Object other) => other is Aux && other.n == n;

  @override
  int get hashCode => n.hashCode;

  @override
  String toString() => 'q$n';
}

/// A question outside the fragment the Omega test decides: the relation is dropped.
final class Over implements Exception {
  const Over();

  @override
  String toString() => 'undecided: outside the fragment the Omega test decides';
}

/// The order of two maps of coefficients: entry by entry, key then value, a prefix first.
int _compareMaps<K>(Map<K, BigInt> a, Map<K, BigInt> b, int Function(K, K) keys) {
  final ia = a.entries.iterator, ib = b.entries.iterator;
  while (true) {
    final (na, nb) = (ia.moveNext(), ib.moveNext());
    if (!na || !nb) return (na ? 1 : 0) - (nb ? 1 : 0);
    final c = keys(ia.current.key, ib.current.key);
    if (c != 0) return c;
    final d = ia.current.value.compareTo(ib.current.value);
    if (d != 0) return d;
  }
}

int _compareAtoms(Atom a, Atom b) => a.compareTo(b);

int _compareInts(int a, int b) => a - b;

int _hashMap<K>(Map<K, BigInt> m) => Object.hashAll([
  for (final MapEntry(:key, :value) in m.entries) ...[key, value],
]);

/// Adds `c` to the coefficient of `k` in `m`, removing a coefficient that becomes zero.
void _addTo<K>(Map<K, BigInt> m, K k, BigInt c) {
  final v = (m[k] ?? BigInt.zero) + c;
  if (v == BigInt.zero) {
    m.remove(k);
  } else {
    m[k] = v;
  }
}

/// The Euclidean quotient: the remainder `a - q·b` is in `0..abs(b)`.
BigInt _divEuclid(BigInt a, BigInt b) => (a - a % b) ~/ b;

/// A linear term: each atom times its coefficient, plus a constant. No coefficient is zero.
/// A term is not changed once made.
final class Lin implements Comparable<Lin> {
  /// The coefficients.
  final SplayTreeMap<Atom, BigInt> terms;

  /// The constant.
  final BigInt constant;

  Lin._(this.terms, this.constant);

  /// The constant `k`.
  Lin.constant(this.constant) : terms = SplayTreeMap();

  /// The atom `a`.
  Lin.atom(Atom a) : terms = SplayTreeMap.of({a: BigInt.one}), constant = BigInt.zero;

  /// `0`.
  static final zero = Lin.constant(BigInt.zero);

  /// `this + other`.
  Lin plus(Lin other) {
    final out = SplayTreeMap.of(terms);
    other.terms.forEach((a, c) => _addTo(out, a, c));
    return Lin._(out, constant + other.constant);
  }

  /// `this * k`.
  Lin times(BigInt k) {
    if (k == BigInt.zero) return zero;
    return Lin._(SplayTreeMap.of(terms.map((a, c) => MapEntry(a, c * k))), constant * k);
  }

  /// `this - other`.
  Lin minus(Lin other) => plus(other.times(BigInt.from(-1)));

  /// Whether every atom is a symbol or an auxiliary variable.
  bool get isLinear => !terms.keys.any((a) => a is Product);

  /// The product of two terms, its products of two symbols as atoms; null when neither is a
  /// constant and either holds an atom that is not a symbol.
  Lin? product(Lin other) {
    if (terms.isEmpty) return other.times(constant);
    if (other.terms.isEmpty) return times(other.constant);
    bool syms(Lin l) => l.terms.keys.every((a) => a is Sym);
    if (!syms(this) || !syms(other)) return null;
    final out = SplayTreeMap.of(terms.map((a, c) => MapEntry(a, c * other.constant)));
    out.removeWhere((_, c) => c == BigInt.zero);
    other.terms.forEach((a, c) {
      _addTo(out, a, c * constant);
      terms.forEach((b, d) {
        _addTo(out, Atom.product((a as Sym).name, (b as Sym).name), c * d);
      });
    });
    return Lin._(out, constant * other.constant);
  }

  /// The value at `values`, each atom absent from it zero.
  BigInt eval(Map<Atom, BigInt> values) {
    var v = constant;
    terms.forEach((a, c) => v += c * (values[a] ?? BigInt.zero));
    return v;
  }

  @override
  int compareTo(Lin other) {
    final c = _compareMaps(terms, other.terms, _compareAtoms);
    return c != 0 ? c : constant.compareTo(other.constant);
  }

  @override
  bool operator ==(Object other) => other is Lin && compareTo(other) == 0;

  @override
  late final int hashCode = Object.hash(_hashMap(terms), constant);

  @override
  String toString() {
    final out = StringBuffer();
    var first = true;
    terms.forEach((a, c) {
      final m = c.abs();
      if (first) {
        if (c.isNegative) out.write('-');
      } else {
        out.write(c.isNegative ? ' - ' : ' + ');
      }
      out.write(m == BigInt.one ? '$a' : '$m * $a');
      first = false;
    });
    if (first) {
      out.write(constant);
    } else if (constant > BigInt.zero) {
      out.write(' + $constant');
    } else if (constant < BigInt.zero) {
      out.write(' - ${-constant}');
    }
    return out.toString();
  }
}

/// How a constraint's term compares with zero.
enum Rel {
  /// `t >= 0`.
  ge,

  /// `t == 0`.
  eq,
}

/// A quantifier-free formula over linear constraints.
sealed class Formula {
  const Formula();

  /// `true`.
  static const Formula top = And([]);

  /// `false`.
  static const Formula bottom = Or([]);

  /// The conjunction, flattened, `true` dropped and `false` absorbing.
  static Formula and(List<Formula> fs) {
    final flat = <Formula>[];
    for (final f in fs) {
      switch (f) {
        case And(:final items):
          flat.addAll(items);
        case Or(:final items) when items.isEmpty:
          return bottom;
        default:
          flat.add(f);
      }
    }
    // Of two constraints on one term, the tighter alone, in the place of the first.
    final out = <Formula>[];
    final at = <(Lin, Rel), int>{};
    for (final g in flat) {
      if (g is! Con) {
        out.add(g);
        continue;
      }
      final key = (Lin._(g.lin.terms, BigInt.zero), g.rel);
      if (at[key] case final i?) {
        final old = out[i] as Con;
        if (g.rel == Rel.ge && g.lin.constant < old.lin.constant) {
          out[i] = g;
        } else if (g.rel == Rel.eq && g.lin.constant != old.lin.constant) {
          return bottom;
        }
      } else {
        at[key] = out.length;
        out.add(g);
      }
    }
    return out.length == 1 ? out.single : And(out);
  }

  /// The disjunction, flattened, `false` dropped and `true` absorbing.
  static Formula or(List<Formula> fs) {
    final out = <Formula>[];
    for (final f in fs) {
      switch (f) {
        case Or(:final items):
          out.addAll(items);
        case And(:final items) when items.isEmpty:
          return top;
        default:
          out.add(f);
      }
    }
    return out.length == 1 ? out.single : Or(out);
  }

  /// The disjunction of `a` and `b` with the conjuncts they share taken out of it, so that
  /// joining two narrowings of one relation does not copy the relation into each disjunct.
  static Formula either(Formula a, Formula b) {
    final (pa, pb) = (a.conjuncts, b.conjuncts);
    final inB = pb.toSet();
    final shared = pa.where(inB.contains).toSet();
    Formula rest(List<Formula> p) => and([...p.where((g) => !shared.contains(g))]);
    return and([
      ...pa.where(shared.contains),
      or([rest(pa), rest(pb)]),
    ]);
  }

  /// The negation, with double negations and constants removed.
  static Formula negate(Formula f) => switch (f) {
    Not(:final inner) => inner,
    And(:final items) when items.isEmpty => bottom,
    Or(:final items) when items.isEmpty => top,
    _ => Not(f),
  };

  /// The formula with every constraint that mentions `sym`, alone or in a product, replaced
  /// by `true` where it occurs under an even number of negations and by `false` where under an
  /// odd number: a formula implied by this one that says nothing of `sym`.
  Formula forget(String sym) {
    Formula go(Formula f, bool pos) => switch (f) {
      Con(:final lin) =>
        lin.terms.keys.any(
              (a) => switch (a) {
                Sym(:final name) => name == sym,
                Product(:final a, :final b) => a == sym || b == sym,
                Aux() => false,
              },
            )
            ? (pos ? top : bottom)
            : f,
      Not(:final inner) => negate(go(inner, !pos)),
      And(:final items) => and([for (final g in items) go(g, pos)]),
      Or(:final items) => or([for (final g in items) go(g, pos)]),
    };
    return go(this, true);
  }

  /// Each constraint, in order.
  List<Con> get cons {
    final out = <Con>[];
    void walk(Formula f) {
      switch (f) {
        case Con():
          out.add(f);
        case Not(:final inner):
          walk(inner);
        case And(:final items) || Or(:final items):
          items.forEach(walk);
      }
    }

    walk(this);
    return out;
  }

  /// Each atom, in order.
  SplayTreeSet<Atom> get atoms => SplayTreeSet.of([for (final c in cons) ...c.lin.terms.keys]);

  /// Whether the formula holds at `values`; an absent atom is zero, and a product atom is read
  /// as the product of its symbols' values.
  bool holds(Map<Atom, BigInt> values) {
    final vs = Map.of(values);
    BigInt v(String s) => values[Sym(s)] ?? BigInt.zero;
    for (final a in atoms) {
      if (a case Product(a: final x, b: final y)) vs[a] = v(x) * v(y);
    }
    return holdsAs(vs);
  }

  /// Whether the formula holds at `vs`, each atom read as its value there.
  bool holdsAs(Map<Atom, BigInt> vs) => switch (this) {
    Con(:final lin, :final rel) =>
      rel == Rel.eq ? lin.eval(vs) == BigInt.zero : lin.eval(vs) >= BigInt.zero,
    Not(:final inner) => !inner.holdsAs(vs),
    And(:final items) => items.every((g) => g.holdsAs(vs)),
    Or(:final items) => items.any((g) => g.holdsAs(vs)),
  };

  /// The top-level conjuncts.
  List<Formula> get conjuncts => switch (this) {
    And(:final items) => items,
    _ => [this],
  };

  /// `g` as a part of a conjunction or a disjunction, in parentheses when it is one of more
  /// than one part.
  static String _part(Formula g) => switch (g) {
    And(:final items) || Or(:final items) when items.length > 1 => '($g)',
    _ => '$g',
  };
}

/// A linear constraint.
final class Con extends Formula implements Comparable<Con> {
  /// The term.
  final Lin lin;

  /// Its comparison with zero.
  final Rel rel;

  const Con(this.lin, this.rel);

  /// `a >= b`.
  Con.ge(Lin a, Lin b) : this(a.minus(b), Rel.ge);

  /// `a == b`.
  Con.eq(Lin a, Lin b) : this(a.minus(b), Rel.eq);

  @override
  int compareTo(Con other) {
    final c = lin.compareTo(other.lin);
    return c != 0 ? c : rel.index - other.rel.index;
  }

  @override
  bool operator ==(Object other) => other is Con && other.lin == lin && other.rel == rel;

  @override
  int get hashCode => Object.hash(lin, rel);

  /// The terms with the sign of the first atom's on the left, positive, and the rest on the
  /// right: `a + b <= 49`, `i <= n - 2`.
  @override
  String toString() {
    if (lin.terms.isEmpty) return '${lin.constant} ${rel == Rel.eq ? '==' : '>='} 0';
    final neg = lin.terms.values.first.isNegative;
    final left = SplayTreeMap<Atom, BigInt>(), right = SplayTreeMap<Atom, BigInt>();
    lin.terms.forEach((a, c) => (c.isNegative == neg ? left : right)[a] = c.abs());
    // left_sign * left - right_sign * right + k (rel) 0, with left positive.
    final k = neg ? lin.constant : -lin.constant;
    final op = rel == Rel.eq ? '==' : (neg ? '<=' : '>=');
    return '${Lin._(left, BigInt.zero)} $op ${Lin._(right, k)}';
  }
}

/// Negation.
final class Not extends Formula {
  final Formula inner;

  const Not(this.inner);

  @override
  bool operator ==(Object other) => other is Not && other.inner == inner;

  @override
  int get hashCode => Object.hash(Not, inner);

  @override
  String toString() => switch (inner) {
    Con() || And() || Or() => '!($inner)',
    _ => '!$inner',
  };
}

/// Conjunction; empty is `true`.
final class And extends Formula {
  final List<Formula> items;

  const And(this.items);

  @override
  bool operator ==(Object other) => other is And && _sameItems(other.items, items);

  @override
  int get hashCode => Object.hash(And, Object.hashAll(items));

  @override
  String toString() => items.isEmpty ? 'true' : items.map(Formula._part).join(' && ');
}

/// Disjunction; empty is `false`.
final class Or extends Formula {
  final List<Formula> items;

  const Or(this.items);

  @override
  bool operator ==(Object other) => other is Or && _sameItems(other.items, items);

  @override
  int get hashCode => Object.hash(Or, Object.hashAll(items));

  @override
  String toString() => items.isEmpty ? 'false' : items.map(Formula._part).join(' || ');
}

bool _sameItems(List<Formula> a, List<Formula> b) {
  if (a.length != b.length) return false;
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

/// A relation: a body, and the definitions of its auxiliary variables, each of which fixes
/// one auxiliary variable for every value of the others.
final class Relation {
  /// The body.
  final Formula body;

  /// The definitions, each an auxiliary variable, what it names, and the formula that fixes
  /// it.
  final List<(int, String, Formula)> defs;

  const Relation(this.body, this.defs);

  /// The relation `body`, with no auxiliary variable.
  const Relation.of(this.body) : defs = const [];

  /// The definitions, as one formula.
  Formula get defined => Formula.and([for (final (_, _, f) in defs) f]);

  @override
  String toString() => [
    '$body',
    for (var i = 0; i < defs.length; i++)
      '${i == 0 ? ' where' : ','} q${defs[i].$1} = ${defs[i].$2}',
  ].join();
}

/// A satisfying assignment, in atom order, each atom absent from it zero.
typedef Model = SplayTreeMap<Atom, BigInt>;

/// Whether `f` holds somewhere: a point where it does, or null where it holds nowhere.
/// Throws [Over] when the question is undecided.
Model? satisfiable(Formula f) {
  final p = _propagate(f);
  if (p == null) return null;
  try {
    return _pick(p);
  } on Over {
    // Undecided by the first search; the second follows the removal of disjuncts.
  }
  final q = _probe(p);
  return q == null ? null : _pick(q);
}

/// Whether `f` is shown to hold nowhere; an undecided question is not.
bool _empty(Formula f) {
  try {
    return satisfiable(f) == null;
  } on Over {
    return false;
  }
}

/// [_solve], with an undecided question read as a point.
bool _mayMeet(List<Con> cons) {
  try {
    return _solve(cons) != null;
  } on Over {
    return true;
  }
}

/// A point of `p`, taking for each disjunction in turn the first disjunct that meets the
/// constraints taken so far; throws [Over] when none does.
Model _pick(_Parts p) {
  var model = _solve(p.cons) ?? (throw const Over());
  final acc = [...p.cons];
  final queue = [...p.ors];
  while (queue.isNotEmpty) {
    final ds = queue.removeLast();
    (Formula, Model)? taken;
    for (final d in ds) {
      Model? m;
      try {
        m = _solve([...acc, ..._lits(d)]);
      } on Over {
        m = null;
      }
      if (m != null) {
        taken = (d, m);
        break;
      }
    }
    if (taken == null) throw const Over();
    model = taken.$2;
    final q = _Parts()..add(taken.$1);
    acc.addAll(q.cons);
    queue.addAll(q.ors);
  }
  return model;
}

/// `p` with each disjunct removed whose addition, propagated, leaves no point, until none is
/// removed, or null when `p` has no point. Each round but the last removes a disjunct, and
/// each tests every disjunct by one propagation, so the work is polynomial in the disjuncts.
_Parts? _probe(_Parts p) {
  while (true) {
    var changed = false;
    for (var i = 0; i < p.ors.length; i++) {
      final ds = p.ors[i];
      p.ors[i] = const [];
      final live = [
        for (final d in ds)
          if (!_settlesEmpty(_Parts.of([...p.cons], [...p.ors.where((o) => o.isNotEmpty)])..add(d)))
            d,
      ];
      changed |= live.length < ds.length;
      if (live.isEmpty) return null;
      p.ors[i] = live;
    }
    if (!changed) return p;
    final q = _settle(p);
    if (q == null) return null;
    p = q;
  }
}

/// Whether [_settle] shows `p` has no point; an undecided question is not.
bool _settlesEmpty(_Parts p) {
  try {
    return _settle(p) == null;
  } on Over {
    return false;
  }
}

/// A formula in negation normal form as its top-level constraints and its top-level
/// disjunctions, each a list of disjuncts.
final class _Parts {
  final List<Con> cons;
  List<List<Formula>> ors;

  _Parts() : cons = [], ors = [];

  _Parts.of(this.cons, this.ors);

  /// Adds a formula in negation normal form.
  void add(Formula f) {
    switch (f) {
      case Con():
        cons.add(f);
      case And(:final items):
        items.forEach(add);
      case Or(:final items):
        ors.add(items);
      case Not():
        throw StateError('a formula in negation normal form');
    }
  }
}

/// `f`, negated when `!sign`, with each negation pushed to the constraints: not `t >= 0` is
/// `-t - 1 >= 0`, and not `t == 0` is `t >= 1 || -t >= 1`.
Formula _nnf(Formula f, bool sign) {
  switch ((f, sign)) {
    case (Not(:final inner), _):
      return _nnf(inner, !sign);
    case (And(:final items), true) || (Or(:final items), false):
      return Formula.and([for (final g in items) _nnf(g, sign)]);
    case (And(:final items), false) || (Or(:final items), true):
      return Formula.or([for (final g in items) _nnf(g, sign)]);
    case (Con(), true):
      return f;
    case (Con(:final lin, :final rel), false):
      final one = Lin.constant(BigInt.one);
      final neg = Con.ge(Lin.zero, lin.plus(one));
      return rel == Rel.ge ? neg : Formula.or([Con.ge(lin, one), neg]);
  }
}

/// The top-level constraints of a formula in negation normal form.
List<Con> _lits(Formula f) => switch (f) {
  Con() => [f],
  And(:final items) => [for (final g in items) ..._lits(g)],
  _ => const [],
};

/// The formula's base and disjunctions once no disjunct can be removed, or null when it has
/// no point. A disjunct is removed when its top-level constraints meet the base nowhere; a
/// disjunction left with one disjunct adds it to the base. Each round but the last removes a
/// disjunct, so there are at most as many rounds as disjuncts, each a test of every disjunct.
_Parts? _propagate(Formula f) => _settle(_Parts()..add(_nnf(f, true)));

/// [_propagate] from parts.
_Parts? _settle(_Parts p) {
  while (true) {
    if (_solve(p.cons) == null) return null;
    var changed = false;
    final kept = <List<Formula>>[];
    for (final ds in p.ors) {
      final live = [
        for (final d in ds)
          if (_mayMeet([...p.cons, ..._lits(d)])) d,
      ];
      changed |= live.length < ds.length;
      switch (live.length) {
        case 0:
          return null;
        case 1:
          final q = _Parts()..add(live.single);
          p.cons.addAll(q.cons);
          kept.addAll(q.ors);
        default:
          kept.add(live);
      }
    }
    p.ors = kept;
    if (!changed) return p;
  }
}

/// Whether a conjunction of constraints holds somewhere, and where.
Model? _solve(List<Con> cons) {
  final atoms = SplayTreeSet<Atom>.of([for (final c in cons) ...c.lin.terms.keys]).toList();
  final index = {for (var i = 0; i < atoms.length; i++) atoms[i]: i};
  final eqs = <_Row>[], ges = <_Row>[];
  for (final c in cons) {
    final row = _Row(
      SplayTreeMap.of(c.lin.terms.map((a, k) => MapEntry(index[a]!, k))),
      c.lin.constant,
      c.rel == Rel.eq,
    );
    (row.eq ? eqs : ges).add(row);
  }
  final found = _Omega(atoms.length, cons.length).solve(eqs, ges);
  if (found == null) return null;
  return Model.of({for (var i = 0; i < atoms.length; i++) atoms[i]: ?found[i]});
}

/// The values of the solver's variables, each absent one zero.
typedef _Vals = Map<int, BigInt>;

/// What normalizing a row gives: the row, or whether it holds everywhere.
sealed class _Norm {}

final class _Truth extends _Norm {
  final bool holds;

  _Truth(this.holds);
}

/// `Σ a[i]·x[i] + k`, compared with zero by `==` or `>=`.
final class _Row extends _Norm {
  final SplayTreeMap<int, BigInt> a;
  final BigInt k;
  final bool eq;

  _Row(this.a, this.k, this.eq);

  BigInt eval(_Vals m) {
    var v = k;
    a.forEach((i, c) => v += c * (m[i] ?? BigInt.zero));
    return v;
  }

  /// The row divided by the gcd of its coefficients, an inequality's constant rounded down.
  _Norm normal() {
    final g = a.values.fold(BigInt.zero, (g, c) => g.gcd(c));
    if (g == BigInt.zero) return _Truth(eq ? k == BigInt.zero : k >= BigInt.zero);
    if (eq && k % g != BigInt.zero) return _Truth(false);
    return _Row(SplayTreeMap.of(a.map((i, c) => MapEntry(i, c ~/ g))), _divEuclid(k, g), eq);
  }

  /// The row with `x[j]` replaced by `def`.
  _Row subst(int j, _Row def) {
    final c = a[j];
    if (c == null) return this;
    final out = SplayTreeMap.of(a)..remove(j);
    def.a.forEach((i, d) => _addTo(out, i, c * d));
    return _Row(out, k + c * def.k, eq);
  }

  /// The row without `x[j]`.
  _Row rest(int j) => _Row(SplayTreeMap.of(a)..remove(j), k, eq);
}

/// Pugh's symmetric remainder: `a - m·floor(a/m + 1/2)`.
BigInt _modHat(BigInt a, BigInt m) {
  final r = a % m;
  return r * BigInt.two >= m ? r - m : r;
}

SplayTreeMap<int, BigInt> _opposite(Map<int, BigInt> a) =>
    SplayTreeMap.of(a.map((i, c) => MapEntry(i, -c)));

int _compareRows(Map<int, BigInt> x, Map<int, BigInt> y) => _compareMaps(x, y, _compareInts);

/// How a variable occurs in the inequalities: as a lower or an upper bound, and how often with
/// a coefficient that is not a unit.
final class _Sides {
  int lo = 0, hi = 0, loWide = 0, hiWide = 0;

  /// Whether no elimination of the variable is exact.
  bool get inexact => loWide > 0 && hiWide > 0;

  /// The rows its elimination adds less the rows it removes.
  int get growth => lo * hi - lo - hi;

  bool get oneSided => lo == 0 || hi == 0;
}

/// A system of inequalities, kept normalized as rows are added and removed: each set of
/// coefficients is held once, with its least constant, and each variable knows its rows and
/// how it occurs in them, so that a step touches only the rows of the variable it eliminates.
final class _System {
  final rows = SplayTreeMap<SplayTreeMap<int, BigInt>, _Row>(_compareRows);
  final _of = <int, Set<_Row>>{};
  final _sides = <int, _Sides>{};

  /// The variables whose elimination is exact, and those whose is not, by its growth and
  /// their index.
  final exact = SplayTreeSet<(int, int)>(_compareGrowth);
  final inexact = SplayTreeSet<(int, int)>(_compareGrowth);

  /// The variables bounded on one side only.
  final oneSided = SplayTreeSet<int>();

  /// The lesser coefficients of two opposite rows whose constants sum to zero; a pair may since
  /// have changed, and is checked when taken.
  final _meets = SplayTreeSet<SplayTreeMap<int, BigInt>>(_compareRows);

  /// Whether a row is false, or two opposite rows meet nowhere.
  bool empty = false;

  _System(Iterable<_Row> rows) {
    rows.forEach(add);
  }

  void add(_Row r) {
    switch (r.normal()) {
      case _Truth(holds: false):
        empty = true;
      case _Truth():
        break;
      case final _Row row:
        final old = rows[row.a];
        if (old != null) {
          if (old.k <= row.k) return;
          _remove(old);
        }
        rows[row.a] = row;
        _count(row, 1);
        final opp = _opposite(row.a);
        if (rows[opp] case final o?) {
          final s = row.k + o.k;
          if (s < BigInt.zero) empty = true;
          if (s == BigInt.zero) _meets.add(_compareRows(row.a, opp) < 0 ? row.a : opp);
        }
    }
  }

  void _remove(_Row r) {
    rows.remove(r.a);
    _count(r, -1);
  }

  /// Counts `r` in, or out when `d` is -1, at each of its variables.
  void _count(_Row r, int d) {
    r.a.forEach((i, c) {
      final s = _sides.putIfAbsent(i, _Sides.new);
      (s.inexact ? inexact : exact).remove((s.growth, i));
      oneSided.remove(i);
      final wide = c.abs() != BigInt.one;
      if (c > BigInt.zero) {
        s.lo += d;
        if (wide) s.loWide += d;
      } else {
        s.hi += d;
        if (wide) s.hiWide += d;
      }
      final rs = _of.putIfAbsent(i, () => {});
      if (d > 0) {
        rs.add(r);
      } else {
        rs.remove(r);
      }
      if (s.lo + s.hi == 0) return;
      (s.inexact ? inexact : exact).add((s.growth, i));
      if (s.oneSided) oneSided.add(i);
    });
  }

  /// Removes the rows that hold `x[j]`, and returns them.
  List<_Row> take(int j) {
    final out = [...?_of[j]];
    out.forEach(_remove);
    return out;
  }

  /// The rows of two opposite rows that meet in an equality, the lesser coefficients first.
  _Row? meeting() {
    while (_meets.isNotEmpty) {
      final a = _meets.first;
      final (r, o) = (rows[a], rows[_opposite(a)]);
      if (r != null && o != null && r.k + o.k == BigInt.zero) {
        _remove(r);
        _remove(o);
        _meets.remove(a);
        return r;
      }
      _meets.remove(a);
    }
    return null;
  }

  /// The variable of least growth among the exact eliminations, or failing that the inexact
  /// ones, the first on a tie, whose elimination leaves no more than `room` rows.
  (bool, int)? best(int room) {
    for (final (wide, set) in [(false, exact), (true, inexact)]) {
      if (set.firstOrNull case (final g, final j) when rows.length + g <= room) return (wide, j);
    }
    return null;
  }

  /// Eliminates `x[j]` by its real shadow, or its dark one when `dark`; returns its rows.
  List<_Row> eliminate(int j, bool dark) {
    final withJ = take(j);
    final lowers = [...withJ.where((r) => r.a[j]! > BigInt.zero)];
    final uppers = [...withJ.where((r) => r.a[j]! < BigInt.zero)];
    for (final lo in lowers) {
      for (final hi in uppers) {
        add(_combine(lo, hi, j, dark));
      }
    }
    return withJ;
  }
}

/// The equalities as a stack, a slot emptied when its row holds everywhere, with the slots of
/// each variable.
final class _Equalities {
  final _System sys;
  final _rows = <_Row?>[];
  final _of = <int, Set<int>>{};

  _Equalities(this.sys);

  /// The last equality, if any.
  int? get last {
    while (_rows.isNotEmpty && _rows.last == null) {
      _rows.removeLast();
    }
    return _rows.isEmpty ? null : _rows.length - 1;
  }

  _Row operator [](int s) => _rows[s]!;

  void push(_Row r) {
    _rows.add(null);
    _put(_rows.length - 1, r);
  }

  void _put(int s, _Row r) {
    switch (r.normal()) {
      case _Truth(holds: false):
        sys.empty = true;
      case _Truth():
        break;
      case final _Row row:
        _rows[s] = row;
        for (final i in row.a.keys) {
          _of.putIfAbsent(i, () => {}).add(s);
        }
    }
  }

  void clear(int s) {
    for (final i in _rows[s]!.a.keys) {
      _of[i]!.remove(s);
    }
    _rows[s] = null;
  }

  /// Replaces `x[j]` by `def` in each equality that holds it.
  void subst(int j, _Row def) {
    for (final s in [...?_of[j]]) {
      final r = this[s];
      clear(s);
      _put(s, r.subst(j, def));
    }
  }
}

/// A step the model is built back through, last step first.
sealed class _Step {
  final int j;

  _Step(this.j);
}

/// `x[j]` defined by an equality.
final class _Defined extends _Step {
  final _Row def;

  _Defined(super.j, this.def);
}

/// `x[j]` chosen within the rows that held it.
final class _Chosen extends _Step {
  final List<_Row> rows;

  _Chosen(super.j, this.rows);
}

/// The Omega test. Each step solves an equality, turns two opposite rows that meet into one,
/// drops a variable bounded on one side only, or eliminates a variable, until no row is left;
/// the model is then built back through the steps.
final class _Omega {
  /// The next fresh variable.
  int next;

  /// The most rows an elimination may leave: the rows of the problem as given.
  final int room;

  _Omega(this.next, this.room);

  _Vals? solve(List<_Row> eqs, List<_Row> ges) {
    final sys = _System(ges);
    final es = _Equalities(sys);
    eqs.forEach(es.push);
    final steps = <_Step>[];
    // Below an inexact elimination only the dark shadow is solved, so an empty problem there is
    // undecided, and the real shadow is tried once, at the first.
    var dark = false;
    while (true) {
      if (sys.empty) {
        if (dark) throw const Over();
        return null;
      }
      if (es.last case final s?) {
        _equality(s, es, steps);
        continue;
      }
      if (sys.meeting() case final r?) {
        es.push(_Row(r.a, r.k, true));
        continue;
      }
      if (sys.rows.isEmpty) break;
      if (sys.oneSided.firstOrNull case final j?) {
        steps.add(_Chosen(j, sys.take(j)));
        continue;
      }
      final (inexact, j) = sys.best(room) ?? (throw const Over());
      if (inexact && !dark) {
        // An empty real shadow, over the rationals, shows the problem empty; a point of the
        // dark shadow, which lies within the real one, is a point of it. Between them the
        // question is undecided: the splinters that would settle it recurse once per value of
        // a coefficient at each variable, which is exponential in the variables.
        if (_relaxedEmpty(sys.rows.values)) return null;
        dark = true;
      }
      steps.add(_Chosen(j, sys.eliminate(j, inexact)));
    }
    final m = <int, BigInt>{};
    for (final s in steps.reversed) {
      m[s.j] = switch (s) {
        _Defined(:final def) => def.eval(m),
        _Chosen(:final rows) => _choose(rows, s.j, m),
      };
    }
    return m;
  }

  /// Solves the equality in slot `s`: by a unit coefficient, substituted into every row that
  /// holds its variable, or by Pugh's step with a fresh variable `t`, whose new equality has a
  /// unit coefficient at the variable with the least coefficient, the first on a tie.
  void _equality(int s, _Equalities es, List<_Step> steps) {
    final e = es[s];
    for (final MapEntry(key: j, value: aj) in e.a.entries) {
      if (aj.abs() != BigInt.one) continue;
      // `aj·x + rest == 0`, so `x = -aj·rest`.
      final rest = e.rest(j);
      final def = _Row(
        SplayTreeMap.of(rest.a.map((i, c) => MapEntry(i, -aj * c))),
        -aj * rest.k,
        true,
      );
      es.clear(s);
      steps.add(_Defined(j, def));
      for (final r in es.sys.take(j)) {
        es.sys.add(r.subst(j, def));
      }
      es.subst(j, def);
      return;
    }
    var least = e.a.values.first;
    for (final c in e.a.values) {
      if (c.abs() < least.abs()) least = c;
    }
    final m = least.abs() + BigInt.one;
    final t = next++;
    final a = SplayTreeMap<int, BigInt>();
    e.a.forEach((i, c) {
      final h = _modHat(c, m);
      if (h != BigInt.zero) a[i] = h;
    });
    a[t] = -m;
    es.push(_Row(a, _modHat(e.k, m), true));
  }
}

int _compareGrowth((int, int) x, (int, int) y) => x.$1 != y.$1 ? x.$1 - y.$1 : x.$2 - y.$2;

/// The shadow row of the lower bound `lo` and the upper bound `hi` on `x[j]`: the real shadow,
/// or the dark one when `dark`.
_Row _combine(_Row lo, _Row hi, int j, bool dark) {
  final (a, b) = (lo.a[j]!, -hi.a[j]!);
  final out = SplayTreeMap<int, BigInt>();
  var k = BigInt.zero;
  for (final (src, f) in [(hi, a), (lo, b)]) {
    src.a.forEach((i, c) {
      if (i != j) _addTo(out, i, c * f);
    });
    k += src.k * f;
  }
  if (dark) k -= (a - BigInt.one) * (b - BigInt.one);
  return _Row(out, k, false);
}

/// Whether the inequalities have no rational point, by Fourier–Motzkin elimination with the
/// real shadow alone, each row normalized (which keeps every integer point). A false is "not
/// shown": a variable whose elimination would leave more rows than `gs` holds stops it. Each
/// step eliminates the variable of least growth, the first on a tie.
bool _relaxedEmpty(Iterable<_Row> gs) {
  final sys = _System(gs);
  final room = sys.rows.length;
  while (!sys.empty) {
    final (e, i) = (sys.exact.firstOrNull, sys.inexact.firstOrNull);
    final least = e == null || i != null && _compareGrowth(i, e) < 0 ? i : e;
    if (least == null) return false;
    final (growth, j) = least;
    if (sys.rows.length + growth > room) return false;
    sys.eliminate(j, false);
  }
  return true;
}

/// The value nearest zero for `x[j]` that the rows allow at the values `m` of the others.
BigInt _choose(List<_Row> rows, int j, _Vals m) {
  BigInt? lo, hi;
  for (final r in rows) {
    final c = r.a[j]!;
    final rest = r.rest(j).eval(m);
    // `c·x + rest >= 0`.
    if (c > BigInt.zero) {
      final b = _divEuclid(-rest, c) + ((-rest) % c != BigInt.zero ? BigInt.one : BigInt.zero);
      lo = lo == null || b > lo ? b : lo;
    } else {
      final b = _divEuclid(rest, -c);
      hi = hi == null || b < hi ? b : hi;
    }
  }
  if (lo != null && lo > BigInt.zero) return lo;
  if (hi != null && hi < BigInt.zero) return hi;
  return BigInt.zero;
}

/// The values of a symbol over the formula's points, as a union of intervals (see the library
/// note): exact when one disjunction is left, a set holding them otherwise. A bound past the
/// 64-bit integers is read as no bound. Throws [Over] when undecided.
IntervalSet project(Formula f, Atom sym) => projectEach(f, [sym])[0] ?? (throw const Over());

/// [project] onto each of `syms`, removing disjuncts once: one result for each symbol, null
/// where it is undecided, so that a symbol whose hull is undecided leaves the others
/// projected. Throws [Over] when the formula's disjuncts cannot be settled.
List<IntervalSet?> projectEach(Formula f, List<Atom> syms) {
  List<IntervalSet?> none() => [for (final _ in syms) const IntervalSet.empty()];
  var p = _propagate(f);
  if (p == null) return none();
  if (p.ors.length > 1) {
    try {
      _pick(p);
    } on Over {
      p = _probe(p);
      if (p == null) return none();
    }
  }
  final model = _solve(p.cons);
  if (model == null) return none();
  final base = Formula.and([...p.cons]);
  // Each disjunct's projections with the base, a level of disjunctions fewer than `f`; an
  // undecided one is null.
  final parts = [
    for (final ds in p.ors)
      [
        for (final d in ds)
          () {
            try {
              return projectEach(Formula.and([base, d]), syms);
            } on Over {
              return null;
            }
          }(),
      ],
  ];
  final many = p.ors.length > 1;
  return [
    for (var k = 0; k < syms.length; k++)
      () {
        try {
          var out = _hullFrom(base, syms[k], model);
          for (final ds in parts) {
            IntervalSet? u = const IntervalSet.empty();
            for (final d in ds) {
              final h = d?[k];
              u = u == null || h == null ? null : u.join(h);
            }
            if (u != null) out = out.meet(u);
          }
          return many ? _tighten(f, syms[k], out) : out;
        } on Over {
          return null;
        }
      }(),
  ];
}

/// `set`, holding every value of `sym` over `f`'s points, with each finite bound raised or
/// lowered by bisection to the nearest value at which `f` with `sym` past it is shown to have
/// no point. A bound moves only on such a proof, so an undecided question leaves it sound.
IntervalSet _tighten(Formula f, Atom sym, IntervalSet set) {
  if (set.bounds case (Fin(v: final lo), Fin(v: final hi))) {
    final x = Lin.atom(sym);
    bool none(Con con) => _empty(Formula.and([f, con]));
    // The least `v` in `lo..=hi` with no proof that `f` has no point where `sym <= v`, and the
    // greatest with none where `sym >= v`.
    var (a, b) = (BigInt.from(lo), BigInt.from(hi));
    while (a < b) {
      final mid = a + _divEuclid(b - a, BigInt.two);
      if (none(Con.ge(Lin.constant(mid), x))) {
        a = mid + BigInt.one;
      } else {
        b = mid;
      }
    }
    final newLo = a;
    if (none(Con.ge(Lin.constant(newLo), x))) return const IntervalSet.empty();
    (a, b) = (newLo, BigInt.from(hi));
    while (a < b) {
      final mid = b - _divEuclid(b - a, BigInt.two);
      if (none(Con.ge(x, Lin.constant(mid)))) {
        b = mid - BigInt.one;
      } else {
        a = mid;
      }
    }
    return set.meet(IntervalSet.range(End.exact(newLo), End.exact(a)));
  }
  return set;
}

/// The least and greatest values of a symbol over a conjunction.
IntervalSet _hull(Formula c, Atom sym) {
  final m = satisfiable(c);
  return m == null ? const IntervalSet.empty() : _hullFrom(c, sym, m);
}

final _minInt = BigInt.from(minInt), _maxInt = BigInt.from(maxInt);

/// [_hull] given a point `m` of the conjunction, found by the monotone questions "is there a
/// point with the symbol at most `v`" and "at least `v`". Each bound is searched outward from
/// the point's value with steps that double, then by bisection, so it takes O(log d) questions
/// for a bound at distance d, and one when the symbol is unbounded that way.
IntervalSet _hullFrom(Formula c, Atom sym, Model m) {
  final x = Lin.atom(sym);
  final at = m[sym] ?? BigInt.zero;
  bool meets(Con con) => satisfiable(Formula.and([c, con])) != null;
  bool below(BigInt v) => meets(Con.ge(Lin.constant(v), x));
  bool above(BigInt v) => meets(Con.ge(x, Lin.constant(v)));
  // The last value of the monotone `holds` that is true, moving from `start` (true) by `dir`
  // toward `end` (false).
  BigInt edge(bool Function(BigInt) holds, BigInt start, BigInt end, int dir) {
    final d = BigInt.from(dir);
    var (good, step) = (start, BigInt.one);
    BigInt bad;
    while (true) {
      final next = good + d * step;
      if ((next - end) * d >= BigInt.zero) {
        bad = end;
        break;
      }
      if (!holds(next)) {
        bad = next;
        break;
      }
      good = next;
      step *= BigInt.two;
    }
    while ((bad - good).abs() > BigInt.one) {
      final mid = good + (bad - good) ~/ BigInt.two;
      if (holds(mid)) {
        good = mid;
      } else {
        bad = mid;
      }
    }
    return good;
  }

  final lo = below(_minInt) ? negInf : End.exact(edge(below, at, _minInt, -1));
  final hi = above(_maxInt) ? posInf : End.exact(edge(above, at, _maxInt, 1));
  return IntervalSet.range(lo, hi);
}

/// The set `s` of a symbol as a formula: the disjunction of its pieces.
Formula member(Atom sym, IntervalSet s) => within(Lin.atom(sym), s);

/// The values of the term `l` in the set `s`, as a formula.
Formula within(Lin l, IntervalSet s) => Formula.or([
  for (final (lo, hi) in s.pieces)
    Formula.and([
      if (lo case Fin(:final v)) Con.ge(l, Lin.constant(BigInt.from(v))),
      if (hi case Fin(:final v)) Con.ge(Lin.constant(BigInt.from(v)), l),
    ]),
]);

/// What rung 2 concludes about an entailment.
sealed class Entailment {
  const Entailment();

  static String _model(Model m) =>
      [for (final MapEntry(:key, :value) in m.entries) '$key = $value'].join(', ');
}

/// The premises entail the goal; the certificate is the premise set, the products of the
/// factor premises included.
final class Proved extends Entailment {
  final List<Formula> premises;

  const Proved(this.premises);

  @override
  String toString() => 'proved from ${premises.join(' && ')}';
}

/// The goal fails at these values of the symbols, where the premises hold.
final class Refuted extends Entailment {
  final Model model;

  const Refuted(this.model);

  @override
  String toString() => 'refuted: countermodel ${Entailment._model(model)}';
}

/// The premises with the products, read linearly, hold at these values with the goal failing,
/// but the values of the product atoms are not the products of the symbols'.
final class NotProved extends Entailment {
  final Model model;

  const NotProved(this.model);

  @override
  String toString() => 'not proved: the linear reading fails at ${Entailment._model(model)}';
}

/// The question lies outside the fragment the test decides (see the library note).
final class Undecided extends Entailment {
  const Undecided();

  @override
  String toString() => 'undecided: outside the fragment the Omega test decides';
}

/// Whether `premises` entail `goal` (rung 2).
Entailment entails(Relation premises, Relation goal) {
  try {
    return _entails(premises, goal);
  } on Over {
    return const Undecided();
  }
}

Entailment _entails(Relation premises, Relation goal) {
  final defs = Formula.and([premises.defined, goal.defined]);
  final ps = [premises.body, ..._products(premises, goal)];
  final m = satisfiable(Formula.and([defs, Formula.and(ps), Formula.negate(goal.body)]));
  if (m == null) return Proved(ps);
  // A countermodel of the linear reading is a countermodel when the premises hold and the
  // goal fails with each product read as a product.
  final real = Formula.and([defs, premises.body, Formula.negate(goal.body)]);
  final syms = Model.of({
    for (final MapEntry(:key, :value) in m.entries)
      if (key is! Product) key: value,
  });
  if (real.holds(syms)) {
    return Refuted(
      Model.of({
        for (final MapEntry(:key, :value) in syms.entries)
          if (key is Sym) key: value,
      }),
    );
  }
  return NotProved(m);
}

/// For each product the formulas mention, the products in pairs of the premises on its two
/// factors, each `>= 0`.
List<Formula> _products(Relation premises, Relation goal) {
  final wanted = SplayTreeSet<(String, String)>((x, y) {
    final c = x.$1.compareTo(y.$1);
    return c != 0 ? c : x.$2.compareTo(y.$2);
  });
  for (final f in [premises.body, goal.body]) {
    for (final a in f.atoms) {
      if (a case Product(a: final x, b: final y)) wanted.add((x, y));
    }
  }
  if (wanted.isEmpty) return const [];
  // The top-level linear inequalities, an equality read as two.
  final linear = <Lin>[];
  for (final g in premises.body.conjuncts) {
    if (g case Con(:final lin, :final rel) when lin.isLinear) {
      linear.add(lin);
      if (rel == Rel.eq) linear.add(lin.times(BigInt.from(-1)));
    }
  }
  final base = Formula.and([
    premises.defined,
    Formula.and([for (final l in linear) Con(l, Rel.ge)]),
  ]);
  final on = <String, List<Lin>>{};
  for (final s in SplayTreeSet.of([
    for (final (x, y) in wanted) ...[x, y],
  ])) {
    final atom = Sym(s);
    final set = SplayTreeSet<Lin>.of(linear.where((l) => l.terms.containsKey(atom)));
    final x = Lin.atom(atom);
    if (_hull(base, atom).bounds case (final lo, final hi)) {
      if (lo case Fin(:final v)) set.add(x.minus(Lin.constant(BigInt.from(v))));
      if (hi case Fin(:final v)) set.add(Lin.constant(BigInt.from(v)).minus(x));
    }
    on[s] = set.toList();
  }
  final out = SplayTreeSet<Con>();
  for (final (x, y) in wanted) {
    for (final a in on[x]!) {
      for (final b in on[y]!) {
        if (a.product(b) case final p?) out.add(Con(p, Rel.ge));
      }
    }
  }
  return [...out];
}
