/// The random terms over `x` and `y` that the linear-relation domain states, and the checks of
/// the translation, the Omega test, the projection and entailment against the interpreter at
/// every point of a window. Each check returns null when it passes, else what failed.
library;

import 'package:zed/kernel.dart' hide Atom;
import 'package:zed/presburger.dart';
import 'package:zed/store.dart' show IntervalSet;

import '../../support/instances.dart';
import 'support.dart';

/// The window every check runs over.
const lo = -5;
const hi = 5;

/// A random integer term over `x` and `y` that the domain states, of depth at most `d`.
Term intTerm(Rng rng, int d) {
  if (d == 0 || rng.below(3) == 0) {
    return switch (rng.below(5)) {
      0 || 1 => const Var('x'),
      2 || 3 => const Var('y'),
      _ => lit(rng.int_(-6, 6)),
    };
  }
  Term sub() => intTerm(rng, d - 1);
  Term nonzero() {
    final c = rng.int_(1, 5);
    return lit(rng.below(3) == 0 ? -c : c);
  }

  return switch (rng.below(11)) {
    0 || 1 => PrimApp(Prim.add, [sub(), sub()]),
    2 => PrimApp(Prim.sub, [sub(), sub()]),
    3 => PrimApp(Prim.mul, [lit(rng.int_(-3, 3)), sub()]),
    4 => PrimApp(Prim.intDiv, [sub(), nonzero()]),
    5 => PrimApp(Prim.mod, [sub(), nonzero()]),
    6 => PrimApp(Prim.neg, [sub()]),
    7 => PrimApp(Prim.abs, [sub()]),
    8 => PrimApp(rng.pick([Prim.min, Prim.max]), [sub(), sub()]),
    _ => If(boolTerm(rng, d - 1), sub(), sub()),
  };
}

/// A random test over `x` and `y` that the domain states, of depth at most `d`.
Term boolTerm(Rng rng, int d) {
  Term cmp() {
    final p = rng.pick([Prim.lt, Prim.le, Prim.gt, Prim.ge, Prim.eq, Prim.ne]);
    return PrimApp(p, [intTerm(rng, d), intTerm(rng, d)]);
  }

  if (d == 0 || rng.below(2) == 0) return cmp();
  Term sub() => boolTerm(rng, d - 1);
  return switch (rng.below(4)) {
    0 => PrimApp(Prim.not, [sub()]),
    1 => PrimApp(Prim.and, [sub(), sub()]),
    2 => PrimApp(Prim.or, [sub(), sub()]),
    _ => If(sub(), sub(), sub()),
  };
}

const names = ['x', 'y'];

/// The window as a formula over `names`.
Formula boxed(List<String> names) =>
    Formula.and([for (final n in names) member(Sym(n), IntervalSet.of(lo, hi))]);

/// The relation's points as a formula: its definitions, its body, and the window.
Formula whole(Relation r, List<String> names) => Formula.and([r.defined, r.body, boxed(names)]);

/// The relation holds at each point of the window exactly where `t` does.
String? checkPoints(Relation r, Term t, List<String> names) {
  for (final p in window(names.length, lo, hi)) {
    final at = Formula.and([
      for (var i = 0; i < names.length; i++)
        Con.eq(Lin.atom(Sym(names[i])), Lin.constant(BigInt.from(p[i]))),
    ]);
    final Model? sat;
    try {
      sat = satisfiable(Formula.and([r.defined, r.body, at]));
    } on Over {
      return '$t: undecided at $p';
    }
    if ((sat != null) != holds(t, names, p)) {
      return '$t at $p: the interpreter gives ${holds(t, names, p)}, and the relation $r '
          '${sat != null ? 'holds' : 'fails'}';
    }
  }
  return null;
}

/// The Omega test finds a point of the window exactly when `t` holds at one, and the point it
/// finds is one.
String? checkModel(List<int>? found, Term t, List<String> names) {
  final any = window(names.length, lo, hi).where((p) => holds(t, names, p)).firstOrNull;
  if (found != null) {
    return found.every((v) => lo <= v && v <= hi) && holds(t, names, found)
        ? null
        : '$t: the model $found is no point of it in the window';
  }
  return any == null ? null : '$t: unsatisfiable, but it holds at $any';
}

/// Each claimed projection holds every value the points of `t` take, within their hull.
String? checkProjection(List<IntervalSet> claimed, Term t, List<String> names) {
  final points = window(names.length, lo, hi).where((p) => holds(t, names, p)).toList();
  final wants = projections(points, names.length);
  for (var i = 0; i < names.length; i++) {
    final (c, want) = (claimed[i], wants[i]);
    final hull = want.hull();
    if (!want.isSubset(c) || !c.isSubset(hull)) {
      return '$t: `${names[i]}` takes $want, and the projection is $c';
    }
  }
  return null;
}

/// No point of the window refutes a proved entailment from `p` to `g`, and a countermodel is
/// one.
String? checkEntailment(Entailment e, Term p, Term g, List<String> names) {
  final counter = window(
    names.length,
    lo,
    hi,
  ).where((q) => holds(p, names, q) && !holds(g, names, q)).firstOrNull;
  return switch (e) {
    Proved() when counter != null => '$p to $g: proved, but $counter refutes it',
    Proved() => null,
    Refuted(:final model) => switch (point(model, names)) {
      final q when holds(p, names, q) && !holds(g, names, q) => null,
      final q => '$p to $g: the countermodel $q is none',
    },
    NotProved() || Undecided() => '$p to $g: $e, which a linear question never gives',
  };
}

/// The window as a test over `names`.
Term windowTerm(List<String> names) => [
  for (final n in names)
    PrimApp(Prim.and, [
      PrimApp(Prim.le, [lit(lo), Var(n)]),
      PrimApp(Prim.le, [Var(n), lit(hi)]),
    ]),
].reduce((a, b) => PrimApp(Prim.and, [a, b]));
