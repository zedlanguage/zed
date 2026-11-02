/// The reduced product's time against the size of the test (the rule of low complexity,
/// DESIGN.md Part G): a conjunction of disjunctions narrows a scope in time near linear in
/// its length, and a chain of `let`s and a nest of `if`s yield their arms in time near linear
/// in their depth. Each term is built before it is timed.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart' hide Lattice;
import 'package:zed/store.dart';

import '../../support/instances.dart';
import '../../support/scaling.dart' as scaling;
import 'support.dart';

Term bin(Prim p, Term a, Term b) => prim(p, [a, b]);

/// `(x + y >= 0 || x - y >= 0) && (x + y >= 1 || x - y >= 1) && …`, `k` disjunctions.
Term clauses(int k) {
  Term clause(int j) => bin(
    Prim.or,
    bin(Prim.ge, bin(Prim.add, const Var('x'), const Var('y')), lit(j)),
    bin(Prim.ge, bin(Prim.sub, const Var('x'), const Var('y')), lit(j)),
  );
  var t = clause(0);
  for (var j = 1; j < k; j++) {
    t = bin(Prim.and, t, clause(j));
  }
  return t;
}

/// `let x1 = x0 + 1 in … let xk = x(k-1) + 1 in if xk >= 0 { 1 } else { 2 }`.
Term lets(int k) {
  Term t = If(bin(Prim.ge, Var('x$k'), lit(0)), lit(1), lit(2));
  for (var i = k; i >= 1; i--) {
    t = Let('x$i', bin(Prim.add, Var('x${i - 1}'), lit(1)), t);
  }
  return t;
}

/// `if x0 >= 0 { if x0 >= 1 { … } else { 0 } } else { 0 }`, `k` deep.
Term ifs(int k) {
  var t = lit(1);
  for (var i = k - 1; i >= 0; i--) {
    t = If(bin(Prim.ge, const Var('x0'), lit(i)), t, lit(0));
  }
  return t;
}

/// `(x1 == 0 && … && xk == 0) || (x1 == 1 && … && xk == 1)`.
Term allZeroOrAllOne(int k) {
  Term all(int v) {
    var t = bin(Prim.eq, const Var('x1'), lit(v));
    for (var i = 2; i <= k; i++) {
      t = bin(Prim.and, t, bin(Prim.eq, Var('x$i'), lit(v)));
    }
    return t;
  }

  return bin(Prim.or, all(0), all(1));
}

/// A random conjunction over `x1`..`x5`: bounds, differences and sums of two names, and
/// disjunctions of two of these, so that the blocks form chains, trees and cycles.
Term randomConjunction(Rng rnd) {
  Term name() => Var('x${rnd.int_(1, 5)}');
  Term atom() {
    final rel = rnd.pick([Prim.lt, Prim.le, Prim.eq]);
    final a = name(), b = name();
    return switch (rnd.below(3)) {
      0 => bin(rel, a, lit(rnd.int_(-3, 3))),
      1 => bin(rel, a, bin(Prim.add, b, lit(rnd.int_(-2, 2)))),
      _ => bin(rel, bin(Prim.add, a, b), lit(rnd.int_(-4, 4))),
    };
  }

  Term conjunct() => rnd.below(3) == 0 ? bin(Prim.or, atom(), atom()) : atom();
  final n = rnd.int_(2, 7);
  var t = conjunct();
  for (var i = 1; i < n; i++) {
    t = bin(Prim.and, t, conjunct());
  }
  return t;
}

/// Times `run` on the terms of [make] at `n` and `8n`, built first.
void scales(String what, int n, Term Function(int) make, void Function(Term) run) {
  final inputs = {n: make(n), scaling.factor * n: make(scaling.factor * n)};
  scaling.check(what, n, (m) => run(inputs[m]!));
}

void main() {
  test('a scope keeps every clause of a relation', () {
    final s = ints(['x', 'y']);
    for (final k in [1, 4, 40]) {
      final r = s.assume(clauses(k), true, none);
      final n = r.relation.cons.length;
      expect(n, 3 * k, reason: '$k clauses: $n constraints in ${r.relation}');
      // Every point that meets the test is in the scope.
      for (final (x, y) in [(40, 0), (0, -40), (39, 0)]) {
        var holds = true;
        for (var j = 0; j < k; j++) {
          holds &= x + y >= j || x - y >= j;
        }
        expect(
          !holds || r.contains({'x': Int(x), 'y': Int(y)}),
          isTrue,
          reason: '$k clauses: ($x, $y) left out',
        );
      }
    }
  });

  test('narrowing by a conjunction of disjunctions scales', () {
    final s = ints(['x', 'y']);
    scales(
      'a conjunction of disjunctions of linear tests',
      32,
      clauses,
      (t) => s.assume(t, true, none),
    );
  });

  test('a chain of lets scales', () {
    final x0 = ints(['x0']);
    scales('a chain of `let`s', 50, lets, (t) => arms(t, x0));
  });

  test('a nest of ifs scales', () {
    // Each level's test implies the one before, so the relation keeps one constraint.
    final x0 = ints(['x0']);
    scales('`if`s nested on one name', 64, ifs, (t) => arms(t, x0));
  });

  test('a nest of ifs and a chain of lets 16384 deep yield their arms', () {
    // The walk keeps its own stack, so the depth is not bounded by the VM's.
    final x0 = ints(['x0']);
    expect(arms(ifs(16384), x0), hasLength(2 * 16384));
    expect(arms(lets(16384), x0), hasLength(2));
  });

  /// `if x >= 0 { let x = x - 100 in if x >= 0 { 1 } else { 2 } } else { 3 }`: the inner `x`
  /// is the outer one less 100, so the inner false arm is reached at `x = -100`. What held of
  /// the outer `x` does not hold of the inner one.
  test('a binding forgets what held of the name it shadows', () {
    Term test() => bin(Prim.ge, const Var('x'), lit(0));
    final inner = If(test(), lit(1), lit(2));
    final body = Let('x', bin(Prim.sub, const Var('x'), lit(100)), inner);
    final a = arms(If(test(), body, lit(3)), ints(['x']));
    final shown = [for (final a in a) '${a.guard} ${a.outcome}: ${a.scope}'].join('\n');
    expect(a, hasLength(4), reason: shown);
    final reached = a[2];
    expect(reached.outcome, isFalse, reason: shown);
    expect(reached.scope.bottom, isFalse, reason: shown);
    expect(reached.scope.contains({'x': const Int(-100)}), isTrue, reason: shown);
  });
  test('a join keeps the equalities of its sides and scales', () {
    List<String> names(int k) => [for (var i = 1; i <= k; i++) 'x$i'];
    for (final k in [2, 5, 10, 20]) {
      final r = ints(names(k)).assume(allZeroOrAllOne(k), true, none);
      final differ = bin(Prim.ne, const Var('x1'), Var('x$k'));
      expect(r.assume(differ, true, none).bottom, isTrue, reason: 'k = $k: ${r.relation}');
      final x1 = bin(Prim.eq, const Var('x1'), lit(1));
      expect(r.assume(x1, true, none).bottom, isFalse, reason: 'k = $k');
    }
    // The two sides, built before the timing; the join of the two, reduced, is timed.
    (Scope, Scope) sides(int k) {
      final s = ints(names(k));
      final [a, b] = (allZeroOrAllOne(k) as PrimApp).args;
      return (s.assume(a, true, none), s.assume(b, true, none));
    }

    final built = {
      for (final k in [8, 32, 64, 256]) k: sides(k),
    };
    scaling.check('the join of two sides that fix k names, reduced', 32, (k) {
      final (l, r) = built[k]!;
      l.join(r).reduce();
    });
    expect(
      () => scaling.check('the join reduced as a whole', 8, (k) {
        final (l, r) = built[k]!;
        l.join(r).reduceWhole();
      }),
      throwsStateError,
      reason: 'the check passed a join reduced as a whole',
    );
  });

  test('projecting by blocks keeps what projecting whole trees keeps', () {
    final names = [for (var i = 1; i <= 5; i++) 'x$i'];
    final s = ints(names);
    final rnd = Rng(39);
    var empty = 0;
    for (var i = 0; i < randomInstances; i++) {
      final t = randomConjunction(rnd);
      final a = s.assume(t, true, none);
      final blocks = a.copy()..reduce();
      final whole = a.copy()..reduceWhole();
      expect(blocks.bottom, whole.bottom, reason: '$t');
      if (blocks.bottom) {
        empty++;
        continue;
      }
      for (final x in names) {
        expect(blocks.get(x), whole.get(x), reason: '$x in $t');
      }
    }
    // Both kinds of case occur.
    expect(0 < empty && empty < randomInstances, isTrue, reason: '$empty empty');
  });

  test('a cycle of strict orders is empty', () {
    // x < y and y < x: each bound raises the other without end unless the cycle is seen.
    final s = ints(['x', 'y']);
    final t = bin(
      Prim.and,
      bin(Prim.lt, const Var('x'), const Var('y')),
      bin(Prim.lt, const Var('y'), const Var('x')),
    );
    final a = s.assume(t, true, none)..reduce();
    expect(a.bottom, isTrue, reason: '$a');
  });

  test('an even number that is odd is empty', () {
    // c == 2a, c == 2b + 1, c >= 0: no bound is ever tight, only the parity is.
    final s = ints(['a', 'b', 'c']);
    Term two(String x) => bin(Prim.mul, lit(2), Var(x));
    final t = bin(
      Prim.and,
      bin(
        Prim.and,
        bin(Prim.eq, const Var('c'), two('a')),
        bin(Prim.eq, const Var('c'), bin(Prim.add, two('b'), lit(1))),
      ),
      bin(Prim.le, lit(0), const Var('c')),
    );
    final a = s.assume(t, true, none)..reduce();
    expect(a.bottom, isTrue, reason: '$a');
  });
}
