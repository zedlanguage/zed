/// The transfer's time against the size of the term (the rule of low complexity, DESIGN.md
/// Part G): a name bound once is followed once however often it is read, and a test in guard
/// position is transferred once for each outcome.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/store.dart';

import '../../support/scaling.dart' as scaling;
import 'support.dart';

Term prim(Prim p, Term a, Term b) => PrimApp(p, [a, b]);

Term lit(int n) => Lit(Int(n));

/// `x1 = i + i; x2 = x1 + x1; …; xk >= 0`: each name read twice.
Term doubling(int k) {
  Term body = prim(Prim.ge, Var('x$k'), lit(0));
  for (var i = k; i >= 1; i--) {
    final prev = Var(i == 1 ? 'i' : 'x${i - 1}');
    body = Let('x$i', prim(Prim.add, prev, prev), body);
  }
  return body;
}

/// `f0 = (v) -> v; f1 = (v) -> max(f0(v), f0(v + d)); …; fk(i) >= 0`: each function calls
/// the one before it twice, with arguments that differ when `d` is 1 and agree when it is 0.
Term calls(int k, int d) {
  Term call(int j, Term a) => App(Var('f$j'), [a]);
  Term body = prim(Prim.ge, call(k, const Var('i')), lit(0));
  for (var j = k; j >= 0; j--) {
    const v = Var('v');
    final e = j == 0
        ? v
        : prim(Prim.max, call(j - 1, v), call(j - 1, d == 0 ? v : prim(Prim.add, v, lit(d))));
    body = Let('f$j', Lam(const ['v'], e), body);
  }
  return body;
}

Term callsApart(int k) => calls(k, 1);

Term callsAlike(int k) => calls(k, 0);

/// `if (if (… i >= 3 …) { i >= 1 } else { i <= -1 }) { i >= 0 } else { i <= 0 }`: each
/// branch's guard is the branch before it.
Term guards(int k) {
  const i = Var('i');
  Term g = prim(Prim.ge, i, lit(3));
  for (var j = 0; j < k; j++) {
    g = If(g, prim(Prim.ge, i, lit(j)), prim(Prim.le, i, lit(-j)));
  }
  return g;
}

/// `i >= 0 && i >= 1 && … && i >= k - 1`.
Term conjunction(int k) {
  const i = Var('i');
  Term a = prim(Prim.ge, i, lit(0));
  for (var j = 1; j < k; j++) {
    a = prim(Prim.and, a, prim(Prim.ge, i, lit(j)));
  }
  return a;
}

/// `x * x mod 10 == 9` with `x` in `0..=n`.
(Term, Domains) squares(int n) {
  const x = Var('x');
  final t = prim(Prim.eq, prim(Prim.mod, prim(Prim.mul, x, x), lit(10)), lit(9));
  return (t, doms([('x', 0, n)]));
}

/// `x * y mod 7 == 3` with each in `1..=n`.
(Term, Domains) products(int n) {
  final xy = prim(Prim.mul, const Var('x'), const Var('y'));
  final t = prim(Prim.eq, prim(Prim.mod, xy, lit(7)), lit(3));
  return (t, doms([('x', 1, n), ('y', 1, n)]));
}

/// `x * y <= n` with each in `1..=n`: the plain preimage is exact on every sub-box under or
/// over the curve, so only the boxes the curve crosses are split.
(Term, Domains) hyperbola(int n) {
  final t = prim(Prim.le, prim(Prim.mul, const Var('x'), const Var('y')), lit(n));
  return (t, doms([('x', 1, n), ('y', 1, n)]));
}

/// `f0 = (v) -> v; f1 = (v) -> f0(v) + f0(v + d); …; fk(i) - j >= 0`: a sum, which the catalog
/// does not invert exactly with two inputs, so the linear-relation translation reads it.
Term sumsOfCalls(int k, int d) {
  Term call(int n, Term a) => App(Var('f$n'), [a]);
  Term body = prim(Prim.ge, prim(Prim.sub, call(k, const Var('i')), const Var('j')), lit(0));
  for (var n = k; n >= 0; n--) {
    const v = Var('v');
    final e = n == 0
        ? v
        : prim(Prim.add, call(n - 1, v), call(n - 1, d == 0 ? v : prim(Prim.add, v, lit(d))));
    body = Let('f$n', Lam(const ['v'], e), body);
  }
  return body;
}

void main() {
  final ds = doms([('i', -50, 50)]);
  const yes = BoolDemand(true);

  const sums = 'i [0..=50]; exact';

  test('preimages within the depth are exact', () {
    for (final (t, want) in [
      (doubling(6), sums),
      (guards(6), 'i [5..=50]; exact'),
      (conjunction(6), 'i [5..=50]; exact'),
    ]) {
      expect(shown(preimage(t, ds, yes)), want, reason: '$t');
    }
  });

  test('the transfer scales', () {
    void Function(int) run(Term Function(int) make) =>
        (k) => preimage(make(k), ds, yes);
    scaling.check('a chain of `let`s, each name read twice', 6, run(doubling));
    scaling.check('branches nested in guard position', 6, run(guards));
    scaling.check('a conjunction of tests', 8, run(conjunction));
    scaling.check('functions each calling the one before twice, alike', 6, run(callsAlike));
    scaling.check('functions each calling the one before twice, apart', 6, run(callsApart));
  });

  // A function is summarized once for each abstraction of its arguments, so a chain of
  // functions each calling the one before twice is read in time linear in its length, not
  // exponential; and the preimage is still exact.
  test('nested calls are summarized', () {
    for (final k in const [1, 2, 5, 20, 48]) {
      expect(shown(preimage(callsAlike(k), ds, yes)), 'i [0..=50]; exact', reason: '$k alike');
      final lo = -(k < 50 ? k : 50);
      expect(shown(preimage(callsApart(k), ds, yes)), 'i [$lo..=50]; exact', reason: '$k apart');
    }
  });

  // A chain of `let`s is followed to the end and memoized, never cut. An old count of nested
  // terms cut every chain of 22 or more and fell back on enumeration.
  test('a long chain of lets is not cut', () {
    for (var k = 1; k <= 64; k++) {
      expect(shown(preimage(doubling(k), ds, yes)), sums, reason: '$k `let`s');
    }
  });

  // Under `@exact` the search visits fewer than twice as many boxes as there are points in
  // the domain, each in time of the size of the term, so its time is of the order of the
  // number of points: `n` for one input in `0..=n`, `n^2` for two; and where the plain
  // preimage is exact on sub-boxes, of the boxes the boundary crosses: `n` for `x * y <= n`.
  test('the exact search scales with the number of points', () {
    void Function(int) run((Term, Domains) Function(int) make) => (n) {
      final (t, d) = make(n);
      exactPreimage(t, d, {}, yes);
    };
    scaling.check('`x * x mod 10 == 9` over `0..=n` under `@exact`', 256, run(squares));
    scaling.checkOrder(
      '`x * y mod 7 == 3` over `1..=n` squared under `@exact`',
      16,
      2,
      run(products),
    );
    scaling.check('`x * y <= n` over `1..=n` squared under `@exact`', 64, run(hyperbola));
  });

  test('the linear translation of calls scales', () {
    final ds = doms([('i', 0, 50), ('j', -50, 50)]);
    for (final d in const [0, 1]) {
      scaling.check(
        'sums of calls, each calling the one before twice',
        6,
        (k) => preimage(sumsOfCalls(k, d), ds, yes),
      );
    }
  });
}
