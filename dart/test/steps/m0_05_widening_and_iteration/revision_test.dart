/// The tonicity table, interval revision and the reductions, on constraints from ordinary
/// programs, and checked for soundness by brute force over every operand interval with
/// endpoints in a small range.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import 'harness.dart';

IntervalSet top() => IntervalSet.top();

/// The operand intervals of the brute-force checks: every interval with endpoints in -3..=3
/// or infinite, the empty set, and a two-piece union.
List<IntervalSet> operands() {
  final ends = <End>[negInf, for (var v = -3; v <= 3; v++) Fin(v), posInf];
  return [
    const IntervalSet.empty(),
    IntervalSet.of(-3, -2).join(IntervalSet.of(2, 3)),
    for (final lo in ends)
      for (final hi in ends)
        if (lo <= hi && lo != posInf && hi != negInf) IntervalSet.range(lo, hi),
  ];
}

int? apply(Op op, int x, int y) => switch (op) {
  Op.add => x + y,
  Op.sub => x - y,
  Op.neg => -x,
  Op.mul => x * y,
  Op.div => y == 0 ? null : divEuclid(x, y),
  Op.mod => y == 0 ? null : x % y,
  Op.abs => x.abs(),
  Op.min => x < y ? x : y,
  Op.max => x > y ? x : y,
  _ => [for (var i = 0; i < op.k; i++) x].fold<int>(1, (p, f) => p * f),
};

const ops = [
  Op.add,
  Op.sub,
  Op.neg,
  Op.mul,
  Op.pow(2),
  Op.pow(3),
  Op.div,
  Op.mod,
  Op.abs,
  Op.min,
  Op.max,
];

void main() {
  test('the tonicity table follows the sign of the other argument', () {
    expect(tonicity(Op.add, 1), Tonicity.up);
    expect(tonicity(Op.sub, 0), Tonicity.up);
    expect(tonicity(Op.sub, 1), Tonicity.down);
    expect(tonicity(Op.mul, 0), Tonicity.upWhereOtherNonneg);
    expect(tonicity(Op.abs, 0), Tonicity.downThenUp);
    expect(tonicity(const Op.pow(2), 0), Tonicity.downThenUp);
    expect(tonicity(const Op.pow(3), 0), Tonicity.up);
    expect(tonicity(Op.mod, 0), Tonicity.none);
    // A product whose factors straddle 0 is split at 0 and the parts' images joined:
    // (-3..=2) * (-1..=4) has extremes -3*4 and 2*4.
    expect(forward(Op.mul, IntervalSet.of(-3, 2), IntervalSet.of(-1, 4)), IntervalSet.of(-12, 8));
    // 0 times an unbounded factor is 0, not undefined.
    expect(forward(Op.mul, IntervalSet.single(0), top()), IntervalSet.single(0));
  });

  test('an order total bounds the quantity', () {
    // `total = price * qty` with prices from 10 to 20 cents and a total of at most 50: the
    // quantity is at most 5, and is unchanged where it was already smaller.
    final (price, qty) = (IntervalSet.of(10, 20), IntervalSet.of(0, 100));
    final total = forward(Op.mul, price, qty).meet(iv(null, 50));
    expect(backward(Op.mul, 1, price, qty, total), IntervalSet.of(0, 5));
    // A free price that may be 0 gives the quantity no bound.
    expect(backward(Op.mul, 1, IntervalSet.of(0, 20), qty, total), qty);
  });

  test('a minute count bounds the seconds', () {
    // `minutes = seconds div 60` with 2 or 3 minutes: 120 to 239 seconds.
    expect(
      backward(Op.div, 0, iv(0, null), IntervalSet.single(60), IntervalSet.of(2, 3)),
      IntervalSet.of(120, 239),
    );
    // `hour = t mod 24`: any hour without more, and the shifted range when t spans no wrap.
    final day = IntervalSet.single(24);
    expect(forward(Op.mod, top(), day), IntervalSet.of(0, 23));
    expect(forward(Op.mod, IntervalSet.of(25, 30), day), IntervalSet.of(1, 6));
    expect(forward(Op.mod, IntervalSet.of(20, 30), day), IntervalSet.of(0, 23));
  });

  test('a tolerance on a difference gives one or two pieces', () {
    // `abs(delta) <= 5` and `abs(delta) >= 3`.
    expect(backward(Op.abs, 0, top(), top(), IntervalSet.of(0, 5)), IntervalSet.of(-5, 5));
    expect(backward(Op.abs, 0, top(), top(), iv(3, null)).toString(), '[..=-3, 3..]');
    // `x ** 2` between 10 and 50: x is 4 to 7 in either sign.
    expect(
      backward(const Op.pow(2), 0, top(), top(), IntervalSet.of(10, 50)).toString(),
      '[-7..=-4, 4..=7]',
    );
    // `x ** 3` up to -8: x at most -2.
    expect(backward(const Op.pow(3), 0, top(), top(), iv(null, -8)), iv(null, -2));
  });

  test('a minimum bounds both arguments from below and one from above', () {
    // `min(stock, ordered) >= 3`: both are at least 3.
    final stock = IntervalSet.of(0, 50);
    expect(backward(Op.min, 0, stock, IntervalSet.of(0, 9), iv(3, null)), IntervalSet.of(3, 50));
    // `min(stock, ordered) <= 2` with at least 5 ordered: the stock is at most 2.
    expect(
      backward(Op.min, 0, stock, IntervalSet.of(5, 9), IntervalSet.of(0, 2)),
      IntervalSet.of(0, 2),
    );
    // `max(a, b) <= 10` bounds both from above.
    expect(backward(Op.max, 1, top(), top(), IntervalSet.of(0, 10)), iv(null, 10));
  });

  test('an aligned index moves its bounds to the alignment', () {
    // An index into an array of 100 that is a multiple of 4 and at least 1: 4 to 96.
    expect(reduceCongruence(IntervalSet.of(1, 99), Congruence(4, 0)).$1, IntervalSet.of(4, 96));
    // An index fixed to 8 fixes the congruence to that value.
    expect(reduceCongruence(IntervalSet.of(5, 10), Congruence(8, 0)).$2, Congruence.single(8));
    // The examples of sec:constraints: `int[0..=10]` with `1 mod 4` is `int[1..=9]`, and
    // `int[2..=4]` with `1 mod 4` is empty.
    final oneModFour = Congruence(4, 1);
    expect(reduceCongruence(IntervalSet.of(0, 10), oneModFour).$1, IntervalSet.of(1, 9));
    expect(reduceCongruence(IntervalSet.of(2, 4), oneModFour), (
      const IntervalSet.empty(),
      Congruence.bottom,
    ));
    // A status in 400..=499 out of the known codes {200, 404, 500}: just 404.
    expect(reduceFinite(IntervalSet.of(400, 499), FiniteSet.of([200, 404, 500])), (
      IntervalSet.single(404),
      FiniteSet.of([404]),
    ));
  });

  test('one round of revision never loses a solution', () {
    // For every operator, operand intervals and demanded result: a forward pass then a
    // backward pass to each operand keeps every pair of members whose result is demanded.
    // Members are taken from -9..=9, which every finite endpoint lies inside.
    final all = operands();
    var kept = 0;
    for (final op in ops) {
      for (final x in all) {
        for (final y in all) {
          for (var iz = 0; iz < all.length; iz += 4) {
            final z = all[iz].meet(forward(op, x, y));
            final x2 = backward(op, 0, x, y, z);
            final y2 = op.arity == 2 ? backward(op, 1, x2, y, z) : y;
            final ys = op.arity == 1
                ? [0]
                : [
                    for (var b = -9; b <= 9; b++)
                      if (y.contains(b)) b,
                  ];
            for (var a = -9; a <= 9; a++) {
              if (!x.contains(a)) continue;
              for (final b in ys) {
                final r = apply(op, a, b);
                if (r != null && z.contains(r)) {
                  if (!x2.contains(a) || op.arity == 2 && !y2.contains(b)) {
                    fail('$op $x $y $z: lost ($a, $b)');
                  }
                  kept++;
                }
              }
            }
          }
        }
      }
    }
    expect(kept, greaterThan(1000000), reason: 'only $kept solutions checked');
  });
}
