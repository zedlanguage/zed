/// The derived forms the laws are stated over, checked on hand-computed examples before the
/// laws use them.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/check.dart';
import '../../support/kernel.dart';
import 'harness.dart';

String run(Term t) => eval(t).toString();

void main() {
  test('map applies to every value and keeps the keys', () {
    final prices = ints([(101, 250), (102, 1200), (105, 75)]);
    final doubled = map(prices, (v) => mul(v, lit(2)));
    expect(run(doubled), '{101 -> 500, 102 -> 2400, 105 -> 150}');
  });

  test('scan gives running totals', () {
    final dailySales = seq([3, 1, 4, 1]);
    final totals = scan(dailySales, const PrimFn(Prim.add));
    expect(run(totals), '{0 -> 3, 1 -> 4, 2 -> 8, 3 -> 9}');
  });

  test('foldl and foldr apply the operator in sequence', () {
    // A balance of 100 less three withdrawals, left to right.
    final withdrawals = seq([10, 3, 2]);
    const minus = PrimFn(Prim.sub);
    expect(run(foldl(withdrawals, lit(100), minus)), '85');
    // 10 - (3 - (2 - 0)), right to left.
    expect(run(foldr(withdrawals, minus, lit(0))), '9');
    final none = seq([]);
    expect(run(foldl(none, lit(100), minus)), '100');
    expect(run(foldr(none, minus, lit(7))), '7');
  });

  test('flip swaps the arguments', () {
    expect(run(app(flip(const PrimFn(Prim.sub)), [lit(3), lit(10)])), '7');
  });

  test('rank widen puts tied scores under one dense rank', () {
    final scores = family([
      for (final (n, x) in const [('ann', 90), ('bob', 85), ('cy', 90), ('dee', 70)])
        (s(n), Int(x)),
    ]);
    final ranked = rankWiden(scores, (v) => v, lt);
    expect(run(ranked), '{0 -> {"dee" -> 70}, 1 -> {"bob" -> 85}, 2 -> {"ann" -> 90, "cy" -> 90}}');
  });

  test('refine keeps passes, rejects, and lets failures through', () {
    final positive = func(1, (x) => lt(lit(0), x[0]));
    expect(outcome(refine(lit(5), positive)), const Int(5));
    expect(outcome(refine(lit(-1), positive)), const Atom('invalid'));
    // A failure in the input flows out unchanged, and `p` is never asked about it.
    expect(outcome(refine(idiv(lit(12), lit(0)), positive)), const Atom('divByZero'));
  });

  test('disjoint union merges disjoint families and rejects overlap', () {
    final morning = ints([(1, 30), (2, 45)]);
    final evening = ints([(7, 20)]);
    expect(run(disjointUnion(morning, evening, 1)), '{1 -> 30, 2 -> 45, 7 -> 20}');
    // The kernel's `Union` merges two equal leaves; `⊎` rejects them.
    final again = ints([(2, 45)]);
    expect(run(prim(Prim.union, [morning, again])), '{1 -> 30, 2 -> 45}');
    expect(outcome(disjointUnion(morning, again, 1)), isA<CollisionError>());
  });

  test('fresh names never repeat', () {
    expect(fresh('x'), isNot(fresh('x')));
  });
}
