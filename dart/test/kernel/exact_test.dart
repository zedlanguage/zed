import 'dart:math' as math;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

const maxF64 = double.maxFinite;

void main() {
  test('the exact sum rounds once', () {
    // Left to right, 0.1 + 0.2 + 0.3 rounds twice and gives 0.6000000000000001.
    expect(0.1 + 0.2 + 0.3, 0.6000000000000001);
    expect(exactSum([0.1, 0.2, 0.3]), 0.6);
    expect(exactSum([1e100, 1.0, -1e100]), 1.0);
    expect(exactSum([1e308, 1e308, -1e308]), 1e308);
    expect(exactSum([maxF64, maxF64]), double.infinity);
    expect(exactSum([-maxF64, -maxF64]), double.negativeInfinity);
  });

  test('the exact sum matches an order-free reference', () {
    // Shuffles of one multiset give one bit pattern.
    final xs = [3.5e-310, 1e16, -1.0, 2.5, -1e16, 7e-300, 1.0 / 3.0];
    final a = exactSum(xs);
    final ys = xs.reversed.toList();
    expect(f64Bits(exactSum(ys)), f64Bits(a));
    final t = ys[1];
    ys[1] = ys[4];
    ys[4] = t;
    expect(f64Bits(exactSum(ys)), f64Bits(a));
  });

  test('ties round to even', () {
    // 2^53 + 1 is a tie between 2^53 and 2^53 + 2; the even one is 2^53.
    const two53 = 9007199254740992.0;
    expect(exactSum([two53, 1.0]), two53);
    // 2^53 + 3 is a tie between 2^53 + 2 and 2^53 + 4; the even mantissa is 2^53 + 4.
    expect(exactSum([two53, 3.0]), two53 + 4.0);
    // A tie broken by a sticky bit far below rounds up.
    expect(exactSum([two53, 1.0, 1e-300]), two53 + 2.0);
  });

  test('carries and round up into the next binade', () {
    // Three values with all-ones mantissas fill bits 0..159 of the sum; one more unit carries
    // through all of them, giving exactly 2^159 units, 2^-915.
    double ones(int biased) => f64FromBits(biased << 52 | ((1 << 52) - 1));
    final xs = [ones(1), ones(54), ones(107), f64FromBits(1)];
    expect(exactSum(xs), math.pow(2.0, -915));
    // 2^54 - 1 is a tie between 2^54 - 2, whose mantissa is odd, and 2^54.
    const two54 = 18014398509481984.0;
    expect(exactSum([two54 - 2.0, 1.0]), two54);
  });

  test('subnormals and zeros', () {
    final tiny = f64FromBits(1);
    expect(exactSum([tiny, tiny]), f64FromBits(2));
    expect(f64Bits(exactSum([tiny, -tiny])), f64Bits(0.0));
    expect(f64Bits(exactSum([-0.0, -0.0])), f64Bits(-0.0));
    expect(f64Bits(exactSum([-0.0, 0.0])), f64Bits(0.0));
    expect(f64Bits(exactSum([])), f64Bits(0.0));
    const minPositive = 2.2250738585072014e-308;
    expect(exactSum([minPositive, -tiny]), minPositive - tiny);
  });

  test('specials', () {
    expect(exactSum([1.0, double.nan]).isNaN, isTrue);
    expect(exactSum([double.infinity, double.negativeInfinity]).isNaN, isTrue);
    expect(exactSum([double.infinity, -1e308]), double.infinity);
    expect(exactSum([double.negativeInfinity, 1.0]), double.negativeInfinity);
  });

  String shape(int n) => canonicalTree([for (var i = 0; i < n; i++) 'e$i'], (a, b) => '($a ⊕ $b)');

  test('canonical tree shapes', () {
    expect(shape(1), 'e0');
    expect(shape(3), '((e0 ⊕ e1) ⊕ e2)');
    // The example of (sec:reduction).
    expect(shape(6), '(((e0 ⊕ e1) ⊕ (e2 ⊕ e3)) ⊕ (e4 ⊕ e5))');
    expect(shape(7), '((((e0 ⊕ e1) ⊕ (e2 ⊕ e3)) ⊕ (e4 ⊕ e5)) ⊕ e6)');
  });

  test('the canonical tree is floor(log n) + popcount(n) - 1 deep', () {
    for (var n = 1; n < 200; n++) {
      final depth = canonicalTree(List.filled(n, 0), (a, b) => math.max(a, b) + 1);
      final expected = n.bitLength - 1 + n.toRadixString(2).replaceAll('0', '').length - 1;
      expect(depth, expected, reason: 'n = $n');
    }
  });
}
