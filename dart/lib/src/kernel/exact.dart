/// Float reductions that read no evaluation order: the exact sum and the canonical tree
/// (DESIGN.md sec:reduction).
library;

import 'value.dart' show f64Bits, f64FromBits;

/// The sum of `xs` rounded once, to nearest with ties to even, as if added in exact
/// arithmetic: so every order of the same values gives the same bits. Each finite value is
/// added as an integer count of the smallest subnormal, `2^-1074`.
double exactSum(List<double> xs) {
  var pos = BigInt.zero, neg = BigInt.zero;
  var pinf = false, ninf = false, nan = false;
  var allNegZero = xs.isNotEmpty;
  for (final x in xs) {
    if (x.isNaN) {
      nan = true;
      continue;
    }
    if (x.isInfinite) {
      if (x > 0) {
        pinf = true;
      } else {
        ninf = true;
      }
      continue;
    }
    allNegZero &= x == 0 && x.isNegative;
    final bits = f64Bits(x);
    final biased = (bits >>> 52) & 0x7ff;
    final frac = bits & ((1 << 52) - 1);
    final units = biased == 0 ? BigInt.from(frac) : BigInt.from(frac | 1 << 52) << (biased - 1);
    if (x < 0) {
      neg += units;
    } else {
      pos += units;
    }
  }
  if (nan || (pinf && ninf)) return double.nan;
  if (pinf) return double.infinity;
  if (ninf) return double.negativeInfinity;
  final c = pos.compareTo(neg);
  if (c < 0) return -_round(neg - pos);
  if (c > 0) return _round(pos - neg);
  return allNegZero ? -0.0 : 0.0;
}

/// The float nearest `acc` units of `2^-1074`, ties to even; `acc` is positive.
double _round(BigInt acc) {
  final high = acc.bitLength - 1;
  if (high < 53) {
    // Below 2^53 units the value is a subnormal or the smallest binade, exactly
    // representable, and the product by the smallest subnormal is exact.
    return acc.toInt() * f64FromBits(1);
  }
  final shift = high - 52;
  var m = (acc >> shift).toInt();
  final half = (acc >> (shift - 1)) & BigInt.one == BigInt.one;
  final sticky = acc & ((BigInt.one << (shift - 1)) - BigInt.one) != BigInt.zero;
  var exp = shift + 1;
  if (half && (sticky || m & 1 == 1)) {
    m += 1;
    if (m == 1 << 53) {
      m >>= 1;
      exp += 1;
    }
  }
  if (exp >= 2047) return double.infinity;
  return f64FromBits(exp << 52 | (m & ((1 << 52) - 1)));
}

/// The canonical tree over `n` leaves (sec:reduction) in post order: a leaf's index, or -1 to
/// combine the last two results. The left part holds all but the lowest power of two in `n`,
/// or half of `n` when `n` is one, so the tree is `floor(log n) + popcount(n) - 1` deep.
List<int> canonicalPlan(int n) {
  if (n <= 0) {
    throw ArgumentError("the canonical tree of an empty level is the empty-fold rule's business");
  }
  final plan = <int>[];
  void build(int lo, int n) {
    if (n == 1) {
      plan.add(lo);
      return;
    }
    final p = n & -n;
    final split = p == n ? n ~/ 2 : n - p;
    build(lo, split);
    build(lo + split, n - split);
    plan.add(-1);
  }

  build(0, n);
  return plan;
}

/// `xs` combined by `op` along the canonical tree.
T canonicalTree<T>(List<T> xs, T Function(T, T) op) {
  final stack = <T>[];
  for (final i in canonicalPlan(xs.length)) {
    if (i >= 0) {
      stack.add(xs[i]);
    } else {
      final b = stack.removeLast(), a = stack.removeLast();
      stack.add(op(a, b));
    }
  }
  return stack.single;
}
