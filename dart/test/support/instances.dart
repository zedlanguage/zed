/// Instances for the finite-model harness (step M0.10) and the steps that reuse it: exhaustive
/// enumerations in shortlex order, cut to the bounds below, and seeded random instances beyond
/// them. The bounds are the harness's sample sizes, not a rule of Zed: the compiler has no
/// enumeration budget or bounded-model instance.
library;

import 'package:zed/kernel.dart';

/// The integers each integer binder ranges over, `-8..=8`.
const bmcIntLo = -8, bmcIntHi = 8;

/// The floats each float binder ranges over: both zeros, which compare equal under IEEE `==`
/// but are different values, the three decimals whose sum shows double rounding, both
/// infinities, and a NaN.
const bmcFloats = [
  0.0,
  -0.0,
  1.0,
  0.1,
  0.2,
  0.3,
  double.infinity,
  double.negativeInfinity,
  double.nan,
];

/// The most exhaustive instances one law runs.
const enumerationBudget = 4096;

/// How many seeded random instances each law runs beyond its exhaustive ones.
const randomInstances = 512;

/// A SplitMix64 generator, so that every random instance is reproducible from its seed.
final class Rng {
  int _state;

  /// A generator from `seed`.
  Rng(this._state);

  /// The next 64 random bits, as a two's-complement `int`.
  int nextU64() {
    _state += 0x9e3779b97f4a7c15;
    var z = _state;
    z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9;
    z = (z ^ (z >>> 27)) * 0x94d049bb133111eb;
    return z ^ (z >>> 31);
  }

  /// A number in `0..n`: the next 64 bits, read as unsigned, modulo `n`.
  int below(int n) {
    final u = nextU64();
    return ((u >>> 1) % n * 2 + (u & 1)) % n;
  }

  /// A number in `lo..=hi`.
  int int_(int lo, int hi) => lo + below(hi - lo + 1);

  /// One element of `xs`.
  T pick<T>(List<T> xs) => xs[below(xs.length)];

  /// A sequence of at most `maxLen` elements of `alphabet`, its length uniform.
  List<T> seq<T>(List<T> alphabet, int maxLen) => [
    for (var i = below(maxLen + 1); i > 0; i--) pick(alphabet),
  ];
}

/// The integers of the instance, `-8..=8`.
List<int> bmcInts() => [for (var i = bmcIntLo; i <= bmcIntHi; i++) i];

/// The floats of the instance, as values.
List<Value> bmcFloatValues() => [for (final x in bmcFloats) Float(x)];

/// Every sequence of at most `maxLen` elements of `alphabet`, in shortlex order: by length,
/// then lexicographically in the alphabet's order.
List<List<T>> shortlex<T>(List<T> alphabet, int maxLen) {
  final out = <List<T>>[[]];
  var level = <List<T>>[[]];
  for (var i = 0; i < maxLen; i++) {
    level = [
      for (final prefix in level)
        for (final a in alphabet) [...prefix, a],
    ];
    out.addAll(level);
  }
  return out;
}

/// Every partial map from `keys` to `alphabet`: each key absent or bound to one element.
List<List<(int, T)>> partialMaps<T>(List<int> keys, List<T> alphabet) {
  var out = <List<(int, T)>>[[]];
  for (final k in keys) {
    out = [
      for (final m in out) ...[
        m,
        for (final a in alphabet) [...m, (k, a)],
      ],
    ];
  }
  return out;
}

/// The sequence `xs` as a family `0..n -> x`.
Value seqValue(List<Object> xs) =>
    Family.of([for (var i = 0; i < xs.length; i++) (Int(i), valueOf(xs[i]))]);

/// The partial map `m` as a one-level family.
Value mapValue(List<(int, Object)> m) => Family.of([for (final (k, v) in m) (Int(k), valueOf(v))]);
