/// Instances for the finite-model harness (step M0.10) and the steps that reuse it.
library;

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
