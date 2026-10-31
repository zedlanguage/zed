/// The scaling test of the rule of low complexity (DESIGN.md Part G, "Six standing rules"): a
/// pass runs at sizes n and 8n, and the larger run may take at most `24 × 8^(k−1)` times as
/// long, where `n^k` is the order the measured work is defined to have. A run of order `n^k`
/// or `n^k log n` stays near `8^k` to `1.4 × 8^k` times, and one a power of n above it near
/// `8^(k+1)`. The test fails only when three measurements in a row are over the limit.
library;

import 'dart:math' as math;

/// How much larger the second run is.
const factor = 8;

/// The most times as long as the first the second run may take, for work of order `n`.
const ratio = 24.0;

/// How many measurements must all be over the limit before the test fails.
const tries = 3;

/// [checkOrder] for work of order `n` or `n log n`: every pass of the compiler and runtime.
void check(String what, int n, void Function(int) run) => checkOrder(what, n, 1, run);

/// Runs `run` at sizes `n` and `factor * n`, each the fastest of five runs, and throws when
/// the larger takes more than `ratio * factor^(power - 1)` times as long in each of [tries]
/// measurements. `power` is the power of n in the order the work is defined to have.
void checkOrder(String what, int n, int power, void Function(int) run) {
  Duration time(int m) {
    var best = const Duration(days: 1);
    for (var i = 0; i < 5; i++) {
      final sw = Stopwatch()..start();
      run(m);
      if (sw.elapsed < best) best = sw.elapsed;
    }
    return best;
  }

  final limit = ratio * math.pow(factor, power - 1);
  // A first run warms caches and compiles the code it runs.
  run(n);
  final seen = <String>[];
  for (var i = 0; i < tries; i++) {
    var small = time(n);
    if (small < const Duration(microseconds: 1)) small = const Duration(microseconds: 1);
    final large = time(factor * n);
    final r = large.inMicroseconds / small.inMicroseconds;
    if (r <= limit) return;
    seen.add('$small and $large, ${r.toStringAsFixed(1)} times as long');
  }
  throw StateError(
    '$what: sizes $n and ${factor * n} took ${seen.join('; then ')}; for work of order '
    'n^$power the rule of low complexity allows at most $limit times (DESIGN.md Part G)',
  );
}
