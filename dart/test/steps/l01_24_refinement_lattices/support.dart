/// Step L1.24: the refinement lattices.
///
/// The store's per-cell domains (DESIGN.md sec:domains): integer intervals with symbolic
/// affine bounds, congruences, finite sets, float classes and lengths, each held in a cell with
/// the premises it rests on. Each domain is checked against its meaning as a set: the bounds
/// and float tests compare every operation with the members it should have, the loops test
/// solves the equations of ordinary loops with the M0.5 strategy and compares the solution
/// with the values a run takes, and the cell test follows the premises through meets, joins
/// and widenings.
library;

import 'package:zed/store.dart';

import '../../support/instances.dart';

/// The symbols the tests use: a count and a second length.
const syms = ['n', 'm'];

/// The integers the oracle tries.
final window = [for (var x = -24; x <= 24; x++) x];

/// Symbol values the oracle tries: each pair in a small grid.
final envs = [
  for (final n in const [-7, -2, -1, 0, 1, 3, 8])
    for (final m in const [-7, -2, -1, 0, 1, 3, 8]) (n, m),
];

typedef Env = (int, int);

/// The function giving each symbol its value in `env`.
int Function(Sym) at(Env env) =>
    (s) => switch (s.name) {
      'n' => env.$1,
      'm' => env.$2,
      _ => throw ArgumentError('not a test symbol: $s'),
    };

/// The members of `b` in the window at `env`.
List<int> members(Bounds b, Env env) => [
  for (final x in window)
    if (b.contains(x, at(env))) x,
];

/// `k1 · n + k2 · m + c`.
Affine affine((int, int) k, int c) => Affine.of({'n': k.$1, 'm': k.$2}, c);

/// A random element: an interval union of up to two pieces, and up to two symbolic bounds on
/// each side, over `n`, `m`, `-n`, `2 * n` or `n - m`, some with a floor.
Bounds randomBounds(Rng rng) {
  if (rng.below(12) == 0) return Bounds.bottom;
  final ints = switch (rng.below(4)) {
    0 => IntervalSet.top(),
    1 => IntervalSet.range(Fin(rng.int_(-10, 4)), posInf),
    2 => IntervalSet.range(negInf, Fin(rng.int_(-4, 10))),
    _ => () {
      final lo = rng.int_(-12, 6);
      final mid = lo + rng.int_(0, 6);
      return IntervalSet.fromPieces([
        (Fin(lo), Fin(mid)),
        (Fin(mid + rng.int_(2, 4)), Fin(mid + rng.int_(4, 12))),
      ]);
    }(),
  };
  const terms = [(1, 0), (0, 1), (-1, 0), (2, 0), (1, -1)];
  // A bound has a floor one time in three, as a join with a number gives.
  List<Bound> side(End none) => [
    for (var i = rng.below(3); i > 0; i--)
      () {
        final a = affine(rng.pick(terms), rng.int_(-3, 3));
        return Bound(a, rng.below(3) == 0 ? Fin(rng.int_(-6, 6)) : none);
      }(),
  ];
  final lo = side(posInf);
  final hi = side(negInf);
  return Bounds.fromBounds(ints, lo, hi);
}
