/// The interval-union operations at the rule of low complexity (DESIGN.md Part G): `cap`
/// merges neighbors by a heap rather than by a scan per merge, `join` merges two sorted lists,
/// `contains` searches, and the forward transfer does work linear in its operands and gives
/// no sign region more pieces than an operand has in one, so piece counts do not multiply
/// along a chain of operators. No constant bounds the pieces.
library;

import 'dart:math' as math;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';
import '../../support/scaling.dart' as scaling;

/// `n` pieces with random gaps, the outer ones infinite when `open`.
IntervalSet pieces(Rng rng, int n, bool open) {
  var at = 0;
  final out = <Piece>[];
  for (var i = 0; i < n; i++) {
    final lo = at + rng.int_(2, 9);
    final hi = lo + rng.int_(0, 5);
    out.add((Fin(lo), Fin(hi)));
    at = hi;
  }
  if (open && n > 0) {
    out[0] = (negInf, out[0].$2);
    out[n - 1] = (out[n - 1].$1, posInf);
  }
  return IntervalSet.fromPieces(out);
}

/// The rule `cap` must follow, as step M0.5 states it: while there are too many pieces, merge
/// the two neighbors with the fewest integers between them, the lower pair on a tie.
IntervalSet capByRule(IntervalSet s, int limit) {
  final p = [...s.pieces];
  int gap(int i) => switch ((p[i].$2, p[i + 1].$1)) {
    (Fin(v: final hi), Fin(v: final lo)) => lo - hi,
    _ => throw StateError('an inner end is infinite'),
  };
  while (p.length > math.max(limit, 1)) {
    var at = 0;
    for (var i = 1; i < p.length - 1; i++) {
      if (gap(i) < gap(at)) at = i;
    }
    p[at] = (p[at].$1, p[at + 1].$2);
    p.removeAt(at + 1);
  }
  return IntervalSet.fromPieces(p);
}

/// Eight single integers far apart, so that a sum of two has up to 64 distinct members.
IntervalSet sparse(Rng rng) {
  var at = 0;
  return IntervalSet.fromPieces([
    for (var i = 0; i < 8; i++) (Fin(at += rng.int_(1000, 1000000)), Fin(at)),
  ]);
}

/// A sum of `k` operands of eight sparse pieces each, the way a chain of `+` builds one: each
/// image keeps to its operands' eight pieces, so the chain's cost is linear in `k`.
IntervalSet sumChain(int k) {
  final rng = Rng(k);
  var acc = sparse(rng);
  for (var i = 0; i < k; i++) {
    acc = forward(Op.add, acc, sparse(rng));
    expect(acc.pieces.length, lessThanOrEqualTo(8), reason: '$acc');
  }
  return acc;
}

/// The pieces of `s` in each sign region: negative, zero, positive.
List<int> perRegion(IntervalSet s) {
  final n = [0, 0, 0];
  for (final (lo, hi) in s.signParts()) {
    n[hi.compareTo(const Fin(0)) < 0
            ? 0
            : lo.compareTo(const Fin(0)) > 0
            ? 2
            : 1] +=
        1;
  }
  return n;
}

/// Up to six pieces within `-40..=40`.
IntervalSet small(Rng rng) {
  final n = rng.int_(1, 6);
  return IntervalSet.fromPieces([
    for (var i = 0; i < n; i++)
      () {
        final lo = rng.int_(-40, 40);
        return (Fin(lo), Fin(lo + rng.int_(0, 4)));
      }(),
  ]);
}

const ops = [Op.add, Op.sub, Op.mul, Op.div, Op.min, Op.max];

int? apply(Op op, int a, int b) => switch (op) {
  Op.add => a + b,
  Op.sub => a - b,
  Op.mul => a * b,
  Op.div when b == 0 => null,
  // Euclidean division: `%` in Dart is never negative.
  Op.div => (a - a % b) ~/ b,
  Op.min => math.min(a, b),
  _ => math.max(a, b),
};

/// `k` lower and `k` upper bounds, each on a symbol of its own and each with a floor.
Bounds many(int k, int shift) {
  List<Bound> side(int c, End floor) => [
    for (var i = 0; i < k; i++) Bound(Affine.sym('s$i').plus(c)!, floor),
  ];
  return Bounds.fromBounds(
    IntervalSet.top(),
    side(shift, const Fin(-1)),
    side(shift + 10, const Fin(1)),
  );
}

void main() {
  test('cap follows the merge rule', () {
    final rng = Rng(24);
    var tried = 0;
    for (var i = 0; i < 2000; i++) {
      final n = rng.below(30);
      final s = pieces(rng, n, rng.below(2) == 0);
      final limit = rng.below(12);
      expect(s.cap(limit), capByRule(s, limit), reason: '$s capped to $limit');
      tried++;
    }
    expect(tried, 2000);
  });

  test('join and contains agree with membership', () {
    final rng = Rng(7);
    for (var i = 0; i < 500; i++) {
      final (n, m) = (rng.below(12), rng.below(12));
      final a = pieces(rng, n, false);
      final b = pieces(rng, m, false);
      final j = a.join(b);
      for (var v = -2; v <= 120; v++) {
        if (j.contains(v) != (a.contains(v) || b.contains(v))) fail('$a ∪ $b at $v');
      }
      expect(j, IntervalSet.fromPieces([...a.pieces, ...b.pieces]));
    }
  });

  test('a chain of operators keeps to its operands\' pieces', () {
    // Each step's image contains every sum of members, so the members are kept.
    final a = IntervalSet.fromPieces([
      (const Fin(0), const Fin(0)),
      (const Fin(10), const Fin(10)),
    ]);
    var acc = a;
    for (var i = 0; i < 6; i++) {
      acc = forward(Op.add, acc, a);
    }
    for (var v = 0; v <= 70; v += 10) {
      expect(acc.contains(v), isTrue, reason: '$acc has $v');
    }
    expect(acc.pieces.length, lessThanOrEqualTo(2), reason: '$acc');
    scaling.check('a chain of `+` over eight-piece operands', 200, sumChain);
  });

  test('an image holds every result and keeps to the most pieces of a region', () {
    final rng = Rng(325);
    var checked = 0;
    for (var i = 0; i < 600; i++) {
      final a = small(rng);
      final b = small(rng);
      for (final op in ops) {
        final z = forward(op, a, b);
        for (var x = -44; x <= 44; x++) {
          if (!a.contains(x)) continue;
          for (var y = -44; y <= 44; y++) {
            if (!b.contains(y)) continue;
            if (apply(op, x, y) case final r?) {
              if (!z.contains(r)) fail('$op $a $b: $x, $y gives $r, not in $z');
              checked++;
            }
          }
        }
        final most = [...perRegion(a), ...perRegion(b)].reduce(math.max);
        expect(perRegion(z).every((n) => n <= most), isTrue, reason: '$op $a $b gives $z');
      }
    }
    expect(checked, greaterThan(100000));
  });

  test('an image with a one-piece operand is the join of the pieces\' images', () {
    // With one operand of one piece nothing is merged before the image is taken, so when the
    // join of each piece's image keeps to the region bound, the image is that join.
    final rng = Rng(326);
    var equal = 0;
    for (var i = 0; i < 2000; i++) {
      final a = small(rng);
      final lo = rng.int_(-40, 40);
      final b = IntervalSet.range(Fin(lo), Fin(lo + rng.int_(0, 9)));
      for (final op in ops) {
        final join = a.pieces.fold(
          const IntervalSet.empty(),
          (j, p) => j.join(forward(op, IntervalSet.fromPieces([p]), b)),
        );
        final most = [...perRegion(a), ...perRegion(b)].reduce(math.max);
        if (perRegion(join).every((n) => n <= most)) {
          expect(forward(op, a, b), join, reason: '$op $a $b');
          equal++;
        }
      }
    }
    expect(equal, greaterThan(6000));
  });

  test('the interval operations scale', () {
    (IntervalSet, IntervalSet) sets(int n) {
      final rng = Rng(n);
      return (pieces(rng, n, true), pieces(rng, n, false));
    }

    scaling.check('capping n pieces to 8', 4000, (n) {
      expect(sets(n).$1.cap(8).pieces.length, math.min(8, n));
    });
    scaling.check('the forward `*` of two sets of n pieces', 4000, (n) {
      final (a, b) = sets(n);
      expect(forward(Op.mul, a, b.neg()).isEmpty, isFalse);
    });
    scaling.check('joining two sets of n pieces', 4000, (n) {
      final (a, b) = sets(n);
      expect(a.join(b).isEmpty, isFalse);
    });
    scaling.check('n membership tests in a set of n pieces', 4000, (n) {
      final b = sets(n).$2;
      var hits = 0;
      for (var v = 0; v < n; v++) {
        if (b.contains(v * 7)) hits++;
      }
      expect(hits, lessThanOrEqualTo(n));
    });
  });

  test('bounds on many symbols scale', () {
    scaling.check('symbolic bounds on distinct symbols', 200, (k) {
      final (a, b) = (many(k, 0), many(k, 1));
      expect(a.join(b).bounds(Side.lower).length, k);
      a.meet(b);
    });
  });
}
