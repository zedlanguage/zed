/// Intervals with symbolic affine bounds, against their members at each symbol value.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';
import 'support.dart';

void main() {
  test('meet is exact, and join and widening hold both sides', () {
    final rng = Rng(0x124);
    for (var i = 0; i < randomInstances; i++) {
      final (a, b) = (randomBounds(rng), randomBounds(rng));
      final (meet, join) = (a.meet(b), a.join(b));
      final widened = a.widen(join, Landmarks.none());
      expect(join, b.join(a), reason: 'join of $a and $b is not symmetric');
      for (final env in envs) {
        final f = at(env);
        for (final x in window) {
          final (ia, ib) = (a.contains(x, f), b.contains(x, f));
          if (meet.contains(x, f) != (ia && ib)) fail('$x at $env: $a meet $b is $meet');
          if (ia || ib) {
            if (!join.contains(x, f)) fail('$x at $env: $a join $b is $join');
            if (!widened.contains(x, f)) fail('$x at $env: $a widened by $join is $widened');
          }
        }
      }
    }
  });

  test('the order is sound and holds of meets and joins', () {
    final rng = Rng(0x1240);
    var below = 0;
    for (var i = 0; i < randomInstances; i++) {
      final (a, b) = (randomBounds(rng), randomBounds(rng));
      expect(a.leq(a), isTrue, reason: '$a is not below itself');
      expect(a.leq(a.join(b)), isTrue, reason: '$a is not below its join with $b');
      expect(a.meet(b).leq(a), isTrue, reason: 'the meet of $a and $b is not below $a');
      if (a.leq(b)) {
        below++;
        for (final env in envs) {
          final mb = members(b, env).toSet();
          expect(
            members(a, env).every(mb.contains),
            isTrue,
            reason: '$a is taken as below $b, but not at $env',
          );
        }
      }
    }
    // The bottom and the tops of the random elements make the order hold sometimes.
    expect(below, greaterThan(0));
  });

  test('an offset moves every member', () {
    final rng = Rng(0x1241);
    for (var i = 0; i < randomInstances; i++) {
      final a = randomBounds(rng);
      final c = rng.int_(-5, 5);
      final moved = a.offset(c);
      for (final env in envs) {
        for (final x in window) {
          if (moved.contains(x, at(env)) != a.contains(x - c, at(env))) {
            fail('$x at $env: $a moved by $c is $moved');
          }
        }
      }
    }
  });

  test('widening chains are finite', () {
    final rng = Rng(0x1242);
    var longest = 0;
    for (var i = 0; i < randomInstances; i++) {
      var x = randomBounds(rng);
      var steps = 0;
      for (var j = 0; j < 64; j++) {
        final next = x.join(randomBounds(rng));
        final w = x.widen(next, Landmarks.none());
        if (w == x) continue;
        x = w;
        steps++;
      }
      if (steps > longest) longest = steps;
    }
    // Each step either drops a symbolic bound or moves an end of the union to infinity or
    // removes a piece, and an element has at most 9 pieces and a few bounds.
    expect(longest, lessThanOrEqualTo(24), reason: 'a widening chain took $longest steps');
  });

  test('bounds print in the type syntax', () {
    final n = Affine.sym('n');
    const zero = Affine.constant(0);
    final cases = [
      (Bounds.range(zero, n.plus(-1)), '[0..=n - 1]'),
      (Bounds.range(n, null), '[n..]'),
      (Bounds.range(null, n.times(2)), '[..=2 * n]'),
      (Bounds.range(zero, affine((1, -1), 1)), '[0..=-m + n + 1]'),
      (
        Bounds.range(Affine.sym('m'), n).meet(Bounds.ints(IntervalSet.of(0, 9))),
        '[max(0, m)..=min(9, n)]',
      ),
      (
        Bounds.fromBounds(IntervalSet.range(const Fin(0), posInf), [], [Bound(n, const Fin(0))]),
        '[0..=max(0, n)]',
      ),
      (
        Bounds(IntervalSet.fromPieces([(const Fin(0), const Fin(3)), (const Fin(5), posInf)]), [], [
          n,
        ]),
        '[0..=3, 5..] & [..=n]',
      ),
      (Bounds.ints(IntervalSet.of(2, 4)), '[2..=4]'),
    ];
    for (final (b, want) in cases) {
      expect(b.toString(), want);
    }
  });

  test('a bound crossing its opposite is empty', () {
    // `int[n..=n - 1]` has no member whatever `n` is.
    final n = Affine.sym('n');
    expect(Bounds.range(n, n.plus(-1)), Bounds.bottom);
    // `int[n..=m]` is empty only when `n > m`, so it stays.
    final c = Bounds.range(n, Affine.sym('m'));
    expect(c, isNot(Bounds.bottom));
    expect(c.bounds(Side.lower).length + c.bounds(Side.upper).length, 2);
  });

  test('a tighter bound with the same terms replaces the looser', () {
    final n = Affine.sym('n');
    final b = Bounds.range(null, n).meet(Bounds.range(null, n.plus(-2)));
    expect(b.toString(), '[..=n - 2]');
    // A bound the union already implies is dropped: `max(5, n)` when every member is at most 3.
    final c = Bounds.fromBounds(IntervalSet.of(0, 3), [], [Bound(n, const Fin(5))]);
    expect(c, Bounds.ints(IntervalSet.of(0, 3)));
  });
}
