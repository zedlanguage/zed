/// The widening and the narrowing of each lattice: a value between the operands' join or meet
/// and the old value, with every chain finite, within the bound step M0.5 states for it from
/// the first value and the landmarks.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';
import 'harness.dart';

/// A random union of up to 12 intervals with endpoints in `-50..=50`.
IntervalSet randomSet(Rng rng) => IntervalSet.fromPieces([
  for (var i = rng.below(13); i > 0; i--)
    if (rng.int_(-50, 50) case final lo) (Fin(lo), Fin(lo + rng.int_(0, 6))),
]);

/// Runs `x ∇ (x ⊔ step())` from `bottom` until it is stable, returning the chain.
List<L> chain<L extends Lattice<L>>(L bottom, L Function() step, Landmarks marks, [int? limit]) {
  final out = [bottom];
  while (true) {
    final x = out.last;
    final next = x.widen(x.join(step()), marks);
    expect(x.join(next), next, reason: 'the widening is not an upper bound: $x ∇ … = $next');
    if (next == x) {
      // A few more steps confirm the chain is stable, not momentarily unchanged.
      var y = next;
      for (var i = 0; i < 8; i++) {
        y = y.widen(y.join(step()), marks);
      }
      if (y == x) return out;
      out.add(y);
    } else {
      out.add(next);
    }
    if (limit != null && out.length > limit) fail('chain longer than $limit: $out');
  }
}

/// Runs `x Δ (x ⊓ step())` from `top` until it is stable, checking that each value lies
/// between the meet and the one before; returns the chain.
List<L> descent<L extends Lattice<L>>(L top, L Function() step, Landmarks marks, [int? limit]) {
  final out = [top];
  while (true) {
    final x = out.last;
    final m = x.meet(step());
    final next = x.narrow(m, marks);
    expect(
      m.leq(next) && next.leq(x),
      isTrue,
      reason: 'the narrowing is not between: $x Δ $m = $next',
    );
    if (next == x) {
      var y = next;
      for (var i = 0; i < 8; i++) {
        y = y.narrow(y.meet(step()), marks);
      }
      if (y == x) return out;
      out.add(y);
    } else {
      out.add(next);
    }
    if (limit != null && out.length > limit) fail('descent longer than $limit: $out');
  }
}

/// Random landmarks: up to four literals in `-50..=50`.
Landmarks randomMarks(Rng rng) =>
    Landmarks.of([for (var i = rng.below(5); i > 0; i--) rng.int_(-50, 50)]);

/// The finite endpoints of `x`.
Set<int> ends(IntervalSet x) => {
  for (final (lo, hi) in x.pieces)
    for (final e in [lo, hi])
      if (e case Fin(:final v)) v,
};

void main() {
  test('interval widening chains stay on the first ends and the landmarks', () {
    // Every element's finite ends lie in K, the first element's and the landmarks, and the
    // chain has at most 2|K| + 2 elements, at any number of pieces.
    final rng = Rng(0x71de);
    var longest = 0;
    for (var i = 0; i < randomInstances; i++) {
      final marks = randomMarks(rng);
      final first = randomSet(rng).join(IntervalSet.single(rng.int_(-50, 50)));
      IntervalSet? fed = first;
      final c = chain(const IntervalSet.empty(), () {
        final f = fed;
        fed = null;
        return f ?? randomSet(rng);
      }, marks);
      final k = ends(first).union(marks.ints.toSet());
      expect(c.length, lessThanOrEqualTo(2 * k.length + 3), reason: '|K| = ${k.length}');
      for (final x in c.skip(1)) {
        expect(k.containsAll(ends(x)), isTrue, reason: '$x has an end outside $k');
      }
      if (c.length > longest) longest = c.length;
    }
    expect(longest, greaterThan(3), reason: 'the chains are all short');
  });

  test('interval narrowing chains stay on the first ends and the landmarks', () {
    // Each value lies between its meet and the one before; its finite ends are the first
    // value's, landmarks, or a bound that replaced an infinite end, once on each side.
    final rng = Rng(0x71df);
    for (var i = 0; i < randomInstances; i++) {
      final marks = randomMarks(rng);
      final first = randomSet(rng).join(iv(rng.int_(-60, 60), null));
      final c = descent(first, () => randomSet(rng).join(iv(rng.int_(-60, 60), null)), marks);
      final k = ends(first).union(marks.ints.toSet());
      expect(c.length, lessThanOrEqualTo(2 * k.length + 5), reason: '|K| = ${k.length}');
      for (final x in c) {
        expect(ends(x).difference(k).length, lessThanOrEqualTo(2), reason: '$x against $k');
      }
    }
  });

  test('a moved endpoint goes to the next landmark or infinity', () {
    final none = Landmarks.none();
    final x = IntervalSet.of(0, 3).join(IntervalSet.of(10, 12));
    // The upper bound moved: with no landmark above it, it goes to +inf.
    expect(x.widen(x.join(IntervalSet.of(12, 14)), none), IntervalSet.of(0, 3).join(iv(10, null)));
    // With the literal 20 written, it stops at 19, for `< 20`.
    expect(
      x.widen(x.join(IntervalSet.of(12, 14)), Landmarks.of([20])),
      IntervalSet.of(0, 3).join(IntervalSet.of(10, 19)),
    );
    // A new piece inside the gap: its new endpoints move to the old ones and merge it with
    // both neighbors, unless a landmark is nearer.
    expect(x.widen(x.join(IntervalSet.single(6)), none), IntervalSet.of(0, 12));
    expect(
      x.widen(x.join(IntervalSet.single(8)), Landmarks.of([6])),
      IntervalSet.of(0, 3).join(IntervalSet.of(7, 12)),
    );
    // The lower bound moved: it goes to -inf.
    expect(x.widen(x.join(IntervalSet.single(-1)), none).toString(), '[..=3, 10..=12]');
    // From the bottom, the widening is the value.
    expect(const IntervalSet.empty().widen(x, none), x);
  });

  test('a narrowing keeps old ends and takes a bound for an infinite one', () {
    final none = Landmarks.none();
    final x = iv(0, null);
    // An infinite end takes the bound.
    expect(x.narrow(IntervalSet.of(0, 99), none), IntervalSet.of(0, 99));
    // A finite one moves back to the old end, or to a landmark in between.
    final y = IntervalSet.of(0, 99);
    expect(y.narrow(IntervalSet.of(5, 50), none), y);
    expect(y.narrow(IntervalSet.of(5, 50), Landmarks.of([10, 60])), IntervalSet.of(0, 59));
  });

  test('congruence chains end when the modulus stops dividing', () {
    // A pointer's offsets 4, 12, 16, 10 and 7, seen in turn: the class weakens from 4 to
    // 4 mod 8, 0 mod 4, 0 mod 2 and every integer. Each modulus divides the one before, so
    // every chain is finite.
    var x = Congruence.bottom;
    final seen = <Congruence>[];
    for (final v in [4, 12, 16, 10, 7]) {
      x = x.widen(x.join(Congruence.single(v)), Landmarks.none());
      seen.add(x);
    }
    expect(seen, [
      Congruence.single(4),
      Congruence(8, 4),
      Congruence(4, 0),
      Congruence(2, 0),
      Congruence.top,
    ]);
    final rng = Rng(0xc0);
    for (var i = 0; i < randomInstances; i++) {
      // The modulus of a 64-bit value has at most 64 prime factors, plus the first value.
      chain(
        Congruence.bottom,
        () => Congruence.single(rng.int_(-1000, 1000)),
        Landmarks.none(),
        66,
      );
    }
  });

  test('a congruence narrows at most three times', () {
    // Meets alone could descend 0 mod 2, 0 mod 4, 0 mod 8, ... without end; the narrowing
    // leaves the top once and then moves only to one value or none.
    final none = Landmarks.none();
    final even = Congruence(2, 0);
    expect(Congruence.top.narrow(even, none), even);
    expect(even.narrow(Congruence(4, 0), none), even);
    expect(even.narrow(Congruence.single(8), none), Congruence.single(8));
    final rng = Rng(0xc1);
    for (var i = 0; i < randomInstances; i++) {
      descent(Congruence.top, () => Congruence(1 << rng.below(8), 0), none, 4);
    }
  });

  test('a finite set widens to the top at a member the program does not write', () {
    // Tags the program writes, 0 to 200, stay exact however many there are.
    final written = [for (var t = 0; t <= 200; t += 3) t];
    final tags = Landmarks.of(written);
    final next = written.iterator;
    final c = chain(
      FiniteSet<int>.bottom(),
      () => FiniteSet.of([if (next.moveNext()) next.current]),
      tags,
      70,
    );
    expect(c.last.members, hasLength(67));
    // A computed value the program does not write gives the top.
    final codes = FiniteSet.of([200, 404]);
    final marks = Landmarks.of([200, 404, 500]);
    expect(codes.widen(codes.join(FiniteSet.of([500])), marks), FiniteSet.of([200, 404, 500]));
    expect(codes.widen(codes.join(FiniteSet.of([1000])), marks), const FiniteSet<int>.top());
  });

  test('a growing buffer length widens to unbounded and stays nonnegative', () {
    // A buffer that grows: a new upper bound on its length widens to unbounded at once when
    // no landmark is above it.
    final len = Card.range(const Fin(0), const Fin(1));
    final none = Landmarks.none();
    expect(
      len.widen(len.join(Card.range(const Fin(2), const Fin(2))), none),
      Card.range(const Fin(0), posInf),
    );
    // A length that shrinks below its old minimum widens to 0, not -inf.
    final shrunk = Card.range(const Fin(3), const Fin(5));
    expect(
      shrunk.widen(shrunk.join(Card.range(const Fin(1), const Fin(1))), none),
      Card.range(const Fin(0), const Fin(5)),
    );
    final rng = Rng(0xca);
    for (var i = 0; i < randomInstances; i++) {
      chain(
        const Card.bottom(),
        () {
          final a = rng.int_(0, 40);
          return Card.range(Fin(a), Fin(a + rng.int_(0, 3)));
        },
        none,
        4,
      );
    }
  });
}
