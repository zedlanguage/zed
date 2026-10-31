/// The unit checks of the congruence, finite-set and cardinality lattices.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

List<Congruence> classes() => [
  Congruence.bottom,
  for (var m = 0; m <= 6; m++)
    for (var r = 0; r < (m > 1 ? m : 1); r++) Congruence(m, r),
  for (var v = -3; v <= 3; v++) Congruence.single(v),
];

void main() {
  test('a congruence join and meet agree with their members', () {
    // On -30..=30, the join contains both operands and the meet is exactly the common members.
    for (final a in classes()) {
      for (final b in classes()) {
        final (j, m) = (a.join(b), a.meet(b));
        for (var v = -30; v <= 30; v++) {
          if (a.contains(v) || b.contains(v)) expect(j.contains(v), isTrue, reason: '$a ⊔ $b');
          expect(m.contains(v), a.contains(v) && b.contains(v), reason: '$a ⊓ $b at $v');
        }
      }
    }
  });

  test('a congruence join is the least class above both', () {
    expect(Congruence.single(1).join(Congruence.single(5)), Congruence(4, 1));
    expect(Congruence(4, 1).join(Congruence.single(3)), Congruence(2, 1));
    expect(Congruence(4, 1).join(Congruence(6, 1)), Congruence(2, 1));
    expect(Congruence(2, 1).join(Congruence.single(2)), Congruence.top);
  });

  test('finite sets widen to the top unless the new members are landmarks', () {
    final small = FiniteSet.of([for (var i = 0; i < 100; i++) i]);
    final none = Landmarks.none();
    expect(FiniteSet<int>.bottom().widen(small, none), small);
    final more = small.join(FiniteSet.of([200]));
    expect(small.widen(more, none), const FiniteSet<int>.top());
    expect(small.widen(more, Landmarks.of([200])), more);
    expect(FiniteSet.of([1]).meet(const FiniteSet.top()), FiniteSet.of([1]));
  });

  test('a cardinality never goes below zero', () {
    final c = Card.range(const Fin(2), const Fin(3));
    final none = Landmarks.none();
    expect(
      c.widen(Card.range(const Fin(1), const Fin(3)), none),
      Card.range(const Fin(0), const Fin(3)),
    );
    expect(c.widen(Card.range(const Fin(2), const Fin(4)), none), Card.range(const Fin(2), posInf));
    expect(Card.range(negInf, const Fin(1)), Card.range(const Fin(0), const Fin(1)));
  });
}
