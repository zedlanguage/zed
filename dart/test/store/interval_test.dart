/// The interval domain's unit checks: normalization, printing, exact meet and join, the cap,
/// and the widening's moves.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

IntervalSet set(List<(int, int)> pieces) =>
    IntervalSet.fromPieces([for (final (a, b) in pieces) (Fin(a), Fin(b))]);

void main() {
  test('normalization merges overlapping and adjacent pieces', () {
    expect(set([(5, 7), (0, 2), (3, 3)]), set([(0, 3), (5, 7)]));
    expect(set([(0, 2), (1, 9)]).pieces, [(const Fin(0), const Fin(9))]);
    expect(set([(3, 2)]).isEmpty, isTrue);
    expect(IntervalSet.range(const Fin(maxInt), posInf).pieces, hasLength(1));
  });

  test('printing uses the type syntax', () {
    expect(set([(0, 4)]).toString(), '[0..=4]');
    expect(IntervalSet.range(const Fin(0), posInf).toString(), '[0..]');
    expect(IntervalSet.top().toString(), '[..]');
    expect(
      IntervalSet.fromPieces([(negInf, const Fin(-1)), (const Fin(1), posInf)]).toString(),
      '[..=-1, 1..]',
    );
    expect(const IntervalSet.empty().toString(), '[]');
  });

  test('meet and join are exact on small sets', () {
    // Every pair of subsets of 0..6 given as unions: meet and join agree with set algebra.
    List<int> members(IntervalSet s) => [
      for (var v = 0; v < 6; v++)
        if (s.contains(v)) v,
    ];
    final sets = [
      for (var mask = 0; mask < 64; mask++)
        IntervalSet.fromPieces([
          for (var i = 0; i < 6; i++)
            if (mask & (1 << i) != 0) (Fin(i), Fin(i)),
        ]),
    ];
    for (final a in sets) {
      for (final b in sets) {
        expect(members(a.meet(b)), [...members(a).where(b.contains)]);
        expect(members(a.join(b)), [
          for (var v = 0; v < 6; v++)
            if (a.contains(v) || b.contains(v)) v,
        ]);
      }
    }
  });

  test('the cap merges the smallest gap and the lower pair on a tie', () {
    final s = set([(0, 0), (2, 2), (4, 4), (10, 10)]);
    expect(s.cap(3), set([(0, 2), (4, 4), (10, 10)]));
    expect(s.cap(2), set([(0, 4), (10, 10)]));
    expect(s.cap(1), set([(0, 10)]));
  });

  test('widening sends moved outer endpoints to infinity', () {
    final none = Landmarks.none();
    final a = set([(0, 2)]);
    expect(a.widen(set([(0, 3)]), none), IntervalSet.range(const Fin(0), posInf));
    expect(a.widen(set([(-1, 2)]), none), IntervalSet.range(negInf, const Fin(2)));
    expect(a.widen(a, none), a);
    expect(const IntervalSet.empty().widen(a, none), a);
  });

  test('widening fills a gap that a new inner endpoint opens', () {
    final none = Landmarks.none();
    // A new piece between two old ones: both of its endpoints are new, so the gaps on both
    // sides are filled.
    expect(set([(0, 0), (10, 10)]).widen(set([(0, 0), (5, 5), (10, 10)]), none), set([(0, 10)]));
    // An inner endpoint that moves down joins its piece to the one below.
    expect(set([(0, 0), (10, 20)]).widen(set([(0, 0), (9, 20)]), none), set([(0, 20)]));
  });
}
