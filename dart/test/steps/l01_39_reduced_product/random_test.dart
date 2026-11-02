/// The reduced product against the interpreter on random bodies of the shape of `shape.dart`.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';
import 'shape.dart';

void main() {
  test('every value that reaches an arm is in its scope', () {
    final rng = Rng(0x139);
    var (checked, unreachable, narrowed) = (0, 0, 0);
    for (var i = 0; i < 300; i++) {
      final s = Shape.random(rng);
      final arms = s.arms();
      try {
        checked += check(s, arms);
      } on StateError catch (e) {
        fail('$s: ${e.message}');
      }
      unreachable += arms.where((a) => !a.reachable).length;
      narrowed += arms
          .where(
            (a) =>
                a.reachable &&
                switch (a.scope.get('x').ints.bounds) {
                  (final lo, final hi) => lo != negInf || hi != posInf,
                  null => false,
                },
          )
          .length;
    }
    // The check ran, found arms unreachable, and found arms the tests narrowed.
    expect(checked, greaterThan(20000));
    expect(unreachable, greaterThan(40));
    expect(narrowed, greaterThan(100));
  });
}
