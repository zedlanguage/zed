/// The unit checks of the weak topological order.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

void main() {
  test('a chain has no component', () {
    expect(
      show(
        weakTopologicalOrder([
          [1],
          [2],
          [],
        ]),
      ),
      '0 1 2',
    );
  });

  test('an inner loop is a component inside the outer one', () {
    // A loop 2 → 3 → 4 → 5 → 6 → 2 with an inner loop 4 ⇄ 5 and an exit 6 → 7. The inner
    // head is 4, which the traversal reaches before 5.
    final succ = [
      [1],
      [2, 7],
      [3],
      [4, 6],
      [5],
      [4, 6],
      [2, 7],
      <int>[],
    ];
    expect(show(weakTopologicalOrder(succ)), '0 1 (2 3 (4 5) 6) 7');
  });

  test('a self-loop is a component', () {
    final order = weakTopologicalOrder([
      [0, 1],
      [],
    ]);
    expect(show(order), '(0) 1');
    expect(order[0].vertices(), [0]);
  });
}
