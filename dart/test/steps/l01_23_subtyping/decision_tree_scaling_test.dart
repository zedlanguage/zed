/// Step L1.23: a product of tuple types covered by the rows of a decision tree, decided by
/// narrowing the product on every row at each split.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/scaling.dart';

Type lit(int i) => Type.lit(Int(i))!;

/// The rows of a decision tree on `c` columns of `{b, b + 1, b + 2}`: on column `i`, after
/// `b + 2` in every column before it, `b` and `b + 1` each end a row and `b + 2` goes on; on
/// the last column `b + 2` ends a row too. The rows cover the product of the columns.
(Type, List<Type>) decisionTree(int c, int b) {
  final column = Type.unionAll([for (var v = b; v < b + 3; v++) lit(v)]);
  Type row(int i, int v) =>
      Type.tuple([for (var j = 0; j < c; j++) j < i ? lit(b + 2) : (j == i ? lit(v) : column)]);
  final rows = [
    for (var i = 0; i < c; i++) ...[row(i, b), row(i, b + 1)],
    row(c - 1, b + 2),
  ];
  return (Type.tuple(List.filled(c, column)), rows);
}

void main() {
  test('a decision tree is decided in polynomial time', () {
    // Splitting the product on every row in turn made `3^c` pieces, and cubic from there once
    // the split took a column whose cells are disjoint. Narrowing every row on every column at
    // each of the `c` splits was `O(c³)`, `N^1.5` in the `N ≈ 2c²` components written: 6.2 s
    // at `c = 128`. A split now tests again only the rows open on the column it changed:
    // `O(c²)`, linear in `N`.
    var fresh = 1;
    checkOrder('a decision tree, by column count', 16, 2, (c) {
      final (p, rows) = decisionTree(c, 1000 * fresh++);
      expect(
        (p - Type.unionAll(rows)).isEmpty,
        isTrue,
        reason: 'the rows cover the product at c = $c',
      );
    });
  });

  test('a row left out of a decision tree is found', () {
    for (final c in [1, 2, 5, 16]) {
      final (p, rows) = decisionTree(c, 0);
      expect((p - Type.unionAll(rows)).isEmpty, isTrue, reason: 'c = $c');
      for (var i = 0; i < rows.length; i++) {
        final less = [...rows]..removeAt(i);
        expect((p - Type.unionAll(less)).isEmpty, isFalse, reason: 'c = $c, row $i left out');
      }
    }
  });
}
