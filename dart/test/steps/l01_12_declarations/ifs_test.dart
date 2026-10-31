/// `if` takes both branches, and `else if` nests on the right.
library;

import 'package:test/test.dart';

import 'sx.dart';

void main() {
  test('if takes both branches and else if nests on the right', () {
    check([
      (
        'sign(x) = if x < 0 { -1 } else { 1 };',
        '(def sign (x) = (if (< x 0) (block (return (- 1))) (block (return 1))))',
      ),
      (
        'sign(x) = if x < 0 { -1 } else if x == 0 { 0 } else { 1 };',
        '(def sign (x) = (if (< x 0) (block (return (- 1))) '
            '(if (== x 0) (block (return 0)) (block (return 1)))))',
      ),
    ]);
  });

  test('every branch block exports', () {
    check([
      (
        'f(x) = if x { y = 1; } else { 2 };',
        'error: this block exports nothing: end it with an expression or `return e;`',
      ),
    ]);
  });
}
