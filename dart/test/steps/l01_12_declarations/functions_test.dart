/// Functions in equation and block form, `main`'s ports, and `test` tables.
library;

import 'package:test/test.dart';

import 'sx.dart';

void main() {
  test('an equation function is its expression', () {
    check([
      ('area(w, h) = w * h;', '(def area (w h) = (* w h))'),
      (
        'scale(x: f64, by: f64 = 2.0) = x * by;',
        '(def scale ((x: f64) (by: f64 = 2.0)) = (* x by))',
      ),
      ('zero() = 0;', '(def zero () = 0)'),
    ]);
  });

  test('a block function is its block', () {
    check([
      (
        'hyp(a, b) { s = a * a + b * b; sqrt(s) }',
        '(def hyp (a b) (block (= (s) (+ (* a a) (* b b))) (return (call sqrt s))))',
      ),
    ]);
  });

  test('main declares its ports and may only push', () {
    check([
      (
        'main(stdin: Lines) -> (stdout: Lines) { stdout <- stdin; }',
        '(def main ((stdin: Lines)) (-> (stdout: Lines)) (block (<- stdout stdin)))',
      ),
      (
        'main(stdin: Lines) -> (out: Lines, err: Lines) { out <- stdin; err <- stdin; }',
        '(def main ((stdin: Lines)) (-> (out: Lines) (err: Lines)) '
            '(block (<- out stdin) (<- err stdin)))',
      ),
    ]);
  });

  test('a test table lists input and expected in order', () {
    check([
      (
        'double(x) = 2 * x test { 1 -> 2, 3 -> 6, }',
        '(def double (x) = (* 2 x) (test (1 2) (3 6)))',
      ),
      (
        'neg(x) { 0 - x } test { 1 -> -1 } test { 0 -> 0 }',
        '(def neg (x) (block (return (- 0 x))) (test (1 (- 1)) (0 0)))',
      ),
    ]);
  });

  test('a function inside a block is a statement', () {
    check([
      (
        'f(x) { sq(v) = v * v; sq(x) }',
        '(def f (x) (block (def sq (v) = (* v v)) (return (call sq x))))',
      ),
    ]);
  });

  test("the unit's top level exports nothing and block bodies still export once", () {
    check([
      ('return 1;', "error: `return` exports from a block; a unit's top level has none"),
      ('f(x) { return x; x }', "error: a block exports once; the block's first export at byte 7"),
    ]);
  });

  test('a form of a later layer names that layer', () {
    check([
      ('f(x) -> int = x;', 'error: this form (Result) is built from layer L10'),
      ('t[i] <- 1;', 'error: this form (Push) is built from layer L7'),
    ]);
  });
}
