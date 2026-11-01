/// A declared function's signature comes from its body: an untyped parameter is a type
/// variable, bounded by the carriers its uses take, and the error is at the use that leaves
/// it none.
library;

import 'package:test/test.dart';

import 'support.dart';

void main() {
  test('arithmetic gives a variable bounded by the numeric carriers', () {
    expect(sig('area(w, h) = w * h;\n', 'area'), '(w: T, h: T) -> T for T in int | f64 | rat');
    expect(sig('neg(x) = -x;\n', 'neg'), '(x: T) -> T for T in int | f64 | rat');
  });

  test('an operator with one carrier fixes it', () {
    expect(sig('shout(s) = upper(s) ++ "!";\n', 'shout'), '(s: String) -> String');
    expect(sig('both(a, b) = a && b;\n', 'both'), '(a: bool, b: bool) -> bool');
    // `/` divides f64 and rat only, and the literal `2` adopts f64.
    expect(sig('half(x) = x / 2;\n', 'half'), '(x: f64) -> f64');
    expect(sig('avg(a, b) = (a + b) / 2;\n', 'avg'), '(a: f64, b: f64) -> f64');
  });

  test('comparison checks at every ordered carrier', () {
    expect(
      sig('lt(a, b) = a < b;\n', 'lt'),
      '(a: T, b: T) -> bool for T in int | f64 | rat | String | bool',
    );
  });

  test('a parameter any value fits gets a type variable', () {
    expect(sig('label(n) = "n = \${n}";\n', 'label'), '(n: T) -> String');
    expect(sig('pair(a, b) = (a, b);\n', 'pair'), '(a: T, b: U) -> (T, U)');
    expect(sig('g(r) = r else 0;\n', 'g'), '(r: T) -> 0 | T');
    // Only the condition is fixed; the branches stay generic, each its own variable.
    expect(
      sig('pick(positional c, positional a, positional b) = if c { a } else { b };\n', 'pick'),
      '(bool, T, U) -> T | U',
    );
  });

  test('a type variable used as a tuple gives the unknown', () {
    expect(sig('first(p) = p[0];\n', 'first'), '(p: T) -> _');
  });

  test('a declared type is kept', () {
    expect(
      sig('apply(positional x, f: (int) -> int) = f(x);\n', 'apply'),
      '(int, f: ((int) -> int)) -> int',
    );
    expect(
      sig('n(x: int | String) = if x is String { len(x) } else { x * 2 };\n', 'n'),
      '(x: int | String) -> int',
    );
  });

  test("a default is checked at its parameter's type", () {
    expect(
      sig('tax(price, rate = 0.2) = price * rate;\n', 'tax'),
      '(price: f64, rate: f64) -> f64',
    );
    expect(
      sig('tax(price, rate = price / 10.0) = price * rate;\n', 'tax'),
      '(price: f64, rate: f64) -> f64',
    );
  });

  test('a default of the wrong type is an error', () {
    expect(typeErrors('f(a: int, b: int = a > 0) = a + b;\n'), [
      'the default of `b` is bool, not int [a > 0]',
    ]);
  });

  test('a body that checks at no type is reported', () {
    // Wrong at every type: the error is the body's own.
    expect(typeErrors('bad(x) = x + "a" * 2;\n'), ['`*` does not take ("a", 2) ["a" * 2]']);
    // Wrong at each carrier, for a reason that depends on it: `++` makes `x` a String, and
    // the error is at the use that then finds it none.
    expect(typeErrors('neither(x) = x ++ "a" + 1;\n'), [
      '`+` does not take (String, 1) [x ++ "a" + 1]',
    ]);
  });

  test('a parameter compared with a tuple may be a tuple', () {
    // `<` orders tuples of one length as well as carriers, so `x` may be `(3, 4)`: its
    // class keeps the tuple arrow, which allows only other values, and it gives `_`.
    const src = 'lt(positional x) = x < (1, 2);\nmain() = lt((3, 4));\n';
    expect(sig(src, 'lt'), '(_) -> bool');
    expect(typeErrors(src), isEmpty);
  });

  test('a literal compared for equality does not bound a parameter', () {
    // `==` takes any two values, so the literal follows the class and leaves it every
    // carrier: `eq1("a")` is false, not an error.
    const src = 'eq1(positional x) = x == 1;\nmain() = eq1("a");\n';
    expect(sig(src, 'eq1'), '(T) -> bool');
    expect(typeErrors(src), isEmpty);
  });
}
