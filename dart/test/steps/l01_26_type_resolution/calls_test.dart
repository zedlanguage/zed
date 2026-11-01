/// A call through a value takes named arguments, closed defaults and `...` from the signature
/// the checker gives the value.
library;

import 'package:test/test.dart';

import '../l01_16_elaboration/elab.dart';
import 'support.dart';

void main() {
  test('named arguments through a value', () {
    expect(value('sub(a, b) = a - b;\nk = sub;\ny = k(b: 5, a: 3);\n', 'y'), '-2');
  });

  test('a closed default is filled through a value', () {
    expect(
      value('tax(price, rate = 0.2) = price * rate;\nt = tax;\ny = t(price: 10.0);\n', 'y'),
      '2.0',
    );
  });

  test('a default that reads other parameters needs the declared function', () {
    expect(
      errors('tax(price, rate = price / 10.0) = price * rate;\nt = tax;\ny = t(price: 10.0);\n'),
      [
        "the default of `rate` reads the function's other parameters, so only a call of the "
            'declared function fills it: pass `rate` [t(price: 10.0)]',
      ],
    );
  });

  test('a partial call through a value', () {
    expect(
      value(
        'greet(positional name, punct = "!") = "\${name}\${punct}";\n'
            'g = greet;\nh = g("Al", ...);\ny = h(punct: "?");\n',
        'y',
      ),
      '"Al?"',
    );
  });

  test('destructuring gives each name its component', () {
    const p = 'a, b = (1, "x");\nc = a + 1;\nd = b ++ "y";\n';
    expect(typeErrors(p), isEmpty);
    expect(value(p, 'c'), '2');
    expect(typeErrors('a, b = (1, 2, 3);\n'), [
      'this value is (1, 2, 3), not a tuple of 2 [(1, 2, 3)]',
    ]);
    expect(typeErrors('t = (1, 2)[2];\n'), ['(1, 2) has no component 2 [(1, 2)[2]]']);
  });
}
