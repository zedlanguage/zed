/// Operator arrows per region: data selects an arrow, a loose atom selects none and flows
/// on, and the atoms of several operands merge into `#errs` of the set of them.
library;

import 'package:test/test.dart';

import '../l01_16_elaboration/elab.dart';
import 'scalar.dart';

void main() {
  test('one failure flows through the arithmetic', () {
    expect(x('int("x") * 2 + 1'), '#invalid');
    expect(x('-(10 div 0)'), '#divByZero');
  });

  test('two failures merge into a set', () {
    expect(x('int("seven") + int(2.5)'), '#errs({#inexact, #invalid})');
    expect(
      x('int(2.5) + int("seven")'),
      '#errs({#inexact, #invalid})',
      reason: 'the set has no order to invent',
    );
    expect(x('int("a") + int("b")'), '#invalid', reason: 'a singleton unwraps');
  });

  test('a merge flattens, and `else` replaces it', () {
    const src =
        'price = int("n/a");\nqty = int(1.5);\nfee = 10 div 0;\n'
        'total = price * qty + fee;\nshown = total else 0;\n';
    expect(value(src, 'total'), '#errs({#divByZero, #inexact, #invalid})');
    expect(value(src, 'shown'), '0');
  });

  test('an atom compared with `==` is data', () {
    expect(x('int("x") == int("y")'), 'true');
    expect(x('int("x") != int(2.5)'), 'true');
  });

  test('Euclidean division keeps the remainder non-negative', () {
    const cases = [
      ('7 div -2', '-3'),
      ('7 mod -2', '1'),
      ('-7 div -2', '4'),
      ('-7 mod -2', '1'),
      ('-7 div 2', '-4'),
      ('-7 mod 2', '1'),
    ];
    for (final (e, want) in cases) {
      expect(x(e), want, reason: e);
    }
  });

  test('mixed kinds select no arrow', () {
    expect(x('1 + 1.0'), startsWith('error: type error'));
    expect(x('"a" ++ 1'), startsWith('error: type error'));
    expect(x('1r/2r * 2'), startsWith('error: type error'));
  });
}
