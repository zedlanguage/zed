/// Lexing floats and rationals is of order n log n in the length of the text: many literals,
/// one long float with a long exponent, and a long float that runs into a name at its end
/// (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/scaling.dart';

void main() {
  test('many literals', () {
    check('lex', 2000, (n) {
      expect(lex('0.5 1.5e-3 6.022_140_76e23 0.1r 2.5e-3r 1..10 ' * n), hasLength(8 * n));
    });
  });

  test('one long float with a long exponent', () {
    check('lex', 20000, (n) {
      expect(lex('${'1_0' * n}.${'0_5' * n}e-${'1' * n}r'), hasLength(1));
    });
  });

  test('one long float that runs into a name', () {
    check('lex', 20000, (n) {
      expect(() => lex('${'1_0' * n}.5${'m' * n}'), throwsA(isA<LexError>()));
    });
  });
}
