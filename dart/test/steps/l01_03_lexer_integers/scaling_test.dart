/// Lexing integers is of order n log n in the length of the text: many literals in every base,
/// one long literal, and a long literal that runs into a name at its end (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/scaling.dart';

void main() {
  test('many literals in every base', () {
    check('lex', 2000, (n) {
      expect(lex('1_048_576 0o755 0xFF_88_00 0b1011 8080 ' * n), hasLength(5 * n));
    });
  });

  test('one long literal', () {
    check('lex', 20000, (n) {
      expect(lex('${'1_0' * n}9'), hasLength(1));
    });
  });

  test('one long literal that runs into a name', () {
    check('lex', 20000, (n) {
      expect(() => lex('0x${'F_0' * n}g'), throwsA(isA<LexError>()));
    });
  });
}
