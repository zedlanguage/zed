/// Lexing names is of order n log n in the length of the text: many names, one long name, and a
/// long name that mixes scripts only at its end (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/scaling.dart';

void main() {
  test('many names in many scripts', () {
    check('lex', 2000, (n) {
      expect(
        lex(
          "gr\u00f6\u00dfe na\u00efve \u9762\u7a4d \u30e6\u30fc\u30b6\u30fc\u540d user\u540d x' _ _y " *
              n,
        ),
        hasLength(8 * n),
      );
    });
  });

  test('one long name', () {
    check('lex', 20000, (n) {
      expect(lex('ab' * n), hasLength(1));
    });
  });

  test('one long name that mixes scripts at its end', () {
    check('lex', 20000, (n) {
      expect(() => lex('${'\u0434\u043b\u0438\u043d\u0430' * n}x'), throwsA(isA<LexError>()));
    });
  });
}
