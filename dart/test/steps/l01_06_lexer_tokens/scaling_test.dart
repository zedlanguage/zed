/// Lexing keywords, operators, comments and doc comments, and rendering tokens by line, are of
/// order n log n in the length of the text (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/scaling.dart';
import '../../support/tokens.dart';

void main() {
  test('many keywords and operators', () {
    final line = '${keywords.join(' ')} ${operators.join(' ')} @log #ok ';
    check('lex', 200, (n) {
      expect(lex(line * n), hasLength((keywords.length + operators.length + 2) * n));
    });
  });

  test('block comments nested deep', () {
    check('lex', 20000, (n) {
      expect(lex('a ${'/* ' * n}${'*/ ' * n}b'), hasLength(2));
    });
  });

  test('many doc comments', () {
    check('lexWithDocs', 2000, (n) {
      final (tokens, docs) = lexWithDocs('/// a doc\nx = 1;\n' * n);
      expect((tokens.length, docs.length), (4 * n, n));
    });
  });

  test('rendering tokens by line', () {
    check('renderLines', 2000, (n) {
      final text = 'total = price * qty; // a comment\n' * n;
      expect(renderLines(text, lex(text)).split('\n'), hasLength(n));
    });
  });
}
