/// Step L1.5: plain strings, their escapes and the indentation stripping of `"""` strings.
library;

import 'package:test/test.dart';

import '../../support/support.dart';
import 'parts.dart';

void main() {
  test('plain strings and escapes', () {
    expect(text('"Hello, world"'), 'Hello, world');
    expect(text('""'), '');
    expect(text(r'"name\tqty\n"'), 'name\tqty\n');
    expect(text(r'"C:\\Users\\ana"'), r'C:\Users\ana');
    expect(text(r'"she said \"hi\""'), 'she said "hi"');
    expect(text(r'"price: \$5, \${not a hole}"'), r'price: $5, ${not a hole}');
    expect(text(r'"nul\0 cr\r"'), 'nul\x00 cr\r');
    expect(text(r'"\u{1F600} \u{e9} \u{0041}"'), '😀 é A');
    // Text in any script, and a comment delimiter in a string is text.
    expect(
      text('"Größe: 面積 // not a comment /* nor this"'),
      'Größe: 面積 // not a comment /* nor this',
    );
  });

  test('a triple-quoted string strips its closing indentation', () {
    const sql =
        '        query = """\n            SELECT name, qty\n              FROM stock\n\n'
        '             WHERE qty < 10\n            """';
    expect(text(sql.substring(16)), 'SELECT name, qty\n  FROM stock\n\n WHERE qty < 10');
  });

  test('stripping needs both delimiters on their own lines', () {
    // Closing delimiter after text: kept as written, the first line break included.
    expect(text('"""\n  a\n  b"""'), '\n  a\n  b');
    // Opening delimiter followed by text: kept as written.
    expect(text('"""a\n  b\n  """'), 'a\n  b\n  ');
    // A `"""` string may hold quotes and need not span lines; it ends at the first `"""`.
    expect(text('"""say "hi" and ""bye"" ok"""'), 'say "hi" and ""bye"" ok');
  });

  test('blank lines and deeper lines inside a stripped string', () {
    // A line of fewer spaces than the indentation, or none, is an empty line; a deeper one
    // keeps its extra spaces; tabs are indentation when the closing line uses tabs.
    expect(text('"""\n    a\n  \n\n      b\n    """'), 'a\n\n\n  b');
    expect(text('"""\n\tx\n\t\ty\n\t"""'), 'x\n\ty');
    // An escape is decoded after stripping, so `\t` and `\n` are text, not indentation.
    expect(text('"""\n    \\tx\\n\n    """'), '\tx\n');
    // Only the delimiters' line breaks: an empty string.
    expect(text('"""\n    """'), '');
  });

  test('malformed strings', () {
    expectOutput(
      'l01_05_lexer_strings',
      'malformed_strings',
      malformed([
        '"unclosed',
        '"two\nlines"',
        '"""never closed\n',
        r'"\q is not an escape"',
        r'"\u{110000}"',
        r'"\u{D800}"',
        r'"\u0041"',
        r'"\u{}"',
        '"""\n    in\n  out\n    """',
        '"""\n    in\n\tout\n    """',
        r'"ends in a backslash\',
      ]),
    );
  });
}
