/// Step L1.3: integer literals in four bases, with `_` between digits.
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/support.dart';

/// The integers of `text` as `(base, digits)`.
List<(int, String)> ints(String text) => [
  for (final t in lex(text))
    switch (t.tok) {
      Int(:final radix, :final digits) => (radix, digits),
      final other => fail('$text: $other'),
    },
];

void main() {
  test('literals as programs write them', () {
    // A megabyte, a file mode, an RGB color, a flag mask, and a port.
    expect(ints('1_048_576 0o755 0xFF_88_00 0b1011 8080'), [
      (10, '1048576'),
      (8, '755'),
      (16, 'FF8800'),
      (2, '1011'),
      (10, '8080'),
    ]);
  });

  test('a literal keeps every digit whatever its size', () {
    // 2^64 and 2^128 + 1, which no machine integer holds: the width is chosen from the use.
    const big = '340282366920938463463374607431768211457';
    expect(ints('18446744073709551616 $big'), [(10, '18446744073709551616'), (10, big)]);
  });

  test('leading zeros are decimal digits and hex digits keep their case', () {
    expect(ints('007 0 00 0xdeadBEEF'), [(10, '007'), (10, '0'), (10, '00'), (16, 'deadBEEF')]);
  });

  test('malformed numbers', () {
    const cases = [
      'timeout 200ms',
      'count 1__000',
      'count 1_000_',
      'mask 0b1012',
      'mode 0o789',
      'color 0x',
      'color 0xG0',
      'big 0X1F',
      'flags 0b_101',
      'day 1d',
    ];
    final out = [
      for (final c in cases)
        switch (() {
          try {
            lex(c);
          } on LexError catch (e) {
            return e;
          }
          fail('$c lexed');
        }()) {
          final e => '${c.padRight(16)} [${e.span.start}..${e.span.end}] $e',
        },
    ];
    expectOutput('l01_03_lexer_integers', 'malformed_numbers', out.join('\n'));
  });

  test('a number ends where a name character does not follow', () {
    // `_` is a name character, so it must be followed by a digit to stay in the number.
    expect([for (final t in lex('12 3')) (t.span.start, t.span.end)], [(0, 2), (3, 4)]);
  });
}
