/// Step L1.4: float literals, which need a leading digit, and exact `r` rationals.
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/support.dart';

/// The token kinds and values of `text`.
List<Tok> toks(String text) => [for (final t in lex(text)) t.tok];

void main() {
  test('floats as programs write them', () {
    // A half, a tolerance, a billion, Avogadro's number grouped, a large exponent.
    expect(toks('0.5 1.5e-3 1e9 6.022_140_76e23 2E+10 1e400'), [
      const Float('0.5'),
      const Float('1.5e-3'),
      const Float('1e9'),
      const Float('6.02214076e23'),
      const Float('2E+10'),
      const Float('1e400'),
    ]);
  });

  test('rationals are decimal and keep their text', () {
    // A third is `1r/3r` once `/` lexes (step L1.6); `0.1r` is one tenth exactly.
    expect(toks('3r 0.1r 2.5e-3r 1_000r'), [
      const Rat('3'),
      const Rat('0.1'),
      const Rat('2.5e-3'),
      const Rat('1000'),
    ]);
  });

  test('a digit must follow the dot, so member access and ranges start with the integer', () {
    // Each number ends before the `.`, an operator; `.5` is no float.
    Tok int(String d) => Int(10, d);
    expect(toks('5.double'), [int('5'), const Op('.'), const Name('double')]);
    expect(toks('1..10'), [int('1'), const Op('..'), int('10')]);
    expect(toks('1.e5'), [int('1'), const Op('.'), const Name('e5')]);
    expect(toks('.5'), [const Op('.'), int('5')]);
    expect(toks('12.'), [int('12'), const Op('.')]);
  });

  test('integers are unchanged', () {
    expect(toks('10 0x1E'), [const Int(10, '10'), const Int(16, '1E')]);
  });

  test('malformed floats and rationals', () {
    const cases = ['1e', '1e+', '1.5e', '1.5f', '3R', '0x10r', '1.5_', '2.5ms', '1e3x', '1rr'];
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
          final e => '${c.padRight(6)} [${e.span.start}..${e.span.end}] $e',
        },
    ];
    expectOutput(
      'l01_04_lexer_floats_and_rationals',
      'malformed_floats_and_rationals',
      out.join('\n'),
    );
  });
}
