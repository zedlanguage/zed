/// Step L1.6: keywords, names reserved by position, operators, atoms and annotations, and the
/// lexical errors.
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/support.dart';
import '../../support/tokens.dart';

/// The error lexing `src`.
LexError error(String src) {
  try {
    lex(src);
  } on LexError catch (e) {
    return e;
  }
  fail('$src lexed');
}

void main() {
  test('every keyword is a keyword and a longer word is a name', () {
    for (final k in keywords) {
      expect(lex(k)[0].tok, Keyword(k), reason: k);
      for (final longer in ['${k}s', '${k}_1', '${k}2', '_$k']) {
        expect(lex(longer)[0].tok, Name(longer), reason: longer);
      }
    }
    expect(keywords, hasLength(36));
    expect(
      render(lex('format iffy in_stock types notable asc ascending')),
      'format iffy in_stock types notable «asc» ascending',
    );
  });

  test('where and sep are names reserved only by position', () {
    expect(render(lex('for x in xs where x > 0')), '«for» x «in» xs where x > 0₍10₎');
    expect(lex('sep')[0].tok, const Name('sep'));
  });

  test('a prime does not continue a keyword', () {
    // `if'` is the keyword `if` and a stray `'`, as `KeywordWord !XID_CONTINUE` reads it.
    final e = error("if'");
    expect((e.kind, e.span.start), (const Unexpected(0x27), 2));
  });

  test('every operator lexes alone and the longest wins', () {
    for (final op in operators) {
      expect([for (final t in lex(op)) t.tok], [Op(op)], reason: op);
    }
    const cases = [
      ('f->?g', 'f ->? g'),
      ('0..<n', '0₍10₎ ..< n'),
      ('0..=n', '0₍10₎ ..= n'),
      ('a...', 'a ...'),
      ('x**2', 'x ** 2₍10₎'),
      ('a++b', 'a ++ b'),
      ('p<-m', 'p <- m'),
      ('x< -1', 'x < - 1₍10₎'),
      ('a><(+)', 'a >< ( + )'),
      ('a?.b*.c', 'a ?. b *. c'),
      ('m::n', 'm :: n'),
      ('a!=b==c<=d>=e', 'a != b == c <= d >= e'),
      ('a&&b||!c', 'a && b || ! c'),
      (r'\x -> x', r'\ x -> x'),
      ('[1,2];{}', '[ 1₍10₎ , 2₍10₎ ] ; { }'),
      ('a=b:c|d&e?f/g', 'a = b : c | d & e ? f / g'),
    ];
    for (final (src, want) in cases) {
      expect(render(lex(src)), want, reason: src);
    }
  });

  test('atoms and annotations', () {
    expect(
      render(lex("@log @pure #none #inexact #syntaxError(pos: 3) #ok' #if")),
      "@log @pure #none #inexact #syntaxError ( pos : 3₍10₎ ) #ok' #if",
    );
  });

  test('lexical errors', () {
    const cases = [
      '# none',
      'x = @',
      '#pаypal',
      r'cost = $5',
      'a % b',
      'a ^ b',
      'x ~ y',
      '`cmd`',
      "x''",
    ];
    expectOutput(
      'l01_06_lexer_tokens',
      'lexical_errors',
      [
        for (final c in cases)
          if (error(c) case final e) '${c.padRight(12)} [${e.span.start}..${e.span.end}] $e',
      ].join('\n'),
    );
  });
}
