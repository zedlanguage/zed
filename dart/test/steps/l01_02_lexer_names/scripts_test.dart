/// The one-script rule: names in every script lex, a name that mixes scripts is rejected.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/lex.dart';

void main() {
  test('names in one script lex', () {
    for (final name in [
      // German, French, Greek, Russian, Hebrew, Arabic, Hindi.
      'gr\u00f6\u00dfe',
      'na\u00efve',
      '\u03c0\u03bb\u03ac\u03c4\u03bf\u03c2',
      '\u0434\u043b\u0438\u043d\u0430',
      '\u05d0\u05d5\u05e8\u05da',
      '\u0637\u0648\u0644',
      '\u0932\u0902\u092c\u093e\u0908',
      // Chinese, Japanese mixing Han with both kana and the long-vowel mark, Korean.
      '\u9762\u7a4d',
      '\u30e6\u30fc\u30b6\u30fc\u540d',
      '\u3072\u3089\u304c\u306a\u6f22\u5b57\u30ab\u30bf\u30ab\u30ca',
      '\uc0ac\uc6a9\uc790',
      // Latin joined with one East Asian writing system.
      'user\u540d',
      'item\u306e\u4fa1\u683c',
      'total\ud569\uacc4',
      // Digits and `_` share every script.
      '\u0434\u043b\u0438\u043d\u0430_2',
      '\u9762\u7a4d1',
      "x'",
    ]) {
      final toks = lex(name);
      expect(toks, hasLength(1), reason: name);
      expect(toks[0].tok, Name(name));
    }
  });

  test('lookalike letters from another script are rejected', () {
    final cases = [
      // `а` is CYRILLIC SMALL LETTER A.
      ('p\u0430ypal', 'Latin, Cyrillic'),
      // `е` and `х` Cyrillic, the rest Latin.
      ('\u0435\u0445ample', 'Cyrillic, Latin'),
      // `ο` is GREEK SMALL LETTER OMICRON.
      ('c\u03bfunt', 'Latin, Greek'),
      // A physics name mixing Greek and Latin is rejected too: write `deltaT` or `ΔΘ`.
      ('\u0394T', 'Greek, Latin'),
      // Hangul with kana is no one writing system.
      ('\uc0ac\uc6a9\uc790\u30e6\u30fc\u30b6\u30fc', 'Hangul, Katakana'),
    ];
    for (final (name, scripts) in cases) {
      final text = 'total $name';
      final e = (() {
        try {
          lex(text);
        } on LexError catch (e) {
          return e;
        }
        fail('$text lexed');
      })();
      expect(e.kind, MixedScript(name));
      expect((e.span.start, e.span.end), (6, utf8.encode(text).length));
      expect(e.toString(), 'the name "$name" mixes scripts: $scripts');
    }
  });

  test('the prime is not read as a script', () {
    expect(() => lex("\u0434\u043b\u0438\u043d\u0430'"), returnsNormally);
    expect(isSingleScript('p\u0430y'), isFalse);
    expect(isSingleScript('pay'), isTrue);
  });
}
