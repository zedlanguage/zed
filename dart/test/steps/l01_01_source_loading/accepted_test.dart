/// Files that load, and the text the lexer then reads.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/source.dart';

const lf = '// invoice\nrate = 3;\ntotal = rate * 4;\n';

String loadText(String s) => load(utf8.encode(s));

void main() {
  test('Windows and classic Mac line endings load as the Unix file', () {
    expect(loadText(lf), lf);
    expect(loadText(lf.replaceAll('\n', '\r\n')), lf);
    expect(loadText(lf.replaceAll('\n', '\r')), lf);
    // A file edited on both systems: each `\r\n`, `\r` and `\n` is one break, so `\n\r` is two.
    expect(loadText('a\r\nb\rc\n\rd'), 'a\nb\nc\n\nd');
  });

  test('NFC text in many scripts loads unchanged', () {
    for (final text in [
      // Precomposed Latin, Vietnamese with two marks on one letter, Greek, Cyrillic.
      'name = "Jos\u00e9"; city = "H\u1ea1\u0301 N\u1ed9i";',
      '// \u03b1\u03b2\u03b3 \u043f\u0440\u0438\u0432\u0435\u0442',
      // A precomposed Hangul syllable, and `q` with a dot above, which has no precomposed form
      // and so stays two characters in NFC.
      'word = "\ud55c\uae00"; mark = "q\u0307";',
      // An emoji sequence joined by U+200D, and an empty file.
      'family = "\u{1f468}\u200d\u{1f469}\u200d\u{1f467}";',
      '',
    ]) {
      expect(loadText(text), text);
    }
  });

  test('a byte order mark after the start is left to the lexer', () {
    expect(loadText('a = 1;\ufeff'), 'a = 1;\ufeff');
  });
}
