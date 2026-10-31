/// Files that are rejected, each as an editor or a tool would write it, with the expected
/// rejection: position, message and span.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/source.dart';
import 'package:zed/src/unicode.dart';

import '../../support/support.dart';

/// The files, by what produced them.
final files = <(String, List<int>)>[
  // Saved as ISO-8859-1 by an editor configured for a Western European locale.
  ('latin1_comment', latin1.encode('// prix du caf\u00e9\nprice = 3;\n')),
  // A customer name pasted from a macOS file name, which stores `e` then U+0301.
  ('decomposed_name', utf8.encode('greeting = "Bonjour";\nname = "Jose\u0301";\n')),
  // Notepad's UTF-8 with a byte order mark.
  ('byte_order_mark', utf8.encode('\ufefftotal = 1;\n')),
  // A download cut off inside the three bytes of `€`.
  ('truncated_download', [...utf8.encode('unit = "'), 0xe2, 0x82]),
  // Java's modified UTF-8 writes a surrogate pair as two three-byte sequences.
  (
    'cesu8_surrogates',
    [...utf8.encode('emoji = "'), 0xed, 0xa0, 0xbd, 0xed, 0xb8, 0x80, ...utf8.encode('";\n')],
  ),
  // An overlong encoding of `/`.
  ('overlong_slash', [...utf8.encode('path = "a'), 0xc0, 0xaf, ...utf8.encode('b";\n')]),
  // U+212B ANGSTROM SIGN, which NFC replaces by U+00C5.
  ('angstrom_sign', utf8.encode('// wavelength in \u212b\nlambda = 5500;\n')),
  // Two marks under and over `a`, typed above first: NFC orders them by combining class.
  ('marks_out_of_order', utf8.encode('word = "a\u0301\u0323";\n')),
  // Conjoining Hangul jamo, which NFC composes to one syllable.
  ('hangul_jamo', utf8.encode('// \u1100\u1161\n')),
  // A Windows file whose second line holds a decomposed character: the column counts the
  // scalars of that line, and `\r\n` is one line break.
  ('crlf_then_decomposed', utf8.encode('a = 1;\r\nb = "n\u0303";\r\n')),
];

String show(String name, List<int> bytes) {
  try {
    load(bytes);
    return '$name: accepted';
  } on Reject catch (r) {
    return '$name: ${r.render(bytes)} [bytes ${r.span.start}..${r.span.end}]';
  }
}

/// A fixed-seed generator, so a failure reproduces.
final class Lcg {
  int _state;
  Lcg(this._state);

  int next(int n) {
    _state = _state * 6364136223846793005 + 1442695040888963407;
    return (_state >>> 33) % n;
  }
}

List<int> cps(List<int> bytes) => utf8.decode(bytes).runes.toList();

void main() {
  test('rejections', () {
    expectOutput(
      'l01_01_source_loading',
      'rejections',
      [for (final (n, b) in files) show(n, b)].join('\n'),
    );
  });

  test('a non-NFC rejection names the NFC spelling, and fixing it loads', () {
    var fixedOne = 0;
    for (final (name, bytes) in files) {
      try {
        load(bytes);
      } on NotNfc catch (r) {
        final fixed = [
          ...bytes.sublist(0, r.span.start),
          ...utf8.encode(r.nfc),
          ...bytes.sublist(r.span.end),
        ];
        expect(() => load(fixed), returnsNormally, reason: '$name: the repaired file still fails');
        fixedOne++;
      } on Reject {
        // Rejected for another reason.
      }
    }
    expect(fixedOne, 5);
  });

  // Over random text built from characters that compose, reorder or are replaced by NFC, the
  // span of every rejection is the first part of the text NFC changes: the text before it is
  // NFC, the span is not, and no shorter end of the span that starts at a character of
  // combining class 0 is not. (An end starting at a mark is not text a person writes: the span
  // starts at the mark's base.)
  test('the span is the first text NFC changes', () {
    const alphabet = [
      0x61, 0x65, 0x6e, 0x78, 0x20, 0x301, 0x303, 0x323, 0x307, 0x212b, 0xc5, //
      0x1100, 0x1161, 0x11a8, 0xac00, 0xb47, 0xb3e, 0x344,
    ];
    final rng = Lcg(29);
    var (rejected, accepted) = (0, 0);
    for (var t = 0; t < 20000; t++) {
      final len = 1 + rng.next(8);
      final s = [for (var i = 0; i < len; i++) alphabet[rng.next(alphabet.length)]];
      final bytes = utf8.encode(String.fromCharCodes(s));
      try {
        final text = load(bytes);
        expect(isNfc(s), isTrue, reason: '$s accepted but not NFC');
        expect(text.runes.toList(), s);
        accepted++;
      } on NotNfc catch (r) {
        final (start, end) = (r.span.start, r.span.end);
        expect(isNfc(s), isFalse, reason: '$s rejected but NFC');
        expect(isNfc(cps(bytes.sublist(0, start))), isTrue, reason: '$s: text before the span');
        final spanned = cps(bytes.sublist(start, end));
        expect(isNfc(spanned), isFalse, reason: '$s: the span is NFC');
        for (var k = 1; k < spanned.length; k++) {
          if (combiningClass(spanned[k]) == 0) {
            expect(isNfc(spanned.sublist(k)), isTrue, reason: '$s: the span could start later');
          }
        }
        expect(r.nfc.runes.toList(), nfc(spanned));
        rejected++;
      }
    }
    expect(rejected, greaterThan(5000), reason: '$rejected rejected');
    expect(accepted, greaterThan(1000), reason: '$accepted accepted');
  });
}
