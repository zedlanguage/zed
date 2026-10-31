/// Loading is of order n log n in the bytes of the file, NFC or not, and so is placing every
/// offset of it (DESIGN.md Part G).
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/source.dart';

import '../../support/scaling.dart';

void main() {
  test('NFC text with line breaks of every kind', () {
    check('load', 4000, (n) {
      final line = utf8.encode('q\u0307me = "Jos\u00e9 \ud55c";\r\n// \u1ea1\u0301\r');
      load([for (var i = 0; i < n; i++) ...line]);
    });
  });

  test('one base with a long run of marks of mixed classes', () {
    // NFC sorts the run by class; the first non-NFC piece is the whole run.
    check('load', 4000, (n) {
      final marks = [for (var i = 0; i < n; i++) i.isEven ? 0x301 : 0x323];
      expect(
        () => load(utf8.encode(String.fromCharCodes([0x78, ...marks]))),
        throwsA(isA<NotNfc>()),
      );
    });
  });

  test('a rejection late in a long file', () {
    check('load', 4000, (n) {
      final bytes = [for (var i = 0; i < n; i++) ...utf8.encode('a\u0303 = 1;\n'), 0xff];
      expect(() => load(bytes), throwsA(isA<NotUtf8>()));
    });
  });

  test('placing every offset', () {
    check('lines', 4000, (n) {
      final bytes = utf8.encode('ab\u00e9\r\n' * n);
      final lines = Lines(bytes);
      for (var i = 0; i < bytes.length; i++) {
        lines.lineStart(i);
      }
    });
  });
}
