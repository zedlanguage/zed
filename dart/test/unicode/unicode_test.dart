/// The NFC of `lib/src/unicode.dart` against the conformance test of the Unicode Character
/// Database, `NormalizationTest.txt` of the version the tables are of.
library;

import 'dart:convert';
import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/src/unicode.dart';
import 'package:zed/src/unicode_tables.dart';

import '../support/support.dart';

List<int> _cps(String field) => [for (final w in field.split(' ')) int.parse(w, radix: 16)];

void main() {
  final lines = const LineSplitter().convert(
    utf8.decode(
      gzip.decode(
        File('${packageDir.path}/test/unicode/NormalizationTest.txt.gz').readAsBytesSync(),
      ),
    ),
  );

  test('the test file is of the tables\' version', () {
    expect(lines.first, '# NormalizationTest-$unicodeVersion.txt');
  });

  test('every line of the conformance test holds', () {
    // c2 == NFC(c1) == NFC(c2) == NFC(c3), and c4 == NFC(c4) == NFC(c5).
    var n = 0;
    final listed = <int>{};
    for (final line in lines) {
      if (line.startsWith('#') || line.startsWith('@')) continue;
      final c = [for (final f in line.split(';').take(5)) _cps(f)];
      if (c[0].length == 1) listed.add(c[0][0]);
      for (final (i, want) in [(0, 1), (1, 1), (2, 1), (3, 3), (4, 3)]) {
        expect(nfc(c[i]), c[want], reason: line);
      }
      expect(isNfc(c[1]), isTrue, reason: line);
      n++;
    }
    expect(n, greaterThan(19000));
    // Part 1 lists every code point that normalization changes; the rest are their own NFC.
    for (var cp = 0; cp < 0x110000; cp++) {
      if ((cp < 0xd800 || cp > 0xdfff) && !listed.contains(cp)) {
        expect(nfc([cp]), [cp], reason: cp.toRadixString(16));
      }
    }
  });

  test('combining classes', () {
    expect(combiningClass(0x61), 0);
    expect(combiningClass(0x301), 230);
    expect(combiningClass(0x323), 220);
    expect(combiningClass(0x334), 1);
    expect(combiningClass(0x10ffff), 0);
  });
}
