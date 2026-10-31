/// The full case mappings of `lib/src/unicode.dart`, which `lower` and `upper` are (DESIGN.md
/// step L1.18): the mappings longer than one character, the final sigma, and the cost of the
/// final sigma's scans.
library;

import 'package:test/test.dart';
import 'package:zed/src/unicode.dart';

import '../support/scaling.dart';

void main() {
  test('the example of the design: upper("straße") is "STRASSE"', () {
    expect(toUpper('straße'), 'STRASSE');
  });

  test('mappings longer than one character', () {
    expect(toLower('İ'), 'i̇');
    expect(toUpper('ﬃ'), 'FFI');
    expect(toUpper('ŉ'), 'ʼN');
    expect(toUpper('ΐ'), 'Ϊ́');
  });

  test('a capital sigma lowercases to the final form only at the end of a word', () {
    for (final (from, to) in [
      ('ΑΣ', 'ας'),
      ('Σ', 'σ'),
      ('ΑΣΑ', 'ασα'),
      ('ΑΣ.', 'ας.'),
      ('Α.Σ', 'α.ς'),
      ("ΑΣ'Α", "ασ'α"),
      ("Α'Σ'", "α'ς'"),
      ('ΣΣ', 'σς'),
      ('ΑΣΣ', 'ασς'),
      ('áΣ', 'áς'),
      ('1Σ', '1σ'),
      ('ΑΣ1', 'ας1'),
    ]) {
      expect(toLower(from), to, reason: from);
    }
  });

  test('uppercasing leaves every sigma capital', () {
    expect(toUpper('ας σ'), 'ΑΣ Σ');
  });

  test('the final sigma scans each character a bounded number of times', () {
    check('toLower', 2000, (n) {
      expect(toLower("Α${"'" * 50}Σ" * n), hasLength(52 * n));
    });
    check('toLower', 2000, (n) {
      expect(toLower('Α${"'" * n}Σ${"'" * n}'), hasLength(2 * n + 2));
    });
  });
}
