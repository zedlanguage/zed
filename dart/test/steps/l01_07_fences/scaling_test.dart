/// Extracting fences and reading their marks and labels are of order n log n in the length of
/// the document (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/fence.dart';

import '../../support/scaling.dart';

void main() {
  test('many fences', () {
    const one = 'Text.\n\n```zed\n// layer L3\nx = 1;   // ✗ no\n// y = 2; // ✗ variant\n```\n';
    check('extract, marks and label', 1000, (n) {
      final fences = extract(one * n);
      expect(fences, hasLength(n));
      for (final f in fences) {
        expect((marks(f.text).lines.length, label(f.text)), (1, 3));
      }
    });
  });

  test('one long fence', () {
    check('extract, marks and label', 2000, (n) {
      final f = extract('```zed\n${'// layer L2\nx = 1; // ✗\n' * n}')[0];
      expect((marks(f.text).lines.length, label(f.text)), (n, 2));
    });
  });
}
