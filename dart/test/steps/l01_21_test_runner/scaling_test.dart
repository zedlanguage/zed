/// The runner at the rule of low complexity (DESIGN.md Part G). Keying each row by a scan of
/// every definition of the unit and running it under all of them as lets would make a unit of
/// `n` functions with a row each take `O(n²)`; a row reads only the definitions it reaches.
library;

import 'package:test/test.dart';
import 'package:zed/testing.dart';

import '../../support/scaling.dart' as scaling;

/// `n` functions, each with one row, beside a constant each that no row reads.
String tables(int n) => [
  for (var i = 0; i < n; i++) 'c$i = $i * 2;\nf$i(positional x) = x + $i test { 1 -> ${i + 1} }\n',
].join();

void main() {
  test("running the rows of many tables scales", () {
    final texts = <int, String>{};
    scaling.check("running n functions' rows", 100, (n) {
      final got = testUnit(texts[n] ??= tables(n));
      expect(got, hasLength(n));
      expect(got.every((Outcome o) => o.failure == null), isTrue, reason: got.first.failure);
    });
  });
}
