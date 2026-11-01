/// Every table row of every corpus unit, waves included, run through ZIR: each closed term the
/// runner evaluates is lowered, validated and raised back, and the row still passes.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/run.dart';
import 'package:zed/testing.dart';
import 'package:zed/zir.dart' hide print;

import '../l01_21_test_runner/zed_test.dart' show units;

void main() {
  test('every row passes through ZIR', () {
    var (lowered, ported) = (0, 0);
    Value through(Term t, Evaluator ev) {
      final Region g;
      try {
        g = lower(t);
        validate(g);
      } on ZirError catch (e) {
        throw RunError(e.message);
      }
      lowered++;
      if (g.args.isNotEmpty) ported++;
      return direct(raise(g), ev);
    }

    var rows = 0;
    for (final file in units()) {
      final text = file.readAsStringSync();
      final want = testUnit(text);
      final got = testThrough(text, through);
      expect(got.map(_show), want.map(_show), reason: file.path);
      rows += got.length;
    }
    // The seven corpus units hold 41 checks, which evaluate 58 closed terms; the 11 waves
    // among them lower to port regions. A runner that skipped the map would pass the
    // comparison above.
    expect(rows, 41);
    expect((lowered, ported), (58, 11));
  });
}

String _show(Outcome o) => '${o.line}:${o.col}: ${o.failure}';
