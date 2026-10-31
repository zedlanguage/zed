/// The enabled fences run.
library;

import 'package:test/test.dart';
import 'package:zed/testing.dart';

import '../../support/fences.dart' as fences;

void main() {
  // Each fence of layer L1 passes its checks but for what a fragment leaves to the text around
  // it, a name it does not bind. A fence with such a name is not elaborated, so its ✗ marks are
  // not checked.
  test('every L1 fence passes but for its free names', () {
    final clean = <(String, int)>[];
    for (final f in fences.all().where((f) => f.layer <= 1 && !f.notation)) {
      final outcomes = testUnit(f.text);
      final failures = <String>[for (final o in outcomes) ?o.failure];
      bool free(String w) => w.endsWith('is not defined');
      if (failures.isEmpty) {
        clean.add((f.at, outcomes.length));
        continue;
      }
      bool unchecked(String w) => w == 'the line is marked ✗ and has no diagnostic';
      expect(
        failures.any(free) && failures.every((w) => free(w) || unchecked(w)),
        isTrue,
        reason: '${f.at}: $failures',
      );
    }
    // The rebinding fence checks its one mark; the lambda fence binds every name it uses.
    expect(clean, [('EXAMPLES.md:78', 1), ('EXAMPLES.md:203', 0)]);
  });
}
