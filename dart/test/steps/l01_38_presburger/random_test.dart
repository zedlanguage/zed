/// The linear-relation domain against the interpreter on random terms over `x` and `y`: the
/// translation of a test holds at exactly the points where the interpreter gives `true`; the
/// Omega test finds a point of the window exactly when one exists, and its model is one; the
/// projection of a relation holds every value a point takes, within the hull of those values;
/// and rung 2 proves no entailment the window refutes, and refutes only with a real
/// countermodel.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart' hide Atom;
import 'package:zed/presburger.dart';
import 'package:zed/store.dart' show relations;

import '../../support/instances.dart';
import 'checks.dart';
import 'support.dart';

void main() {
  test('random tests agree with the interpreter', () {
    final rng = Rng(0x138);
    var (checked, models, entailments) = (0, 0, 0);
    while (checked < 60) {
      final t = boolTerm(rng, 2);
      final rs =
          relations([t], names, false) ??
          (throw StateError('$t: outside the domain, though built from its operators'));
      final r = rs[0];
      expect(checkPoints(r, t, names), isNull);
      final f = whole(r, names);
      final Model? m;
      try {
        m = satisfiable(f);
      } on Over {
        continue;
      }
      final inside = PrimApp(Prim.and, [t, windowTerm(names)]);
      expect(checkModel(m == null ? null : point(m, names), inside, names), isNull);
      if (m != null) models++;
      final claimed = [for (final n in names) project(f, Sym(n))];
      expect(checkProjection(claimed, inside, names), isNull);
      // Rung 2 from the window and this test to a second one.
      final g = boolTerm(rng, 1);
      final pair = relations([inside, g], names, false)!;
      final e = entails(pair[0], pair[1]);
      expect(checkEntailment(e, inside, g, names), isNull);
      if (e is Proved) entailments++;
      checked++;
    }
    // Both answers occur, so neither check passes by never being asked.
    expect(models, inExclusiveRange(10, 55), reason: '$models of 60 satisfiable');
    expect(entailments, inExclusiveRange(3, 57), reason: '$entailments of 60 proved');
  });
}
