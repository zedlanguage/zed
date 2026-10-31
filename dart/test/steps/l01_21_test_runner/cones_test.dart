/// The definitions a row reads: those its terms name, and those they name in turn.
library;

import 'package:test/test.dart';
import 'package:zed/elab.dart';
import 'package:zed/kernel.dart';

import '../../support/instances.dart';
import '../l01_16_elaboration/elab.dart';

/// The cone by one backward pass over the unit, each definition after those it uses.
List<int> byScan(Unit unit, List<Term> roots) {
  final reach = {for (final t in roots) ...free(t)};
  final out = <int>[];
  for (var i = unit.defs.length - 1; i >= 0; i--) {
    if (reach.contains(unit.defs[i].kernel)) {
      reach.addAll(free(unit.defs[i].term));
      out.add(i);
    }
  }
  return out.reversed.toList();
}

void main() {
  test('the cone is the definitions a scan of the unit reaches', () {
    final rng = Rng(0x121c);
    for (var k = 0; k < randomInstances ~/ 8; k++) {
      final n = 1 + rng.below(8);
      // Each `ci` names some of the constants before it.
      final text = [
        for (var i = 0; i < n; i++)
          'c$i = 1 + ${['0', for (var j = 0; j < i; j++)
            if (rng.below(3) == 0) 'c$j'].join(' + ')};\n',
      ].join();
      final unit = elab(text);
      final cones = Cones(unit);
      for (var r = 0; r < 4; r++) {
        final root = unit.defs[rng.below(unit.defs.length)].term;
        final other = unit.defs[rng.below(unit.defs.length)].term;
        for (final roots in [
          [root],
          [root, other],
          <Term>[],
        ]) {
          expect(cones.reach(roots), byScan(unit, roots), reason: text);
        }
      }
    }
  });

  test("a term is closed over its cone alone, in the unit's order", () {
    final unit = elab('a = 1;\nb = a + 1;\nc = 5;\nd = b + a;\n');
    String kernel(String n) => unit.defs.firstWhere((d) => d.name == n).kernel;
    final closed = Cones(unit).close(Var(kernel('d')));
    final lets = <String>[];
    for (var t = closed; t is Let; t = t.body) {
      lets.add(t.name);
    }
    expect(lets, [kernel('a'), kernel('b'), kernel('d')]);
    expect('${unit.close(Var(kernel('d')))}', '$closed');
  });
}
