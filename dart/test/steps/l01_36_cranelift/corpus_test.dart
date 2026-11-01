/// Every table row of every corpus unit, run natively: each closed term the runner evaluates
/// is lowered, planned, compiled by the JIT and run, and the row still passes; each run
/// allocates and writes counts exactly as the counting machine of L1.34 does.
library;

import 'dart:collection';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/native.dart' as native;
import 'package:zed/run.dart';
import 'package:zed/testing.dart';
import 'package:zed/zir.dart' as zir show plan, run;
import 'package:zed/zir.dart' show ZirError, lower;

import '../l01_21_test_runner/zed_test.dart' show units;

/// A copy of [w] as it is now, so a second run sees the ports as the first did.
World copy(World w) {
  final c = World();
  c.inputs.addAll(w.inputs);
  c.sources.addAll(w.sources);
  for (final MapEntry(:key, :value) in w.outputs.entries) {
    c.outputs[key] = Output(value.capacity)..log.addAll(value.log);
  }
  for (final MapEntry(:key, :value) in w.reads.entries) {
    c.reads[key] = SplayTreeMap.of(value);
  }
  return c;
}

void main() {
  test('every row passes natively with the machine\'s counts', () {
    for (final fuse in [true, false]) {
      var (runs, cells, writes) = (0, 0, 0);
      Value through(Term t, Evaluator ev) {
        try {
          final g = lower(t);
          final p = zir.plan(g, fuse);
          // The machine runs in a copy of the world as it was before the native run.
          final machine = Evaluator(copy(ev.world));
          final o = native.run(g, p, ev);
          final (v, s) = zir.run(g, p, machine);
          final n = o.stats;
          expect(o.value, v, reason: '$t');
          expect(
            (n.increments, n.decrements, n.allocations, n.frees, n.peak, n.shared),
            (s.increments, s.decrements, s.allocations, s.frees, s.peak, s.shared),
            reason: '$t',
          );
          runs++;
          cells += n.allocations;
          writes += n.increments + n.decrements;
          return o.value;
        } on ZirError catch (e) {
          throw RunError(e.message);
        }
      }

      var rows = 0;
      for (final file in units()) {
        final text = file.readAsStringSync();
        final want = testUnit(text);
        final got = testThrough(text, through);
        expect(got.map(_show), want.map(_show), reason: '${file.path} (fuse $fuse)');
        rows += got.length;
      }
      expect(rows, 41);
      expect((runs, cells, writes), (58, 108, fuse ? 112 : 138));
    }
  });
}

String _show(Outcome o) => '${o.line}:${o.col}: ${o.failure}';
