/// Every table row of every corpus unit, waves included, run by the counting machine: each
/// closed term the runner evaluates is lowered, planned and run with its counts checked after
/// every node, and the row still passes.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/run.dart';
import 'package:zed/testing.dart';
import 'package:zed/zir.dart' as zir show plan, run;
import 'package:zed/zir.dart' show ZirError, lower;

import '../l01_21_test_runner/zed_test.dart' show units;

void main() {
  test('every row passes through the machine', () {
    for (final fuse in [true, false]) {
      var (runs, cells, writes) = (0, 0, 0);
      Value through(Term t, Evaluator ev) {
        try {
          final g = lower(t);
          final (v, s) = zir.run(g, zir.plan(g, fuse), ev);
          runs++;
          cells += s.allocations;
          writes += s.writes;
          return v;
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
      // The seven corpus units evaluate 58 closed terms, which allocate 108 cells; fusion
      // saves 26 count writes.
      expect((runs, cells, writes), (58, 108, fuse ? 112 : 138));
    }
  });

  // A function that pushes and is called twice runs as one closure whose calls thread the
  // state: the machine's counts check, and the value and the pushes are the kernel's.
  test('a function that pushes and is called twice passes through the machine', () {
    final say = lam([
      'm',
    ], let_('_', Push('stdout', var_('m')), prim(Prim.concat, [var_('m'), lit('!')])));
    final t = let_(
      'say',
      say,
      prim(Prim.tuple, [
        app(var_('say'), [lit('a')]),
        app(var_('say'), [lit('b')]),
      ]),
    );
    final g = lower(t);
    for (final fuse in [true, false]) {
      World world() => World().output('stdout');
      final ev = Evaluator(world());
      final (v, _) = zir.run(g, zir.plan(g, fuse), ev);
      final kev = Evaluator(world());
      expect(v, kev.run(t));
      expect(ev.world.log('stdout'), kev.world.log('stdout'));
      expect(ev.world.log('stdout').length, 2);
    }
  });
}

String _show(Outcome o) => '${o.line}:${o.col}: ${o.failure}';
