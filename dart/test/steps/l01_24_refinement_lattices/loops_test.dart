/// The equations of loops over symbolic bounds, solved with the M0.5 strategy, against the
/// values a run takes at each symbol value.
library;

import 'dart:collection';

import 'package:test/test.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';
import 'support.dart';

/// One term of a cell's transfer: `(cell[from] ⊓ guard) + step`.
typedef Term = ({int from, Bounds guard, int step});

/// `cell[v] = init[v] ⊔ ⋃ terms[v]`: a loop's counter starts at `init` and moves by `step`
/// while `guard` holds.
final class System extends Equations<Bounds> {
  final List<Bounds> init;
  final List<List<Term>> terms;
  @override
  final List<List<int>> reads;

  System(this.init, this.terms)
    : reads = [for (final ts in terms) SplayTreeSet.of(ts.map((t) => t.from)).toList()];

  /// The values each cell takes in a run at `env` that stays in the window.
  List<Set<int>> run(Env env) {
    final f = at(env);
    final cells = [for (final _ in init) <int>{}];
    for (var changed = true; changed;) {
      changed = false;
      for (var v = 0; v < init.length; v++) {
        final next = {
          for (final x in window)
            if (init[v].contains(x, f)) x,
          for (final t in terms[v])
            for (final x in cells[t.from])
              if (t.guard.contains(x, f) && x + t.step >= window.first && x + t.step <= window.last)
                x + t.step,
        };
        if (next.length != cells[v].length || !next.containsAll(cells[v])) {
          cells[v] = next;
          changed = true;
        }
      }
    }
    return cells;
  }

  @override
  Bounds get bottom => Bounds.bottom;

  @override
  Bounds eval(int v, List<Bounds> cells) =>
      terms[v].fold(init[v], (acc, t) => acc.join(cells[t.from].meet(t.guard).offset(t.step)));

  /// The integer ends of cell `v`'s initial value and guards.
  @override
  Landmarks landmarks(int v) => Landmarks.of([
    for (final b in [init[v], for (final t in terms[v]) t.guard])
      for (final (lo, hi) in b.concrete.pieces)
        for (final e in [lo, hi])
          if (e case Fin(:final v)) v,
  ]);

  @override
  String toString() => 'System($init, $terms)';
}

final n = Affine.sym('n');

Bounds num(int c) => Bounds.ints(IntervalSet.single(c));

void main() {
  test('a counting loop keeps its symbolic bound', () {
    // `for i in 0..<n`: `i = 0 ⊔ (i ⊓ [..=n - 1]) + 1`, and the index the body sees,
    // `j = i ⊓ [..=n - 1]`.
    final belowN = Bounds.range(null, n.plus(-1));
    final cells = solve(
      System(
        [num(0), Bounds.bottom],
        [
          [(from: 0, guard: belowN, step: 1)],
          [(from: 0, guard: belowN, step: 0)],
        ],
      ),
    );
    // After the loop the counter is `n`, or 0 when `n` is not positive.
    expect(cells[0].toString(), '[0..=max(0, n)]');
    // In the body it is `int[0..<n]`.
    expect(cells[1].toString(), '[0..=n - 1]');
  });

  test('a loop counting down keeps its symbolic bound', () {
    // `i = n - 1; while i >= 1 { i = i - 1 }`, and the index the body sees.
    final atLeast1 = Bounds.range(const Affine.constant(1), null);
    final cells = solve(
      System(
        [Bounds.range(n.plus(-1), n.plus(-1)), Bounds.bottom],
        [
          [(from: 0, guard: atLeast1, step: -1)],
          [(from: 0, guard: atLeast1, step: 0)],
        ],
      ),
    );
    expect(cells[0].toString(), '[min(0, n - 1)..=n - 1]');
    expect(cells[1].toString(), '[1..=n - 1]');
  });

  test('every solution holds every value a run takes', () {
    final rng = Rng(0x1243);
    var symbolic = 0;
    for (var i = 0; i < randomInstances ~/ 4; i++) {
      final cells = 1 + rng.below(4);
      final init = [for (var c = 0; c < cells; c++) randomBounds(rng)];
      final terms = [
        for (var c = 0; c < cells; c++)
          [
            for (var k = rng.below(3); k > 0; k--)
              (from: rng.below(cells), guard: randomBounds(rng), step: rng.int_(-2, 2)),
          ],
      ];
      final s = System(init, terms);
      final solved = solve(s);
      symbolic += solved.where((c) => c.toString().contains('n')).length;
      for (final env in envs) {
        final run = s.run(env);
        for (var v = 0; v < run.length; v++) {
          for (final x in run[v]) {
            if (!solved[v].contains(x, at(env))) {
              fail('cell $v takes $x at $env, outside ${solved[v]}: $s');
            }
          }
        }
      }
    }
    // The solutions keep symbolic bounds, so the check above tests them.
    expect(symbolic, greaterThan(0));
  });
}
