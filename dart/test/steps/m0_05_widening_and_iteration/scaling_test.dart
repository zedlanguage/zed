/// Phase 1's work on nested loops (COMPLEXITY.md S3). Each loop of the nest counts up to three
/// times the current upper end of the loop around it, `for j in 0..=3 * i`, and reads the loop
/// inside it, so the order nests every loop in the one around it. When each stabilization
/// restarted its head's counters, every entry of an inner loop gave its head three more joins,
/// and the work grew fourfold per level. Counted over the phase, it still grew as the square
/// of the depth, since every change of an enclosing head entered every inner loop again; a
/// loop none of whose inputs changed is now skipped, and the work is linear.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import '../../support/scaling.dart' as scaling;

/// The successor of each finite end of a piece.
List<Piece> _step(Piece p) => [(p.$1.succ(), p.$2.succ())];

/// `depth` nested counters; cell `k` reads itself, the loop around it and the loop inside it.
final class Nest extends Equations<IntervalSet> {
  @override
  final List<List<int>> reads;
  var evals = 0;

  Nest(int depth)
    : reads = [
        for (var k = 0; k < depth; k++)
          [for (var j = k > 0 ? k - 1 : 0; j < (k + 2 < depth ? k + 2 : depth); j++) j],
      ];

  @override
  IntervalSet get bottom => const IntervalSet.empty();

  @override
  IntervalSet eval(int k, List<IntervalSet> cells) {
    evals++;
    // The bound: 3 for the outermost loop, else three times the loop around it.
    final End bound;
    if (k == 0) {
      bound = const Fin(3);
    } else {
      switch (cells[k - 1].bounds) {
        case null:
          return const IntervalSet.empty();
        case (_, Fin(v: final hi)):
          bound = End.exact(BigInt.from(hi) * BigInt.from(3));
        case (_, final e):
          bound = e;
      }
    }
    final step = cells[k].meet(IntervalSet.range(negInf, bound)).lift1(_step);
    return IntervalSet.single(0).join(step);
  }

  @override
  Landmarks landmarks(int v) => Landmarks.of([0, 3]);
}

int depthOf(List<Element> order) {
  var deepest = 0;
  for (final e in order) {
    if (e case Component(:final body)) {
      final d = 1 + depthOf(body);
      if (d > deepest) deepest = d;
    }
  }
  return deepest;
}

List<Element> orderOf(Equations<IntervalSet> eq) => weakTopologicalOrder(dependencyGraph(eq.reads));

int evals(int depth) {
  final eq = Nest(depth);
  final order = orderOf(eq);
  expect(depthOf(order), depth, reason: 'the loops nest: ${show(order)}');
  phase1(eq, order);
  return eq.evals;
}

/// One counter, `i = 0 ⊔ (i < 10·marks) + 1`, in a program that writes the literals 10, 20,
/// …, 10·marks.
final class Counter extends Equations<IntervalSet> {
  @override
  final reads = [
    [0],
  ];
  final int marks;
  var evals = 0;

  Counter(this.marks);

  @override
  IntervalSet get bottom => const IntervalSet.empty();

  @override
  IntervalSet eval(int v, List<IntervalSet> cells) {
    evals++;
    final step = cells[0].meet(IntervalSet.range(negInf, Fin(10 * marks - 1))).lift1(_step);
    return IntervalSet.single(0).join(step);
  }

  @override
  Landmarks landmarks(int v) => Landmarks.of([for (var k = 1; k <= marks; k++) 10 * k]);
}

/// A counter, `i = 0 ⊔ (i < bound) + 1`, at cell 0, beside cells 1 to `marks`, where cell `k`
/// is the literal `10·k`, below the bound.
final class Beside extends Equations<IntervalSet> {
  @override
  final List<List<int>> reads;
  final int bound;
  var evals = 0;

  Beside(int marks, this.bound)
    : reads = [
        [0],
        for (var k = 0; k < marks; k++) <int>[],
      ];

  @override
  IntervalSet get bottom => const IntervalSet.empty();

  @override
  IntervalSet eval(int v, List<IntervalSet> cells) {
    if (v > 0) return IntervalSet.single(10 * v);
    evals++;
    final step = cells[0].meet(IntervalSet.range(negInf, Fin(bound - 1))).lift1(_step);
    return IntervalSet.single(0).join(step);
  }

  @override
  Landmarks landmarks(int v) => v == 0 ? Landmarks.of([0, bound]) : Landmarks.of([10 * v]);
}

void main() {
  test('nested loops cost linear work in the depth', () {
    // The evaluations per loop stay under a constant at every depth: 15 each past the first
    // (the head stops at each landmark 1 to 4 before it widens to infinity).
    for (var depth = 1; depth <= 48; depth++) {
      expect(evals(depth), lessThanOrEqualTo(16 * depth), reason: 'depth $depth');
    }
  });

  test('the nest scales', () {
    scaling.check('phase 1 on nested loops', 6, evals);
  });

  test('the order of nested loops takes time linear in the depth', () {
    // The recursive algorithm traversed each component again at every level, so its cost grew
    // as the square of the depth (COMPLEXITY.md S9).
    scaling.check('the weak topological order of nested loops', 1000, (d) => orderOf(Nest(d)));
  });

  test('a head stops at most once per landmark', () {
    // The head may stop at each landmark below its fixpoint, so its evaluations grow linearly
    // in the landmarks under it, and not in the gaps between them (COMPLEXITY.md S13).
    for (final marks in [1, 2, 4, 8, 16, 32, 64, 128]) {
      final eq = Counter(marks);
      expect(phase1(eq, orderOf(eq)), [IntervalSet.of(0, 10 * marks)]);
      expect(eq.evals, lessThanOrEqualTo(3 * marks + 1), reason: '$marks landmarks');
    }
  });

  test('a head takes only the landmarks of its loop', () {
    // The literals outside the counter's loop are not places for its head to stop, so its
    // evaluations do not grow with them (COMPLEXITY.md S13). With every literal of the program
    // as a landmark, they grew as 3·marks + 1.
    for (final marks in [1, 2, 4, 8, 16, 32, 64, 128]) {
      final eq = Beside(marks, 10 * marks + 5);
      expect(phase1(eq, orderOf(eq))[0], IntervalSet.of(0, 10 * marks + 5));
      expect(eq.evals, lessThanOrEqualTo(5), reason: '$marks literals beside the loop');
    }
  });
}
