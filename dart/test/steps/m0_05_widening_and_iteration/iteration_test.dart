/// The two-phase iteration against a flattened stack machine, against the concrete least
/// fixpoint, and on the loops whose values the landmarks decide.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';
import 'harness.dart';

/// One instruction of the flattened order.
sealed class Instr {}

/// Join the cell with its projection.
final class Eval extends Instr {
  final int v;
  Eval(this.v);
}

/// The head of the component that ends at instruction `end`.
final class Head extends Instr {
  final int head;
  int end = 0;
  Head(this.head);
}

/// The end of the component whose head is at instruction `start`.
final class EndOf extends Instr {
  final int start;
  EndOf(this.start);
}

void flatten(List<Element> order, List<Instr> out) {
  for (final e in order) {
    switch (e) {
      case Vertex(:final v):
        out.add(Eval(v));
      case Component(:final head, :final body):
        final start = out.length, h = Head(head);
        out.add(h);
        flatten(body, out);
        h.end = out.length;
        out.add(EndOf(start));
    }
  }
}

/// Phase 1 as a machine over the flattened order, with one frame per open component holding
/// its iteration count. A head widens at every change.
List<IntervalSet> machine(System eq) {
  final program = <Instr>[];
  final order = weakTopologicalOrder(dependencyGraph(eq.reads));
  flatten(order, program);
  final marks = Scopes(eq, order);
  final cells = List.filled(eq.init.length, const IntervalSet.empty());
  // Frames: (instruction of the head, iteration).
  final frames = <(int, int)>[];
  var pc = 0;
  while (pc < program.length) {
    switch (program[pc]) {
      case Eval(:final v):
        cells[v] = cells[v].join(eq.eval(v, cells));
        pc++;
      case Head(:final head, :final end):
        if (frames.isEmpty || frames.last.$1 != pc) frames.add((pc, 0));
        final i = frames.last.$2;
        final next = cells[head].join(eq.eval(head, cells));
        if (i > 0 && next == cells[head]) {
          frames.removeLast();
          pc = end + 1;
        } else {
          if (next != cells[head]) cells[head] = cells[head].widen(next, marks.of(head));
          frames.last = (pc, i + 1);
          pc++;
        }
      case EndOf(:final start):
        pc = start;
    }
  }
  return cells;
}

/// `i = 0`, then `i = i + 1` while `i < bound`: the counter of `for i in 0..=bound`.
System counter(int bound) => System(
  [IntervalSet.single(0)],
  [
    [Flow(0, iv(null, bound - 1), 1)],
  ],
);

/// `a = 0 ⊔ c; b = a + 1; c = b ⊓ (-inf, 4]`, with the cells numbered so that `head` is cell
/// 0; returns the system and the cells of a, b and c.
(System, List<int>) threeCellLoop(String head) {
  final ix = switch (head) {
    'a' => [0, 1, 2],
    'b' => [2, 0, 1],
    _ => [1, 2, 0],
  };
  final [a, b, c] = ix;
  final init = List.filled(3, const IntervalSet.empty());
  final terms = [<Flow>[], <Flow>[], <Flow>[]];
  init[a] = IntervalSet.single(0);
  terms[a].add(Flow(c, IntervalSet.top(), 0));
  terms[b].add(Flow(a, IntervalSet.top(), 1));
  terms[c].add(Flow(b, iv(null, 4), 0));
  return (System(init, terms), ix);
}

/// The counter followed by a chain of five copies of it.
System counterAndCopies() => System(
  [IntervalSet.single(0), for (var v = 1; v <= 5; v++) const IntervalSet.empty()],
  [
    counter(99).terms[0],
    for (var v = 1; v <= 5; v++) [Flow(v - 1, IntervalSet.top(), 0)],
  ],
).bare();

/// `depth` nested loops, cell `k` reading the loop around it, itself and the loop inside it,
/// and writing the literal `100·k`.
final class Levels extends Equations<IntervalSet> {
  @override
  final List<List<int>> reads;

  Levels(this.reads);

  @override
  IntervalSet get bottom => const IntervalSet.empty();

  @override
  IntervalSet eval(int v, List<IntervalSet> cells) => const IntervalSet.empty();

  @override
  Landmarks landmarks(int v) => Landmarks.of([100 * v]);
}

List<Element> orderOf(Equations<IntervalSet> eq) => weakTopologicalOrder(dependencyGraph(eq.reads));

void main() {
  test('phase one agrees with the stack machine', () {
    final rng = Rng(0x1e7);
    for (var i = 0; i < randomInstances; i++) {
      final e = System.random(rng);
      for (final eq in [e, e.bare()]) {
        expect(phase1(eq, orderOf(eq)), machine(eq), reason: '$eq');
      }
    }
  });

  test('both phases end at a sound post-fixpoint', () {
    // Phase 1 ends at a post-fixpoint; phase 2 keeps it one; and the result contains every
    // value of every execution that stays in a window around the constants.
    final rng = Rng(0x50d);
    var narrowed = 0;
    for (var i = 0; i < randomInstances; i++) {
      final e = System.random(rng);
      final eq = rng.below(2) == 0 ? e : e.bare();
      final order = orderOf(eq);
      final cells = phase1(eq, order);
      expect(isPostFixpoint(eq, cells), isTrue, reason: 'phase 1: $eq');
      final before = [...cells];
      if (narrow(eq, order, cells) > 0) narrowed++;
      expect(isPostFixpoint(eq, cells), isTrue, reason: 'phase 2: $eq');
      final concrete = eq.concrete(-40, 40);
      for (var v = 0; v < concrete.length; v++) {
        expect(cells[v].isSubset(before[v]), isTrue);
        for (final x in concrete[v]) {
          expect(cells[v].contains(x), isTrue, reason: 'cell $v lost $x: $eq');
        }
      }
    }
    expect(narrowed, greaterThan(randomInstances ~/ 10), reason: 'phase 2 changed few systems');
  });

  test('a counter stops at its landmarks in phase one', () {
    // The guard `i < bound` gives the landmarks `bound - 2..=bound`, so the widening stops the
    // counter's upper end there, at any bound, with no delay.
    const order = [Component(0, [])];
    for (final bound in [2, 3, 99, 1000000]) {
      expect(phase1(counter(bound), order), [iv(0, bound)]);
    }
    // With no landmarks the end goes to infinity, and phase 2 brings it back: an infinite end
    // may take a finite bound once.
    expect(phase1(counter(99).bare(), order), [iv(0, null)]);
    expect(solve(counter(99).bare()), [iv(0, 99)]);
  });

  test('the widening point changes the phase one values', () {
    // Phase 1's result depends on where the loop is cut, which is why the traversal is fixed.
    // Cut at a, the bound on c survives widening; cut at c, it does not.
    (List<String>, List<String>) run(String head) {
      final (eq, ix) = threeCellLoop(head);
      final cells = phase1(eq.bare(), orderOf(eq));
      final solved = solve(eq.bare());
      return ([for (final v in ix) '${cells[v]}'], [for (final v in ix) '${solved[v]}']);
    }

    final (atA, solvedA) = run('a');
    final (atC, solvedC) = run('c');
    expect(atA, ['[0..]', '[1..]', '[1..=4]']);
    expect(atC, ['[0..]', '[1..]', '[1..]']);
    // Phase 2 recovers the same values from both.
    expect(solvedA, ['[0..=4]', '[1..=5]', '[1..=4]']);
    expect(solvedC, solvedA);
  });

  test('phase two runs until a round changes nothing', () {
    // With no landmarks, phase 1 leaves every cell at [0..]. Narrowing the counter takes one
    // round, and each copy one more: phase 2 runs all six rounds, with no budget to stop it.
    final eq = counterAndCopies();
    final order = orderOf(eq);
    final cells = phase1(eq, order);
    expect(cells, everyElement(iv(0, null)));
    expect(narrow(eq, order, cells), 6);
    expect(cells, everyElement(iv(0, 99)));
    expect(isPostFixpoint(eq, cells), isTrue);
  });

  test('phase two ends where meets alone would descend forever', () {
    // `x = x + 1` from [0..]: [0..] is a post-fixpoint, and meeting it with the projection
    // gives [1..], [2..], ... without end. The narrowing moves the new lower end back to the
    // old one, so phase 2 changes nothing and ends.
    final eq = System(
      [const IntervalSet.empty()],
      [
        [Flow(0, IntervalSet.top(), 1)],
      ],
    );
    final start = [iv(0, null)];
    expect(isPostFixpoint(eq, start), isTrue);
    expect(start[0].meet(eq.eval(0, start)), iv(1, null));
    final cells = [...start];
    expect(narrow(eq, orderOf(eq), cells), 0);
    expect(cells, start);
  });

  test('a loop with no landmark ends without a cap', () {
    // A counter whose guard is not written anywhere the equations see: the head widens to
    // [0..] at its first change past the old bound, and phase 1 ends after a few evaluations,
    // at any bound.
    for (final bound in [10, 1000000000]) {
      final eq = counter(bound).bare();
      expect(phase1(eq, orderOf(eq)), [iv(0, null)]);
      expect(solve(eq), [iv(0, bound)]);
    }
  });

  test('equations are read through the interface', () {
    // The store calls the equations only through `Equations`; a system that reads nothing is
    // its initial values.
    final eq = System([IntervalSet.of(3, 4)], [<Flow>[]]);
    expect(eq.reads[0], isEmpty);
    expect(solve(eq), [IntervalSet.of(3, 4)]);
    expect(eq.bottom, const IntervalSet.empty());
  });

  test('a loop takes the landmarks of the loops inside it only', () {
    // A guard of an inner loop bounds what flows out to the heads around it, so each head
    // takes the literals of its loop and of every loop inside it, and none from outside.
    const depth = 5;
    final eq = Levels([
      for (var k = 0; k < depth; k++)
        [for (var j = k > 0 ? k - 1 : 0; j < (k + 2 < depth ? k + 2 : depth); j++) j],
    ]);
    final scopes = Scopes(eq, orderOf(eq));
    for (var k = 0; k < depth; k++) {
      expect(scopes.of(k).ints, [
        for (var j = k; j < depth; j++) ...[100 * j - 1, 100 * j, 100 * j + 1],
      ], reason: 'cell $k');
    }
  });
}
