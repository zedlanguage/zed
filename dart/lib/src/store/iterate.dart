/// The store's iteration strategy (DESIGN.md sec:constraints rule 1, fixed by step M0.5).
///
/// Phase 1 computes a post-fixpoint by forward projections only: Bourdoncle's recursive
/// strategy over the weak topological order of the dependency graph, joining at every cell
/// and widening at the heads of components. Phase 2 then narrows that post-fixpoint in rounds:
/// in each round every cell is narrowed by its meet with its projection computed from the
/// state at the start of the round, until a round changes nothing. Both phases end because
/// the widening and the narrowing move bounds only to landmarks and to values already present
/// (lattice.dart), so no delay, no bound on a head's changes and no budget of rounds enters.
/// A cell's landmarks are those of its loop ([Scopes]), so a head stops only at values
/// written in its loop.
library;

import 'lattice.dart';
import 'wto.dart';

/// A system of equations over a lattice: one cell per vertex, `0..n` in source order.
abstract class Equations<L extends Lattice<L>> {
  /// For each cell, the cells its projection reads, in source order.
  List<List<int>> get reads;

  /// The least element of the lattice, where every cell starts.
  L get bottom;

  /// The forward projection into cell `v` from the current cells.
  L eval(int v, List<L> cells);

  /// The values written in the equation of cell `v`, where a widening or a narrowing may
  /// stop a bound.
  Landmarks landmarks(int v);
}

/// The dependency graph: an edge from `u` to every cell that reads `u`, the successors in
/// source order.
List<List<int>> dependencyGraph(List<List<int>> reads) {
  final succ = [for (var v = 0; v < reads.length; v++) <int>[]];
  for (var v = 0; v < reads.length; v++) {
    for (final u in reads[v]) {
      succ[u].add(v);
    }
  }
  // Each list was filled in increasing `v`, so it is sorted; only repeats go.
  return [
    for (final s in succ)
      [
        for (var i = 0; i < s.length; i++)
          if (i == 0 || s[i] != s[i - 1]) s[i],
      ],
  ];
}

/// Phase 1 and then phase 2, from every cell at the bottom.
List<L> solve<L extends Lattice<L>>(Equations<L> eq) {
  final order = weakTopologicalOrder(dependencyGraph(eq.reads));
  final cells = phase1(eq, order);
  narrow(eq, order, cells);
  return cells;
}

/// The landmarks each cell's widening and narrowing take (COMPLEXITY.md S13). A cell in a
/// loop takes those of every equation of its innermost component, nested components included,
/// since a guard of an inner loop bounds what flows out to the heads around it; a cell in no
/// loop takes those of its own equation. So a head stops only at values written in its loop,
/// not at every literal of the program. Building them takes time and space linear in the sum,
/// over the components, of the landmarks each holds, which is at most the landmarks times the
/// depth of nesting.
final class Scopes {
  /// The set of each cell; the cells of one component share one set.
  final List<Landmarks> _of;

  /// The sets of the cells, for the order of the system's dependency graph.
  Scopes(Equations<dynamic> eq, List<Element> order)
    : _of = List.filled(eq.reads.length, Landmarks.none()) {
    for (final element in order) {
      switch (element) {
        case Vertex(:final v):
          _of[v] = eq.landmarks(v);
        case Component(:final head, :final body):
          _component(eq, head, body);
      }
    }
  }

  /// Gives the component headed by `head`, and each one inside it, its set, and returns its
  /// own.
  Landmarks _component(Equations<dynamic> eq, int head, List<Element> body) {
    final marks = Landmarks.none()..extend(eq.landmarks(head));
    _of[head] = marks;
    for (final element in body) {
      switch (element) {
        case Vertex(:final v):
          marks.extend(eq.landmarks(v));
          _of[v] = marks;
        case Component(:final head, :final body):
          marks.extend(_component(eq, head, body));
      }
    }
    return marks;
  }

  /// The landmarks of cell `v`.
  Landmarks of(int v) => _of[v];
}

/// Phase 1 over the given order, from every cell at the bottom.
List<L> phase1<L extends Lattice<L>>(Equations<L> eq, List<Element> order) {
  final w = _Walk(eq, order);
  w.number(order, null);
  w.stabilize(order);
  return w.cells;
}

/// The state of phase 1. Components are named by their heads. `dirty[h]` says whether a cell
/// that the component reads from outside it has changed since the component last
/// stabilized; a clean component is skipped, which changes nothing, since its cells are then
/// a post-fixpoint of its own equations (in a weak topological order every edge back into the
/// component's cells goes to a head inside it). So a component is stabilized once per change
/// of a cell it reads from outside, not once per change of every enclosing head, and nested
/// loops cost work linear in their number, where restarted counters made it exponential in
/// the depth.
final class _Walk<L extends Lattice<L>> {
  final Equations<L> eq;
  final List<L> cells;
  final Scopes marks;
  final List<bool> dirty;
  final List<List<int>> succ;

  /// Each vertex's place in the flattened order; a component's vertices are the places from
  /// its head's to `end[head]`.
  final List<int> pos, end;

  /// The enclosing component of a component.
  final List<int?> parent;

  /// The innermost component holding a vertex (for a head, its own).
  final List<int?> inner;

  var _at = 0;

  _Walk(this.eq, List<Element> order)
    : cells = List.filled(eq.reads.length, eq.bottom),
      marks = Scopes(eq, order),
      dirty = List.filled(eq.reads.length, true),
      succ = dependencyGraph(eq.reads),
      pos = List.filled(eq.reads.length, 0),
      end = List.filled(eq.reads.length, 0),
      parent = List.filled(eq.reads.length, null),
      inner = List.filled(eq.reads.length, null);

  void number(List<Element> order, int? within) {
    for (final element in order) {
      switch (element) {
        case Vertex(:final v):
          pos[v] = _at++;
          inner[v] = within;
        case Component(:final head, :final body):
          pos[head] = _at++;
          inner[head] = head;
          parent[head] = within;
          number(body, head);
          end[head] = _at - 1;
      }
    }
  }

  bool holds(int c, int u) => pos[c] <= pos[u] && pos[u] <= end[c];

  /// Sets cell `v`; on a change, every component that reads `v` from outside it is dirty.
  void set(int v, L value) {
    if (value == cells[v]) return;
    assert(cells[v].leq(value), 'phase 1 fell at cell $v');
    cells[v] = value;
    for (final s in succ[v]) {
      for (var c = inner[s]; c != null && !holds(c, v); c = parent[c]) {
        dirty[c] = true;
      }
    }
  }

  void stabilize(List<Element> order) {
    for (final element in order) {
      switch (element) {
        case Vertex(:final v):
          set(v, cells[v].join(eq.eval(v, cells)));
        case Component(head: final h, :final body):
          if (!dirty[h]) continue;
          for (var i = 0; ; i++) {
            final next = cells[h].join(eq.eval(h, cells));
            if (i > 0 && next == cells[h]) break;
            if (next != cells[h]) set(h, cells[h].widen(next, marks.of(h)));
            stabilize(body);
          }
          dirty[h] = false;
      }
    }
  }
}

/// Phase 2: rounds of narrowing every cell by its meet with its projection from the state at
/// the start of the round, until a round changes nothing. Each cell's values form a chain of
/// narrowings, which is finite, so the rounds end. Returns the number of rounds that changed
/// a cell. `order` is the order of the system's dependency graph, which places the landmarks.
int narrow<L extends Lattice<L>>(Equations<L> eq, List<Element> order, List<L> cells) {
  final marks = Scopes(eq, order);
  for (var round = 0; ; round++) {
    final next = [
      for (var v = 0; v < cells.length; v++)
        cells[v].narrow(cells[v].meet(eq.eval(v, cells)), marks.of(v)),
    ];
    var changed = false;
    for (var v = 0; v < cells.length; v++) {
      assert(next[v].leq(cells[v]), 'phase 2 rose at cell $v');
      if (next[v] != cells[v]) changed = true;
    }
    if (!changed) return round;
    cells.setAll(0, next);
  }
}
