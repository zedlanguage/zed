/// Step M0.5: widening and iteration.
///
/// The store's iteration (DESIGN.md sec:constraints rule 1) is fixed down to the traversal: the
/// weak topological order of the dependency graph, the widening points, the two phases, the
/// landmarks at which a widening or a narrowing stops a bound, and the tonicity and
/// interval-revision tables. Each piece is checked against an independent implementation
/// written here from the definition: `wto` against the declarative definition of the order,
/// `iteration` against a flattened stack machine and against the concrete least fixpoint,
/// `widening` for the termination bound of every lattice, and `revision` on constraints from
/// ordinary programs. This file holds what they share.
library;

import 'package:zed/store.dart';

import '../../support/instances.dart';

/// One term of a cell's transfer: `(cell[from] ⊓ filter) + offset`.
final class Flow {
  final int from;
  final IntervalSet filter;
  final int offset;

  const Flow(this.from, this.filter, this.offset);

  @override
  String toString() => '($from ⊓ $filter) + $offset';
}

/// A system of interval equations, `cell[v] = init[v] ⊔ ⋃ terms[v]`: the shape the store's
/// equations take for loop counters, accumulators and bounds checks.
final class System extends Equations<IntervalSet> {
  final List<IntervalSet> init;
  final List<List<Flow>> terms;
  @override
  final List<List<int>> reads;

  /// Whether the equations give no landmarks, as if the program wrote no bound.
  final bool isBare;

  System(this.init, this.terms, {this.isBare = false})
    : reads = [
        for (final ts in terms) ({for (final t in ts) t.from}.toList()..sort()),
      ];

  /// The same equations with no landmarks.
  System bare() => System(init, terms, isBare: true);

  /// A random system of up to 8 cells, each reading up to 3 cells.
  factory System.random(Rng rng) {
    final n = 1 + rng.below(8);
    final init = <IntervalSet>[];
    final terms = <List<Flow>>[];
    for (var v = 0; v < n; v++) {
      if (rng.below(3) == 0) {
        init.add(const IntervalSet.empty());
      } else {
        final lo = rng.int_(-5, 5);
        init.add(IntervalSet.of(lo, lo + rng.int_(0, 3)));
      }
      terms.add([
        for (var i = rng.below(4); i > 0; i--)
          Flow(rng.below(n), randomFilter(rng), rng.int_(-2, 2)),
      ]);
    }
    return System(init, terms);
  }

  /// The concrete least fixpoint over sets of integers, cut to `lo..=hi`: every value a cell
  /// takes in an execution that stays in the window. The cut makes it a subset of the true
  /// least fixpoint, so it is a lower bound that every sound solution contains.
  List<Set<int>> concrete(int lo, int hi) {
    final cells = [for (var v = 0; v < init.length; v++) <int>{}];
    for (var changed = true; changed;) {
      changed = false;
      for (var v = 0; v < init.length; v++) {
        final next = {
          for (var x = lo; x <= hi; x++)
            if (init[v].contains(x)) x,
        };
        for (final t in terms[v]) {
          for (final x in cells[t.from]) {
            final y = x + t.offset;
            if (t.filter.contains(x) && lo <= y && y <= hi) next.add(y);
          }
        }
        if (next.length != cells[v].length || !next.containsAll(cells[v])) {
          cells[v] = next;
          changed = true;
        }
      }
    }
    return cells;
  }

  @override
  IntervalSet get bottom => const IntervalSet.empty();

  @override
  IntervalSet eval(int v, List<IntervalSet> cells) {
    var acc = init[v];
    for (final t in terms[v]) {
      acc = acc.join(
        cells[t.from].meet(t.filter).lift1((p) => [(shift(p.$1, t.offset), shift(p.$2, t.offset))]),
      );
    }
    return acc;
  }

  /// The finite ends of cell `v`'s initial value and filters.
  @override
  Landmarks landmarks(int v) {
    if (isBare) return Landmarks.none();
    return Landmarks.of([
      for (final s in [init[v], for (final t in terms[v]) t.filter])
        for (final (lo, hi) in s.pieces)
          for (final e in [lo, hi])
            if (e case Fin(:final v)) v,
    ]);
  }

  @override
  String toString() => 'System(init: $init, terms: $terms, bare: $isBare)';
}

IntervalSet randomFilter(Rng rng) {
  switch (rng.below(4)) {
    case 0:
      return IntervalSet.top();
    case 1:
      return IntervalSet.range(negInf, Fin(rng.int_(-3, 8)));
    case 2:
      return IntervalSet.range(Fin(rng.int_(-8, 3)), posInf);
    default:
      final lo = rng.int_(-6, 4);
      return IntervalSet.of(lo, lo + rng.int_(0, 6));
  }
}

End shift(End e, int by) => switch (e) {
  Fin(:final v) => End.exact(BigInt.from(v) + BigInt.from(by)),
  _ => e,
};

/// Whether every cell contains its own projection: a post-fixpoint, which is what phase 1
/// must reach and phase 2 must keep.
bool isPostFixpoint(System eq, List<IntervalSet> cells) =>
    [for (var v = 0; v < cells.length; v++) v].every((v) => eq.eval(v, cells).isSubset(cells[v]));

/// `[lo, hi]` with null for an infinite end, for readable expectations.
IntervalSet iv(int? lo, int? hi) =>
    IntervalSet.range(lo == null ? negInf : Fin(lo), hi == null ? posInf : Fin(hi));
