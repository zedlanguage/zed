/// Step L1.38: the linear-relation domain (DESIGN.md sec:domains, "linear-integer relations
/// among in-scope keys and cardinalities (Presburger)", and sec:verification, rung 2).
///
/// `entailment` checks rung 2 on the facts the design names, written as Zed functions:
/// `y * w + x < h * w` follows from `0 <= y < h` and `0 <= x < w`, and not from `y <= h`.
/// `preimage` checks the z3 fixtures and the relation a non-box preimage keeps. `random` checks
/// the translation, the Omega test, the projection and entailment against the interpreter at
/// every point of a window, and `controls` checks relations of any size, the undecided
/// fragment, and that each check of `random` rejects a wrong answer.
library;

import 'package:zed/kernel.dart' hide Atom;
import 'package:zed/presburger.dart';
import 'package:zed/store.dart' show IntervalSet, relations;

import '../l01_25_preimage_catalog/support.dart';

/// The parameters of `ok` in `src`, and the relation its body states, products of two symbols
/// as atoms.
(List<String>, Relation) relation(String src) {
  final (ps, body) = function(src);
  final r = relations([body], ps, true) ?? (throw StateError('$src: outside the domain'));
  return (ps, r.single);
}

/// The value of `t` with each of `names` bound to its value in `point`; null for a failure.
Value? at(Term t, List<String> names, List<int> point) {
  for (var i = names.length - 1; i >= 0; i--) {
    t = Let(names[i], Lit(Int(point[i])), t);
  }
  try {
    return eval(t);
  } on KernelError {
    return null;
  }
}

/// Whether the test `t` holds at `point`.
bool holds(Term t, List<String> names, List<int> point) => at(t, names, point) == const Bool(true);

/// The values of `names` in a model, each absent one zero, as a point.
List<int> point(Model m, List<String> names) => [
  for (final n in names) (m[Sym(n)] ?? BigInt.zero).toInt(),
];

/// Each point of the square window `[lo..=hi]` in `n` dimensions, the last axis fastest.
List<List<int>> window(int n, int lo, int hi) {
  var out = <List<int>>[[]];
  for (var i = 0; i < n; i++) {
    out = [
      for (final p in out)
        for (var v = lo; v <= hi; v++) [...p, v],
    ];
  }
  return out;
}

/// The values each coordinate takes over `points`, as sets.
List<IntervalSet> projections(List<List<int>> points, int n) => [
  for (var j = 0; j < n; j++)
    {for (final p in points) p[j]}
        .fold(const IntervalSet.empty(), (s, v) => s.join(IntervalSet.single(v))),
];
