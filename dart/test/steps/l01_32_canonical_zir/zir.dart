/// Step L1.32: the M0.7 canonicalizer on ZIR, and the content address over its normal form.
/// Renaming a pattern's binders, renaming or dropping hints, reordering or repeating facets,
/// and respelling a set of integers leave the address alone; changing a value changes it. The
/// rules terminate on random graphs, each step lowering the tuple of ranks.
library;

import 'package:zed/zir.dart';

/// The graph written in `src`.
Region graph(String src) => parse(src);

/// Whether `a` and `b` are the same graph: their binary forms are equal exactly when they are.
bool sameGraph(Region a, Region b) {
  final (x, y) = (encode(a), encode(b));
  if (x.length != y.length) return false;
  for (var i = 0; i < x.length; i++) {
    if (x[i] != y[i]) return false;
  }
  return true;
}
