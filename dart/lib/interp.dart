/// The definitional interpreter (DESIGN.md Part G, steps L1.18–L1.21): elaborated kernel
/// terms run by the kernel's reference evaluator, under the prelude words they read.
///
/// Step L1.18 binds the L1 words on scalars, each to its kernel primitive; the evaluator
/// itself holds the per-region operator arrows, atom pass-through and the `#errs` merge.
library;

import 'kernel.dart';

/// The L1 prelude words and their primitives.
const _words = [
  ('String', Prim.show),
  ('int', Prim.castInt),
  ('rat', Prim.castRat),
  ('f64', Prim.castF64),
  ('abs', Prim.abs),
  ('len', Prim.len),
  ('lower', Prim.lower),
  ('upper', Prim.upper),
  ('trim', Prim.trim),
  ('sum', Prim.sum),
];

/// `body` under the prelude: each word it may read bound to its primitive.
Term prelude(Term body) {
  for (final (name, p) in _words.reversed) {
    body = Let(name, PrimFn(p), body);
  }
  return body;
}
