/// Step M0.10: the finite-model harness.
///
/// Every law of the catalog (DESIGN.md sec:optimizer) is run against the reference evaluator
/// of step M0.9 on finite models: each law's two sides, built as the kernel terms a program
/// elaborates to, must agree on every instance, and each side condition comes with the
/// counterexample that makes it necessary, an instance on which the sides differ once the
/// condition is dropped. Beside the laws: witness bijectivity (`witnesses_test`), the
/// recursion checks (`recursion_test`), and the metatheory smoke cases (`smoke_test`).
///
/// The instances are exhaustive enumerations in shortlex order up to the bounds of
/// `support/instances.dart`, with at most [enumerationBudget] per law, plus
/// [randomInstances] seeded random ones beyond those bounds.
library;

import 'package:zed/kernel.dart';

import '../../support/instances.dart';
import '../../support/kernel.dart';

/// A one-level family of integers, as its entries in key order.
typedef IntMap = List<(int, int)>;

/// The integer maps every law over one level runs on: all 1,296 partial maps from the keys
/// `0..4` to the values `-2..=2`, then random maps over the keys and values `-8..=8`.
List<IntMap> intMaps(int seed) {
  final out = partialMaps([0, 1, 2, 3], [-2, -1, 0, 1, 2]);
  final rng = Rng(seed);
  for (var i = 0; i < randomInstances; i++) {
    out.add([
      for (var k = -8; k <= 8; k++)
        if (rng.below(3) == 0) (k, rng.int_(-8, 8)),
    ]);
  }
  assert(out.length <= enumerationBudget);
  return out;
}

/// The map as a literal family term.
Term ints(IntMap m) => lit(mapValue(m));

/// A sequence as a literal family term `0..n -> x`.
Term seq(List<Object> xs) => lit(seqValue(xs));

/// A literal family from its entries, each a value already.
Term family(List<(Value, Value)> entries) => lit(Family.of(entries));

/// A primitive as a function value.
Term pf(Prim p) => PrimFn(p);

// Relations on the nodes `0..relationNodes`, shared by law 15 and laws 21–28.

/// How many nodes a relation is on.
const relationNodes = 4;

/// The nodes `0..relationNodes` as a set.
Term nodes() => lit(Family.set([for (var i = 0; i < relationNodes; i++) Int(i)]));

/// A relation as the two-level family `u -> v -> true`.
Term relation(List<(int, int)> pairs) => lit(
  Family.fromLeaves([
    for (final (u, v) in pairs) ([Int(u), Int(v)], const Bool(true)),
  ]),
);

/// `r · s`: the pairs `(u, w)` with some `v` such that `(u, v)` is in `r` and `(v, w)` in `s`.
Term compose(Term r, Term s) => famWith(nodes(), (u) {
  final row = famWith(nodes(), (w) {
    final via = discardWith(nodes(), (p, _) {
      final v = key(p, 0);
      return and(found(get(get(r, u), v)), found(get(get(s, v), w)));
    });
    return lt(lit(0), count(via));
  });
  return discardWith(row, (_, e) => e);
});

/// `a ∪ b`.
Term union(Term a, Term b) => prim(Prim.union, [a, b]);

/// Every relation on three of the nodes, then random ones on all four.
List<List<(int, int)>> relations() {
  final pairs3 = [
    for (var u = 0; u < 3; u++)
      for (var v = 0; v < 3; v++) (u, v),
  ];
  final out = [
    for (var mask = 0; mask < 1 << pairs3.length; mask++)
      [
        for (var i = 0; i < pairs3.length; i++)
          if (mask & (1 << i) != 0) pairs3[i],
      ],
  ];
  final rng = Rng(15);
  for (var n = 0; n < 256; n++) {
    out.add([
      for (var u = 0; u < relationNodes; u++)
        for (var v = 0; v < relationNodes; v++)
          if (rng.below(4) == 0) (u, v),
    ]);
  }
  return out;
}
