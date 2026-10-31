/// The metatheory smoke cases (DESIGN.md sec:kernel, "Metatheory targets"): each target the
/// M0.9 evaluator can execute, run on finite models. Keypath uniqueness and progress with
/// preservation get one case per data generator (reindex, discard, fold); confluence is run
/// over permuted arrival orders here and over schedules in `recursion_test`. Termination of
/// the canonicalization rewrites waits for the rewrites themselves (step L5), and the
/// dependency theorem's agreement across schedules is `recursion_test`.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/check.dart';
import '../../support/kernel.dart';
import 'harness.dart';

/// A key map of a one-level integer family, as a term and as the function it computes.
typedef KeyMap = (String name, Term Function(Term k, Term v) term, int Function(int k, int v) f);

/// Key maps from the witness catalog (strictly monotone arithmetic) and outside it, the last
/// three not injective on every family.
final List<KeyMap> keyMaps = [
  ('k + 1', (k, _) => add(k, lit(1)), (k, _) => k + 1),
  ('2k', (k, _) => mul(k, lit(2)), (k, _) => 2 * k),
  ('3k - 5', (k, _) => sub(mul(k, lit(3)), lit(5)), (k, _) => 3 * k - 5),
  ('k div 2', (k, _) => idiv(k, lit(2)), (k, _) => (k - k % 2) ~/ 2),
  ('v', (_, v) => v, (_, v) => v),
  ('k mod 3', (k, _) => modulo(k, lit(3)), (k, _) => k % 3),
];

/// Every permutation of `xs`, in lexicographic order of positions.
List<List<T>> permutations<T>(List<T> xs) {
  if (xs.length <= 1) return [xs];
  return [
    for (var i = 0; i < xs.length; i++)
      for (final p in permutations([...xs.sublist(0, i), ...xs.sublist(i + 1)])) [xs[i], ...p],
  ];
}

void main() {
  test('keypath uniqueness: a reindex never merges, and collides exactly when its map does', () {
    // Well-typedness implies unique keypaths, carried by T-Reindex: a reindex either returns
    // a family with one entry per source entry or is a collision, and it is a collision
    // exactly when the key map sends two source keys to one. The source keys being distinct
    // does not prevent that, which is why injectivity is the rule's premise.
    var kept = 0, collided = 0;
    for (final (name, term, f) in keyMaps) {
      property(intMaps(31), (m) {
        final t = reindex(
          ints(m),
          func(2, (x) => path([term(key(x[0], 0), x[1])])),
          func(2, (x) => x[1]),
        );
        final image = <int, int>{for (final (k, v) in m) f(k, v): v};
        switch (outcome(t)) {
          case Family got when image.length == m.length:
            kept++;
            final want = Family.of([
              for (final MapEntry(:key, :value) in image.entries) (Int(key), Int(value)),
            ]);
            return got == want ? null : '$name: $got';
          case CollisionError() when image.length < m.length:
            collided++;
            return null;
          case final other:
            return '$name: $other with ${image.length} image keys';
        }
      });
    }
    expect(kept > 0 && collided > 0, isTrue, reason: '$kept kept, $collided collided');
  });

  test('progress and preservation for discard: a well-typed filter returns a subfamily', () {
    // A selector returning a bool on every entry: the result is a value, and it is the
    // sub-family of the entries whose verdict is true.
    for (var c = -2; c <= 2; c++) {
      property(intMaps(32), (m) {
        final t = discardWith(ints(m), (_, v) => lt(lit(c), v));
        final want = [
          for (final (k, v) in m)
            if (c < v) (k, v),
        ];
        final got = outcome(t);
        if (got is KernelError) return '$got';
        return got == eval(ints(want)) ? null : 'threshold $c: $got';
      });
    }
  });

  test('progress and preservation for fold: an operator with its identity returns a scalar', () {
    // Sum, max and min over every map: an int, and the identity on the empty map. Without an
    // identity the empty map folds to `#empty`, a value, never a stuck term.
    const minI64 = -0x8000000000000000, maxI64 = 0x7fffffffffffffff;
    final ops = <(Prim, int, int Function(int, int))>[
      (Prim.add, 0, (a, b) => a + b),
      (Prim.max, minI64, (a, b) => a > b ? a : b),
      (Prim.min, maxI64, (a, b) => a < b ? a : b),
    ];
    for (final (p, e, f) in ops) {
      property(intMaps(33), (m) {
        final withId = outcome(fold(ints(m), PrimFn(p), lit(e)));
        final want = m.map((kv) => kv.$2).fold(e, f);
        if (withId != Int(want)) return '$p with identity: $withId';
        final without = outcome(fold(ints(m), PrimFn(p)));
        final Value expected = m.isEmpty ? const Atom('empty') : Int(want);
        return without == expected ? null : '$p: $without';
      });
    }
  });

  test('confluence: a pure pipeline gives one result for every arrival order', () {
    // Sales arrive in any order; revenue by region is grouped and summed in floats, whose
    // canonical tree follows key order, so all 120 arrival orders of five sales agree to the
    // bit.
    const sales = [
      (1, 'east', 0.1),
      (2, 'west', 0.2),
      (3, 'east', 0.3),
      (4, 'east', 1e16),
      (5, 'west', -0.0),
    ];
    Value pipeline(List<(int, String, double)> order) {
      final f = Family.of([
        for (final (id, r, x) in order) (Int(id), Tuple([s(r), Float(x)])),
      ]);
      final byRegion = groupBy(lit(f), (v) => nth(v, 0));
      final amounts = reindex(byRegion, func(2, (x) => x[0]), func(2, (x) => nth(x[1], 1)));
      return eval(foldAt(amounts, 2, const PrimFn(Prim.add)));
    }

    final first = pipeline(sales);
    final n = property(permutations(sales), (order) {
      final got = pipeline(order);
      return got == first ? null : '$got';
    });
    expect(n, 120);
    // And the result is the exact sums, rounded once: 0.1 + 0.3 + 1e16 and 0.2 + -0.0.
    expect(first.toString(), '{"east" -> 10000000000000000.0, "west" -> 0.2}');
  });
}
