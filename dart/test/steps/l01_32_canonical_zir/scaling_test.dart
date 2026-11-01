/// The canonicalizer at the rule of low complexity (DESIGN.md Part G). The normal form, the
/// address, the bottom-up key, the ranks and one rewrite step each take time in proportion to
/// the graph, whether its regions sit side by side or nest; a search of the nodes so far, or
/// of the walk's stack, at each node would take `O(n²)`.
library;

import 'package:test/test.dart';
import 'package:zed/canon.dart' show Facet;
import 'package:zed/kernel.dart' show BindP, Str, TupleP, Type;
import 'package:zed/zir.dart';

import '../../support/scaling.dart' as scaling;

/// An integer edge with a hint and two facets out of order.
Edge edge() => ValueEdge(
  Type.integer,
  facets: [
    Facet('units', Str('m')),
    Facet('name', Str('total'), hint: true),
    Facet('locale', Str('en')),
  ],
);

/// A match on a pair with written binders, whose arm holds `body`, or returns its first
/// binding when `body` is null.
Node match(Src scrutinee, int k, Node? body) => Node(
  MatchOp([
    TupleP([BindP('a$k'), BindP('b$k')]),
  ]),
  [scrutinee],
  [edge()],
  [
    Region(RegionKind.match, [edge(), edge()], [?body], [
      body == null ? const Arg(0) : const Out(0, 0),
    ]),
  ],
);

/// A region of `n` such matches side by side.
Region wide(int n) => Region(
  RegionKind.function,
  [edge()],
  [for (var k = 0; k < n; k++) match(const Arg(0), k, null)],
  [Out(n - 1, 0)],
);

/// `n` matches, each holding a `lambda` whose body holds the next.
Region deep(int n) {
  final fn = Edge.value(Type.morphism(Type.integer, Type.integer, Type.integer));
  var g = Region(RegionKind.function, [edge()], [match(const Arg(0), n, null)], [const Out(0, 0)]);
  for (var k = 0; k < n; k++) {
    g = Region(
      RegionKind.function,
      [edge()],
      [
        match(const Arg(0), k, Node(const LambdaOp(), [const Arg(0)], [fn], [g])),
      ],
      [const Out(0, 0)],
    );
  }
  return g;
}

void main() {
  const n = 4000;
  final graphs = {
    'side by side': {
      for (final m in [n, 8 * n]) m: wide(m),
    },
    'nested': {
      for (final m in [n, 8 * n]) m: deep(m),
    },
  };

  for (final MapEntry(key: shape, value: gs) in graphs.entries) {
    test('the normal form of n regions $shape scales', () {
      scaling.check('canonicalizing n regions $shape', n, (m) => canonicalize(gs[m]!));
    });

    test('the address of n regions $shape scales', () {
      scaling.check('the address of n regions $shape', n, (m) => address(gs[m]!));
    });

    test('the key of n regions $shape scales', () {
      scaling.check('the key of n regions $shape', n, (m) => key(gs[m]!));
    });

    test('the ranks of n regions $shape scale', () {
      scaling.check('the ranks of n regions $shape', n, (m) => ranks(gs[m]!));
    });

    test('one rewrite step on n regions $shape scales', () {
      scaling.check('one step on n regions $shape', n, (m) => step(gs[m]!));
    });
  }
}
