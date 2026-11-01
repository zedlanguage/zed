/// ZIR at the rule of low complexity (DESIGN.md Part G). Reading, checking, printing and the
/// binary form each take time in proportion to the graph, or that times a logarithm where the
/// reader sorts its lines; a search of the lines or nodes so far for each one would take
/// `O(n²)`, as would a walk that copies a region's path at each level it descends.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart' show Type;
import 'package:zed/zir.dart';

import '../../support/scaling.dart' as scaling;

/// The text of a region of `n` nodes, each adding 1 to the one before, its lines reversed so
/// the reader must sort them.
String wide(int n) {
  final lines = [
    'r region function (int)',
    for (var k = 0; k < n; k++) 'r.$k prim + (${k == 0 ? 'r^0' : 'r.${k - 1}^0'}, 1) -> (int)',
    'r results (r.${n - 1}^0)',
  ];
  return 'zir 1\n${lines.reversed.join('\n')}\n';
}

/// `n` `lambda` regions, each nested in the one before.
Region deep(int n) {
  final fn = Edge.value(Type.morphism(Type.integer, Type.integer, Type.integer));
  var g = Region(RegionKind.function, [Edge.value(Type.integer)], const [], [const Arg(0)]);
  for (var k = 0; k < n; k++) {
    g = Region(
      RegionKind.function,
      [Edge.value(Type.integer)],
      [
        Node(const LambdaOp(), [const Arg(0)], [fn], [g]),
      ],
      [const Out(0, 0)],
    );
  }
  return g;
}

void main() {
  const n = 4000;
  final texts = {
    for (final m in [n, 8 * n]) m: wide(m),
  };
  final graphs = {
    for (final m in [n, 8 * n]) m: parse(texts[m]!),
  };
  final bytes = {
    for (final m in [n, 8 * n]) m: encode(graphs[m]!),
  };
  final deeps = {
    for (final m in [n, 8 * n]) m: deep(m),
  };
  final deepBytes = {
    for (final m in [n, 8 * n]) m: encode(deeps[m]!),
  };

  test('reading the text of a region of n nodes scales', () {
    scaling.check('reading n nodes from text', n, (m) => parse(texts[m]!));
  });

  test('checking a region of n nodes scales', () {
    scaling.check('checking n nodes', n, (m) => validate(graphs[m]!));
  });

  test('printing a region of n nodes scales', () {
    scaling.check('printing n nodes', n, (m) => print(graphs[m]!));
  });

  test('the binary form of a region of n nodes scales', () {
    scaling.check('encoding and decoding n nodes', n, (m) {
      encode(graphs[m]!);
      decode(bytes[m]!);
    });
  });

  test('checking regions nested n deep scales', () {
    scaling.check('checking n nested regions', n, (m) => validate(deeps[m]!));
  });

  test('the binary form of regions nested n deep scales', () {
    scaling.check('encoding and decoding n nested regions', n, (m) {
      encode(deeps[m]!);
      decode(deepBytes[m]!);
    });
  });
}
