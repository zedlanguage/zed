/// Whole graphs of the shapes real programs lower to, each through every round trip.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart' show Type;
import 'package:zed/zir.dart';

import 'zir.dart';

/// The total of a price list: `fam` prices each item, and an associative, commutative `+`
/// with identity 0 folds the family's one level.
const priceTotal = '''
zir 1
r region function (struct; int in [0..])
r.0 fam (r^0, r^1) -> (struct)
r.0/0 region function (String; int in [0..])
r.0/0.0 prim * (r.0/0^1, 3) -> (int)
r.0/0 results (r.0/0.0^0)
r.1 lambda () -> ((-> (tuple int int) int))
r.1/0 region function (int; int)
r.1/0.0 prim + (r.1/0^0, r.1/0^1) -> (int)
r.1/0 results (r.1/0.0^0)
r.2 fold 1 identity {associative: axiom, commutative: axiom} (r.0^0, r.1^0, 0) -> (int in [0..] facet units "cents")
r results (r.2^0)
''';

/// `main` printing a greeting: a wave threads the `out` port's state through a push.
const greeting = '''
zir 1
r region port (state out)
r.0 wave (r^0) -> (state out)
r.0/0 region port (state out)
r.0/0.0 port push out (r.0/0^0, "Hello, world") -> (_; state out)
r.0/0 results (r.0/0.0^1)
r results (r.0^0)
''';

/// A read from `in` and a push of what was read to `out`: two ports, each state used once.
const echo = '''
zir 1
r region port (state in; state out)
r.0 port read in (r^0) -> (String; state in)
r.1 port push out (r^1, r.0^0) -> (_; state out)
r results (r.0^1, r.1^1)
''';

/// An optional quantity with a default: a match on an atom, one arm per case.
const defaulted = '''
zir 1
r region function ((| #none (#some (tuple int))); int)
r.0 match [#some(n), #none] (r^0, r^1) -> (int)
r.0/0 region match (int; int)
r.0/0 results (r.0/0^0)
r.0/1 region match (int)
r.0/1 results (r.0/1^0)
r results (r.0^0)
''';

/// A countdown: `gen` steps the frame down by 1 while it is positive.
const countdown = '''
zir 1
r region function (int in [0..])
r.0 gen before (r^0) -> (struct)
r.0/0 region loop (int)
r.0/0.0 prim - (r.0/0^0, 1) -> (int)
r.0/0 results (r.0/0.0^0)
r.0/1 region loop (int)
r.0/1.0 prim > (r.0/1^0, 0) -> (bool)
r.0/1 results (r.0/1.0^0)
r results (r.0^0)
''';

/// Reachability as a least fixed point: bottom `{}`, join by union, and each step adds the
/// edges' targets.
const reachable = '''
zir 1
r region function (struct)
r.0 lambda () -> ((-> (tuple struct struct) struct))
r.0/0 region function (struct; struct)
r.0/0.0 prim union (r.0/0^0, r.0/0^1) -> (struct)
r.0/0 results (r.0/0.0^0)
r.1 fix lattice {finiteHeight: bounded, monotone: proved} ({}, r.0^0, r^0) -> (struct)
r.1/0 region loop (struct; struct)
r.1/0.0 prim union (r.1/0^0, r.1/0^1) -> (struct)
r.1/0 results (r.1/0.0^0)
r results (r.1^0)
''';

/// Sales grouped by region: `group` carries its definition, a `reindex` that swaps the two
/// key levels, as its certificate.
const byRegion = '''
zir 1
r region function (struct)
r.0 group (r^0) -> (struct)
r.0/0 region function (struct)
r.0/0.0 lambda () -> ((-> _ _))
r.0/0.0/0 region function (_)
r.0/0.0/0.0 prim pathKey (r.0/0.0/0^0, 1) -> (_)
r.0/0.0/0.1 prim pathKey (r.0/0.0/0^0, 0) -> (_)
r.0/0.0/0.2 prim path (r.0/0.0/0.0^0, r.0/0.0/0.1^0) -> (_)
r.0/0.0/0 results (r.0/0.0/0.2^0)
r.0/0.1 lambda () -> ((-> _ _))
r.0/0.1/0 region function (_)
r.0/0.1/0 results (r.0/0.1/0^0)
r.0/0.2 reindex residue (r.0/0^0, r.0/0.0^0, r.0/0.1^0) -> (struct)
r.0/0 results (r.0/0.2^0)
r results (r.0^0)
''';

/// Tiered shipping: an `if` whose arms read a captured weight, with facts on every edge.
const shipping = '''
zir 1
r region function (int in [0..=50000] class 0 mod 10 hint name "grams")
r.0 prim < (r^0, 1000) -> (bool)
r.1 if (r.0^0, r^0) -> (int set {499, 999})
r.1/0 region match (int in [0..=50000] class 0 mod 10 hint name "grams")
r.1/0 results (499)
r.1/1 region match (int in [0..=50000] class 0 mod 10 hint name "grams")
r.1/1 results (999)
r results (r.1^0)
''';

/// Mutual recursion: `even` and `odd`, defined together by one `rec`.
const parity = '''
zir 1
r region function ()
r.0 rec () -> ((-> int bool); (-> int bool))
r.0/0 region rec ((-> int bool); (-> int bool))
r.0/0.0 lambda (r.0/0^1) -> ((-> int bool))
r.0/0.0/0 region function (int; (-> int bool))
r.0/0.0/0.0 prim == (r.0/0.0/0^0, 0) -> (bool)
r.0/0.0/0.1 prim - (r.0/0.0/0^0, 1) -> (int)
r.0/0.0/0.2 apply (r.0/0.0/0^1, r.0/0.0/0.1^0) -> (bool)
r.0/0.0/0.3 prim || (r.0/0.0/0.0^0, r.0/0.0/0.2^0) -> (bool)
r.0/0.0/0 results (r.0/0.0/0.3^0)
r.0/0.1 lambda (r.0/0^0) -> ((-> int bool))
r.0/0.1/0 region function (int; (-> int bool))
r.0/0.1/0.0 prim != (r.0/0.1/0^0, 0) -> (bool)
r.0/0.1/0.1 prim - (r.0/0.1/0^0, 1) -> (int)
r.0/0.1/0.2 apply (r.0/0.1/0^1, r.0/0.1/0.1^0) -> (bool)
r.0/0.1/0.3 prim && (r.0/0.1/0.0^0, r.0/0.1/0.2^0) -> (bool)
r.0/0.1/0 results (r.0/0.1/0.3^0)
r.0/0 results (r.0/0.0^0, r.0/0.1^0)
r results (r.0^0, r.0^1)
''';

/// A report keyed by tuples, with every kind of constant on its edges.
const constants = r'''
zir 1
r region function ()
r.0 prim tuple (-3r/4r, 1.5e30, nan, -0.0, 123456789012345678901234567890) -> (_)
r.1 prim tuple (#err(code: 3, why: "disk\nfull"), #pair(1, 2), (7), [1 -> "a"], {1 -> 2, 3 -> 4}, {"x", "y"}, {}) -> (_)
r results (r.0^0, r.1^0, true)
''';

void main() {
  test('price total', () {
    final g = round(priceTotal);
    expect(g.kind, RegionKind.function);
    expect(g.nodes, hasLength(3));
    final fold = g.nodes[2];
    expect(fold.op, isA<FoldOp>().having((f) => (f.depth, f.identity), 'depth', (1, true)));
    expect(fold.inputs[0], isA<Out>().having((o) => (o.node, o.port), 'source', (0, 0)));
    // The capture enters the `fam` region as its argument after the key, with its type.
    expect(g.nodes[0].regions[0].args[1], g.args[1]);
  });

  test('greeting', () {
    final g = round(greeting);
    expect(g.nodes[0].outputs, [const StateEdge('out')]);
  });

  test('echo', () => round(echo));

  test('defaulted', () {
    final g = round(defaulted);
    // The first arm binds `n` before the capture; the second binds nothing.
    expect(g.nodes[0].regions[0].args, hasLength(2));
    expect(g.nodes[0].regions[1].args, hasLength(1));
  });

  test('countdown', () => round(countdown));

  test('reachable', () => round(reachable));

  test('by region', () => round(byRegion));

  test('shipping', () {
    final g = round(shipping);
    expect((g.args[0] as ValueEdge).facets[0].hint, isTrue);
  });

  test('parity', () => round(parity));

  test('constants', () => round(constants));

  test('the text form reads and prints regions nested 2000 deep', () {
    const depth = 2000;
    final s = StringBuffer('zir 1\n');
    var path = 'r';
    final paths = <String>[];
    for (var k = 0; k < depth; k++) {
      s.writeln('$path region function (int)');
      s.writeln('$path.0 lambda ($path^0) -> ((-> int int))');
      paths.add(path);
      path = '$path.0/0';
    }
    s.writeln('$path region function (int)');
    s.writeln('$path results ($path^0)');
    for (final p in paths.reversed) {
      s.writeln('$p results ($p.0^0)');
    }
    final g = parse('$s');
    expect(print(g), '$s');
  });

  // A text line holds its whole path, so the text of a graph nested `d` deep has `d²`
  // characters; a graph nested deeper than a recursive walk could go is built directly.
  test('regions nest deeper than a recursive validator or binary form could go', () {
    const depth = 20000;
    final fn = Edge.value(Type.morphism(Type.integer, Type.integer, Type.integer));
    var g = Region(RegionKind.function, [Edge.value(Type.integer)], const [], [const Arg(0)]);
    for (var k = 0; k < depth; k++) {
      g = Region(
        RegionKind.function,
        [Edge.value(Type.integer)],
        [
          Node(const LambdaOp(), [const Arg(0)], [fn], [g]),
        ],
        [const Out(0, 0)],
      );
    }
    validate(g);
    final bytes = encode(g);
    expect(encode(decode(bytes)), bytes);
  });
}
