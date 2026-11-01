/// Termination on random graphs: every step lowers the ranks lexicographically, the normal
/// form has no written binder, hint, out-of-order facet or unnormalized domain, and shuffling
/// facets or renaming binders leaves the address alone.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart' show Int;
import 'package:zed/zir.dart';

import 'zir.dart';

/// A linear congruential generator, so that every run sees the same graphs.
final class Lcg {
  int state;

  Lcg(this.state);

  int next(int n) {
    state = state * 6364136223846793005 + 1442695040888963407;
    return (state >>> 33) % n;
  }
}

const facets = [
  'facet units "m"',
  'facet units "s"',
  'facet locale "en"',
  'hint name "total"',
  'hint name "n"',
  'facet units "m"',
];

const names = ['a', 'b', 'count', 'x1', 'rest'];

/// A random edge.
String edge(Lcg rng) {
  final e = StringBuffer('int');
  switch (rng.next(4)) {
    case 0:
      break;
    case 1:
      final lo = rng.next(20) - 10;
      e.write(' in [$lo..=${lo + rng.next(30)}]');
    case 2:
      e.write(' class ${rng.next(3)} mod ${3 + rng.next(3)}');
    default:
      final n = 1 + rng.next(4);
      final xs = {for (var i = 0; i < n; i++) rng.next(25) - 5}.toList()..sort();
      e.write(' in [-5..=40] set {${xs.join(', ')}}');
  }
  for (var i = rng.next(4); i > 0; i--) {
    e.write(' ${facets[rng.next(facets.length)]}');
  }
  return '$e';
}

/// A random graph: a function region whose nodes negate an argument, match a pair, or define a
/// function whose body matches one, binding names `name` picks.
String random(Lcg rng, String Function(int) name) {
  final args = 1 + rng.next(3);
  final src = StringBuffer(
    'zir 1\nr region function (${[for (var i = 0; i < args; i++) edge(rng)].join('; ')})\n',
  );
  var binder = 0;
  final nodes = rng.next(5);
  for (var k = 0; k < nodes; k++) {
    final kind = rng.next(3);
    if (kind == 0) {
      src.write('r.$k prim neg (r^0) -> (${edge(rng)})\n');
    } else {
      final (a, b) = (name(binder), name(binder + 1));
      binder += 2;
      final (ea, eb) = (edge(rng), edge(rng));
      if (kind == 1) {
        // A match inside a function's body, one region down.
        src.write(
          'r.$k lambda () -> ((-> tuple int))\nr.$k/0 region function (tuple)\nr.$k/0.0 match [($a, $b)] (r.$k/0^0) -> (${edge(rng)})\nr.$k/0.0/0 region match ($ea; $eb)\nr.$k/0.0/0 results (r.$k/0.0/0^0)\nr.$k/0 results (r.$k/0.0^0)\n',
        );
      } else {
        src.write(
          'r.$k match [(#p($a), $b)] (r^0) -> (${edge(rng)})\nr.$k/0 region match ($ea; $eb)\nr.$k/0 results (r.$k/0^1)\n',
        );
      }
    }
  }
  return '${src}r results (r^0)\n';
}

String written(int i) => '${names[i % names.length]}$i';

/// Whether `a` is lexicographically below `b`.
bool below(List<int> a, List<int> b) {
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return a[i] < b[i];
  }
  return false;
}

/// No written binder, no hint, and no out-of-order or repeated facet anywhere in `g`.
void expectNormal(Region g) {
  final edges = [...g.args];
  for (final n in g.nodes) {
    edges.addAll(n.outputs);
    n.regions.forEach(expectNormal);
    if (n.op case MatchOp(:final patterns)) {
      for (final p in patterns) {
        expect(pattern(p), isNot(matches(RegExp('[A-Za-oq-z]'))));
      }
    }
  }
  for (final e in edges.whereType<ValueEdge>()) {
    expect(e.facets.where((f) => f.hint), isEmpty);
    for (var i = 0; i + 1 < e.facets.length; i++) {
      expect(e.facets[i].compareTo(e.facets[i + 1]), lessThan(0));
    }
    expect(e.domain.rank, 0);
  }
}

/// `g` with every edge's facets reversed.
Region reverseFacets(Region g) {
  Edge flip(Edge e) => switch (e) {
    ValueEdge(:final type, :final domain, :final facets) => ValueEdge(
      type,
      domain: domain,
      facets: facets.reversed.toList(),
    ),
    StateEdge() => e,
  };
  return Region(g.kind, g.args.map(flip).toList(), [
    for (final n in g.nodes)
      Node(n.op, n.inputs, n.outputs.map(flip).toList(), n.regions.map(reverseFacets).toList()),
  ], g.results);
}

void main() {
  test('every step lowers the ranks', () {
    final rng = Lcg(7);
    var steps = 0;
    for (var i = 0; i < 300; i++) {
      var g = graph(random(rng, written));
      var before = ranks(g);
      for (var s = step(g); s != null; s = step(g)) {
        final (h, rule) = s;
        final after = ranks(h);
        expect(below(after, before), isTrue, reason: '$rule: $before -> $after');
        (g, before) = (h, after);
        steps++;
      }
      expect([before[0], before[1], before[3]], [0, 0, 0]);
      expectNormal(g);
    }
    // The graphs gave every rule work to do.
    expect(steps, greaterThan(1000));
  });

  test('shuffles and renamings keep the address', () {
    for (var seed = 0; seed < 200; seed++) {
      // The same draws give the same graph; only the names differ.
      final a = graph(random(Lcg(seed), (i) => 'v$i'));
      final b = graph(random(Lcg(seed), (i) => 'w${100 - i}'));
      expect(address(a), address(b), reason: 'seed $seed');
      // Reversing every edge's facets leaves the address alone.
      expect(address(reverseFacets(a)), address(a), reason: 'seed $seed');
    }
  });

  test('the one-pass normal form is the one the steps reach', () {
    final rng = Lcg(11);
    var changed = 0;
    for (var i = 0; i < 300; i++) {
      final g = graph(random(rng, written));
      var stepped = g;
      for (var s = step(g); s != null; s = step(stepped)) {
        stepped = s.$1;
      }
      final once = canonicalize(g);
      expect(sameGraph(once, stepped), isTrue);
      if (!sameGraph(once, g)) changed++;
    }
    expect(changed, greaterThan(250), reason: '$changed of 300 graphs were not already normal');
  });

  test('the key agrees with the address', () {
    final graphs = [
      for (var seed = 0; seed < 120; seed++) ...[
        graph(random(Lcg(seed), (i) => 'v$i')),
        graph(random(Lcg(seed), (i) => 'w${100 - i}')),
      ],
    ];
    // Copies that differ from their graph only inside a node's region.
    final inner = [
      for (final g in graphs)
        if (g.nodes.indexWhere((n) => n.regions.isNotEmpty) case final k when k >= 0)
          () {
            final n = g.nodes[k];
            final r = n.regions[0];
            final r2 = Region(r.kind, r.args, r.nodes, [
              const Const(Int(99)),
              ...r.results.skip(1),
            ]);
            final n2 = Node(n.op, n.inputs, n.outputs, [r2, ...n.regions.skip(1)]);
            return Region(g.kind, g.args, [...g.nodes]..[k] = n2, g.results);
          }(),
    ];
    expect(inner.length, greaterThan(100));
    graphs.addAll(inner);
    final both = [for (final g in graphs) (address(g), key(g))];
    var (same, differ) = (0, 0);
    for (final a in both) {
      for (final b in both) {
        final byAddress = a.$1 == b.$1;
        expect(a.$2 == b.$2, byAddress);
        if (byAddress) {
          same++;
        } else {
          differ++;
        }
      }
    }
    // Each graph equals its renamed copy, and most pairs differ.
    expect(same, greaterThanOrEqualTo(2 * graphs.length));
    expect(differ, greaterThan(graphs.length * graphs.length ~/ 2));
  });
}
