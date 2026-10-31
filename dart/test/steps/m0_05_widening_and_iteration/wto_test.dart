/// The weak topological order against its declarative definition.
///
/// The definition, written here without Bourdoncle's stack: run a depth-first search from the
/// roots in order, visiting successors in source order, and number the vertices in preorder
/// and in finish order. Group the vertices into strongly connected components by mutual
/// reachability; a component's head is its member with the least preorder number, and the
/// components are listed by decreasing finish time of their heads. A component with one vertex
/// and no self-loop is that vertex; any other is the head followed by the order of the rest of
/// the component, computed the same way with the edges into the head removed and the head's
/// successors as roots.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';

/// The declarative order of the vertices `within` (a subset of the graph), from `roots`.
List<Element> declarative(List<List<int>> succ, List<int> within, List<int> roots) {
  final inside = within.toSet();
  final n = succ.length;
  final pre = List.filled(n, -1), fin = List.filled(n, -1);
  var p = 0, f = 0;
  void dfs(int v) {
    pre[v] = p++;
    for (final w in succ[v]) {
      if (inside.contains(w) && pre[w] < 0) dfs(w);
    }
    fin[v] = f++;
  }

  for (final r in [...roots, ...within]) {
    if (inside.contains(r) && pre[r] < 0) dfs(r);
  }
  // Reachability inside the subset, by closure.
  final reach = [for (var v = 0; v < n; v++) List.filled(n, false)];
  for (final v in within) {
    for (final w in succ[v]) {
      if (inside.contains(w)) reach[v][w] = true;
    }
  }
  for (final k in within) {
    for (final i in within) {
      for (final j in within) {
        if (reach[i][k] && reach[k][j]) reach[i][j] = true;
      }
    }
  }
  final heads = [
    for (final v in within)
      if (within.every((w) => w == v || !(reach[v][w] && reach[w][v]) || pre[v] < pre[w])) v,
  ]..sort((a, b) => fin[b].compareTo(fin[a]));
  return [
    for (final h in heads)
      if ([
            for (final w in within)
              if (w != h && reach[h][w] && reach[w][h]) w,
          ]
          case final rest)
        rest.isEmpty && !reach[h][h]
            ? Vertex(h)
            : Component(h, declarative(succ, rest, [...succ[h].where(rest.contains)])),
  ];
}

List<Element> oracle(List<List<int>> succ) {
  final all = [for (var v = 0; v < succ.length; v++) v];
  return declarative(succ, all, all);
}

List<List<int>> randomGraph(Rng rng) {
  final n = 1 + rng.below(10);
  return [
    for (var v = 0; v < n; v++)
      ({for (var i = rng.below(4); i > 0; i--) rng.below(n)}.toList()..sort()),
  ];
}

bool nests(Element e) => e is Component && e.body.any((b) => b is Component || nests(b));

void main() {
  test('Bourdoncle agrees with the declarative definition', () {
    final rng = Rng(0x5f05);
    var components = 0;
    for (var i = 0; i < 4 * randomInstances; i++) {
      final g = randomGraph(rng);
      final got = weakTopologicalOrder(g);
      expect(show(got), show(oracle(g)), reason: 'graph $g');
      components += got.whereType<Component>().length;
    }
    // The sample exercises components, not only acyclic graphs.
    expect(components, greaterThan(randomInstances));
  });

  test('every backward edge goes to an enclosing head', () {
    // The defining property of a weak topological order: every edge either goes forward in
    // the order, or goes to the head of a component that contains its source.
    void positions(Element e, List<int> heads, List<(int, List<int>)> out) {
      switch (e) {
        case Vertex(:final v):
          out.add((v, [...heads]));
        case Component(:final head, :final body):
          heads.add(head);
          out.add((head, [...heads]));
          for (final b in body) {
            positions(b, heads, out);
          }
          heads.removeLast();
      }
    }

    final rng = Rng(0xb0d);
    for (var i = 0; i < randomInstances; i++) {
      final g = randomGraph(rng);
      final order = <(int, List<int>)>[];
      for (final e in weakTopologicalOrder(g)) {
        positions(e, [], order);
      }
      expect(order, hasLength(g.length), reason: 'each vertex once: $g');
      int at(int v) => order.indexWhere((o) => o.$1 == v);
      for (var u = 0; u < g.length; u++) {
        for (final w in g[u]) {
          if (at(w) <= at(u)) {
            expect(order[at(u)].$2, contains(w), reason: 'edge $u->$w in $g');
          }
        }
      }
    }
  });

  test('a parser loop with an inner retry nests its components', () {
    // A tokenizer's main loop: 0 reads a character, 1 classifies it, 2 accumulates a token and
    // loops on itself while the token continues, 3 emits it and returns to 0; 4 is the end of
    // input, reached from 1.
    final g = [
      [1],
      [2, 4],
      [2, 3],
      [0],
      <int>[],
    ];
    expect(show(weakTopologicalOrder(g)), '(0 1 (2) 3) 4');
    expect(show(oracle(g)), '(0 1 (2) 3) 4');
  });

  test('the traversal order picks the head', () {
    // The same three-cell loop with its cells numbered two ways: the head is whichever cell
    // the traversal reaches first, which is the first in source order.
    expect(
      show(
        weakTopologicalOrder([
          [1],
          [2],
          [0],
        ]),
      ),
      '(0 1 2)',
    );
    expect(
      show(
        weakTopologicalOrder([
          [2],
          [0],
          [1],
        ]),
      ),
      '(0 2 1)',
    );
  });

  test('the order agrees with the declarative definition on larger graphs', () {
    // Successor lists out of order and repeated, the traversal's order following the lists as
    // written.
    final rng = Rng(0x5f06);
    var nested = 0;
    for (var i = 0; i < 2 * randomInstances; i++) {
      final n = 1 + rng.below(40);
      final g = [
        for (var v = 0; v < n; v++)
          [
            // Mostly near, so that loops nest.
            for (var j = rng.below(4); j > 0; j--)
              rng.below(3) == 0 ? rng.below(n) : (v + 2 * n + rng.below(5) - 2) % n,
          ],
      ];
      final got = weakTopologicalOrder(g);
      expect(show(got), show(oracle(g)), reason: 'graph $g');
      if (got.any(nests)) nested++;
    }
    // The sample exercises nested components.
    expect(nested, greaterThan(randomInstances ~/ 4));
  });
}
