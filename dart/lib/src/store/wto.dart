/// The weak topological order of a dependency graph (DESIGN.md sec:domains, fixed by step
/// M0.5), computed by Bourdoncle's algorithm [Bourdoncle, "Efficient chaotic iteration
/// strategies with widenings", 1993, figure 4].
///
/// The vertices are `0..n` in source order, and each vertex's successors are listed in source
/// order; the depth-first traversal starts from the vertices in that order and visits
/// successors in that order. A graph has many weak topological orders, and this traversal
/// picks one, so the order, and with it the widening points, is a function of the source.
library;

/// An element of a weak topological order: a vertex, or a component with its head and body.
sealed class Element {
  const Element();

  /// The vertices of the element, in order.
  List<int> vertices() {
    final out = <int>[];
    final todo = <Element>[this];
    while (todo.isNotEmpty) {
      switch (todo.removeLast()) {
        case Vertex(:final v):
          out.add(v);
        case Component(:final head, :final body):
          out.add(head);
          todo.addAll(body.reversed);
      }
    }
    return out;
  }
}

/// A vertex on no cycle through the enclosing head.
final class Vertex extends Element {
  final int v;

  const Vertex(this.v);

  @override
  bool operator ==(Object other) => other is Vertex && other.v == v;

  @override
  int get hashCode => v.hashCode;

  @override
  String toString() => '$v';
}

/// A strongly connected part, iterated as a loop: the head, where widening happens, and the
/// order of the rest, with the edges into the head removed.
final class Component extends Element {
  /// The head: the first vertex of the component the traversal reaches.
  final int head;

  /// The weak topological order of the rest of the component.
  final List<Element> body;

  const Component(this.head, this.body);

  /// Bourdoncle's notation, head first: `(1 2 (3 4))`.
  @override
  String toString() => '($head${body.map((e) => ' $e').join()})';
}

/// An order in Bourdoncle's notation: `0 (1 2 (3 4)) 5`.
String show(List<Element> order) => order.join(' ');

/// The weak topological order of the graph whose vertex `v` has the successors `succ[v]`.
///
/// It is the order Bourdoncle's recursive algorithm gives, computed from one depth-first
/// traversal in `O((V + E) log V)` (the rule of low complexity, DESIGN.md Part G), where the
/// recursive algorithm traverses each component again at every level of nesting and costs
/// `O(d·(V + E))` for nesting depth `d`. A vertex is a head when an edge returns to it from
/// its own subtree, and its component is the part of its subtree that reaches it there, found
/// as a loop of the loop-nesting forest (the method of Havlak, "Nesting of reducible and
/// irreducible loops", 1997, with each edge read once as in Ramalingam, "Identifying loops in
/// almost linear time", 1999): an edge that is not a back edge is filed at the common ancestor
/// of its ends, the first vertex whose component can hold both. Each level lists its elements
/// in decreasing order of the time the traversal finished them. The step tests check the
/// result against the declarative definition.
List<Element> weakTopologicalOrder(List<List<int>> succ) {
  final n = succ.length;
  final t = _Traversal(succ);
  final predsBack = [for (var v = 0; v < n; v++) <int>[]];
  // Each non-back edge, filed at the common ancestor of its ends where it can first lie
  // inside a component.
  final filed = [for (var v = 0; v < n; v++) <(int, int)>[]];
  final up = t.ancestors();
  for (var u = 0; u < n; u++) {
    for (final w in succ[u]) {
      if (t.ancestorOrSelf(w, u)) {
        predsBack[w].add(u);
      } else if (t.commonAncestor(up, u, w) case final a?) {
        filed[a].add((u, w));
      }
    }
  }
  // Each vertex's set, named by its outermost head found so far, as a union-find forest.
  final set = [for (var v = 0; v < n; v++) v];
  int find(int v) {
    while (set[v] != v) {
      set[v] = set[set[v]];
      v = set[v];
    }
    return v;
  }

  // The edges into each set whose source is not yet known to be inside a component with it.
  final entries = [for (var v = 0; v < n; v++) <int>[]];
  final headOf = List<int?>.filled(n, null);
  final isHead = List.filled(n, false);
  // The head that last took each set into its component, so that no set is taken twice.
  final taken = List<int?>.filled(n, null);
  for (final h in t.order.reversed) {
    for (final (u, w) in filed[h]) {
      entries[find(w)].add(u);
    }
    final work = <int>[];
    void take(int u) {
      final r = find(u);
      if (r != h && taken[r] != h) {
        taken[r] = h;
        work.add(r);
      }
    }

    for (final u in predsBack[h]) {
      isHead[h] = true;
      take(u);
    }
    final members = <int>[];
    while (work.isNotEmpty) {
      final x = work.removeLast();
      members.add(x);
      entries[x]
        ..forEach(take)
        ..clear();
    }
    // Each member's entries were read when it was taken, so only the set changes.
    for (final x in members) {
      headOf[x] = h;
      set[x] = h;
    }
  }
  // Each level's elements, in decreasing order of finishing; the top level is the last list.
  final children = [for (var v = 0; v <= n; v++) <int>[]];
  for (final v in t.finished.reversed) {
    children[headOf[v] ?? n].add(v);
  }
  // A member finishes before its head, so each body is built before the head needs it.
  final built = List<Element?>.filled(n, null);
  for (final v in t.finished) {
    built[v] = isHead[v] ? Component(v, [for (final c in children[v]) built[c]!]) : Vertex(v);
  }
  return [for (final c in children[n]) built[c]!];
}

/// The depth-first traversal from the vertices in order, each vertex's successors in order.
final class _Traversal {
  /// Each vertex's number in the order the traversal reached it.
  final List<int> pre;

  /// One more than the largest number in the vertex's subtree.
  final List<int> end;

  /// The vertex's parent in the traversal's forest.
  final List<int?> parent;

  /// The vertices in the order the traversal reached them.
  final order = <int>[];

  /// The vertices in the order the traversal finished them.
  final finished = <int>[];

  _Traversal(List<List<int>> succ)
    : pre = List.filled(succ.length, -1),
      end = List.filled(succ.length, 0),
      parent = List.filled(succ.length, null) {
    // Each open vertex with the index of its next successor.
    final stack = <(int, int)>[];
    for (var root = 0; root < succ.length; root++) {
      if (pre[root] >= 0) continue;
      pre[root] = order.length;
      order.add(root);
      stack.add((root, 0));
      while (stack.isNotEmpty) {
        final (v, i) = stack.last;
        if (i < succ[v].length) {
          stack.last = (v, i + 1);
          final w = succ[v][i];
          if (pre[w] < 0) {
            pre[w] = order.length;
            parent[w] = v;
            order.add(w);
            stack.add((w, 0));
          }
        } else {
          stack.removeLast();
          end[v] = order.length;
          finished.add(v);
        }
      }
    }
  }

  /// Whether `a` is `v` or an ancestor of it.
  bool ancestorOrSelf(int a, int v) => pre[a] <= pre[v] && pre[v] < end[a];

  /// For each `k`, each vertex's ancestor `2^k` levels up, or itself at a root.
  List<List<int>> ancestors() {
    final n = pre.length;
    final up = [
      [for (var v = 0; v < n; v++) parent[v] ?? v],
    ];
    while (1 << up.length < (n > 1 ? n : 1)) {
      final last = up.last;
      up.add([for (var v = 0; v < n; v++) last[last[v]]]);
    }
    return up;
  }

  /// The deepest common ancestor of `u` and `w`, if they are in one tree.
  int? commonAncestor(List<List<int>> up, int u, int w) {
    if (ancestorOrSelf(u, w)) return u;
    var a = u;
    for (final level in up.reversed) {
      if (!ancestorOrSelf(level[a], w)) a = level[a];
    }
    final p = up[0][a];
    return ancestorOrSelf(p, w) ? p : null;
  }
}
