/// The definedness-fix recursion checks (DESIGN.md sec:kernel, the dependency theorem): every
/// schedule of a definedness `fix` reaches the same family. Jacobi rounds (the wavefront),
/// chaotic iteration in seeded orders, and memoized pull all agree on the entries they
/// define, and on a cyclic dependency all stall on the same keys: the entries that depend,
/// directly or through others, on a cycle.
library;

import 'dart:math' as math;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/instances.dart';
import '../../support/kernel.dart';

/// Every schedule the harness runs: the wavefront, memoized pull, and chaotic iteration in
/// eight seeded orders.
final List<Schedule> schedules = [
  const Rounds(),
  const Pull(),
  for (var i = 0; i < 8; i++) Chaotic(i),
];

String nameOf(Schedule s) => switch (s) {
  Rounds() => 'Rounds',
  Pull() => 'Pull',
  Chaotic(:final seed) => 'Chaotic($seed)',
};

/// The value `t` computes under `schedule`, or the error that stopped it.
Object run(Term t, Schedule schedule) {
  try {
    return Evaluator(World(), schedule: schedule).run(t);
  } on KernelError catch (e) {
    return e;
  }
}

/// A directed graph on the nodes `0..n`, as its successor lists.
typedef Graph = List<List<int>>;

/// The successor table `node -> successor -> true`. A node with no successors has no entry,
/// since an empty inner level drops its key.
Term successors(Graph g) => lit(
  Family.fromLeaves([
    for (var u = 0; u < g.length; u++)
      for (final v in g[u]) ([Int(u), Int(v)], const Bool(true)),
  ]),
);

/// The number of paths from each node to a sink, counting the empty path: a build system's
/// count of the ways each target's inputs reach the sources. `paths(u) = 1 + Σ paths(v)` over
/// the successors `v` of `u`.
Term pathCounts(Graph g) {
  final nodes = lit(Family.set([for (var i = 0; i < g.length; i++) Int(i)]));
  final succ = successors(g);
  return fixDefined(nodes, (self, u) {
    final next = fresh('next');
    final through = fold(famWith(var_(next), (v) => get(self, v)), const PrimFn(Prim.add), lit(0));
    return Match(get(succ, u), [
      (const AtomP('notFound'), lit(1)),
      (BindP(next), add(lit(1), through)),
    ]);
  });
}

/// What `pathCounts` must compute on `g`: the counts, or, when some node reaches a cycle, the
/// stall naming every such node.
Object expected(Graph g) {
  final n = g.length;
  // A node reaches a cycle when it cannot be removed by repeatedly removing sinks.
  final count = List<int?>.filled(n, null);
  for (var changed = true; changed;) {
    changed = false;
    for (var u = 0; u < n; u++) {
      if (count[u] == null && g[u].every((v) => count[v] != null)) {
        count[u] = 1 + g[u].fold(0, (a, v) => a + count[v]!);
        changed = true;
      }
    }
  }
  final stalled = [
    for (var u = 0; u < n; u++)
      if (count[u] == null) Int(u),
  ];
  if (stalled.isNotEmpty) return StalledError(stalled);
  return Family.of([for (var u = 0; u < n; u++) (Int(u), Int(count[u]!))]);
}

/// Every directed graph on three nodes, self-loops included: 2^9 = 512 graphs.
List<Graph> allGraphsOnThreeNodes() => [
  for (var bits = 0; bits < 512; bits++)
    [
      for (var u = 0; u < 3; u++)
        [
          for (var v = 0; v < 3; v++)
            if (bits >> (u * 3 + v) & 1 == 1) v,
        ],
    ],
];

/// Random graphs on 4 to 8 nodes. Half are acyclic under a random topological order, so that
/// key order and dependency order differ; the rest have arbitrary edges.
List<Graph> randomGraphs(int seed) {
  final rng = Rng(seed);
  return [
    for (var i = 0; i < randomInstances; i++)
      () {
        final n = 4 + rng.below(5);
        final rank = [for (var j = 0; j < n; j++) j];
        for (var j = n - 1; j >= 1; j--) {
          final k = rng.below(j + 1);
          final t = rank[j];
          rank[j] = rank[k];
          rank[k] = t;
        }
        return [
          for (var u = 0; u < n; u++)
            [
              for (var v = 0; v < n; v++)
                if ((i % 2 == 1 || rank[u] > rank[v]) && rng.below(3) == 0) v,
            ],
        ];
      }(),
  ];
}

/// The edit distance between `a` and `b`, as a definedness `fix` over the cells `(i, j)` of
/// its table: the distance between the first `i` characters of `a` and the first `j` of `b`.
Term editDistance(String a, String b) {
  final (n, m) = (a.length, b.length);
  final cells = Family.set([
    for (var i = 0; i <= n; i++)
      for (var j = 0; j <= m; j++) Tuple([Int(i), Int(j)]),
  ]);
  Term chars(String w) => lit(Family.of([for (var k = 0; k < w.length; k++) (Int(k), s(w[k]))]));
  final (ca, cb) = (chars(a), chars(b));
  return fixDefined(lit(cells), (self, c) {
    final (i, j) = (nth(c, 0), nth(c, 1));
    Term at(int di, int dj) => get(self, prim(Prim.tuple, [sub(i, lit(di)), sub(j, lit(dj))]));
    Term min(Term x, Term y) => prim(Prim.min, [x, y]);
    final differ = if_(eq(get(ca, sub(i, lit(1))), get(cb, sub(j, lit(1)))), lit(0), lit(1));
    return if_(
      eq(i, lit(0)),
      j,
      if_(
        eq(j, lit(0)),
        i,
        min(min(add(at(1, 0), lit(1)), add(at(0, 1), lit(1))), add(at(1, 1), differ)),
      ),
    );
  });
}

/// The edit distance by the textbook table, for comparison.
int levenshtein(String a, String b) {
  final row = [for (var j = 0; j <= b.length; j++) j];
  for (var i = 1; i <= a.length; i++) {
    var prev = row[0];
    row[0] = i;
    for (var j = 1; j <= b.length; j++) {
      final here = row[j];
      row[j] = math.min(
        math.min(row[j] + 1, row[j - 1] + 1),
        prev + (a[i - 1] != b[j - 1] ? 1 : 0),
      );
      prev = here;
    }
  }
  return row[b.length];
}

Family strings(List<(String, String)> pairs) =>
    Family.of([for (final (k, v) in pairs) (s(k), s(v))]);

void main() {
  test('every schedule counts paths on every three-node graph or stalls on the same keys', () {
    var stalls = 0;
    for (final g in allGraphsOnThreeNodes()) {
      final want = expected(g);
      if (want is KernelError) stalls++;
      final t = pathCounts(g);
      for (final sch in schedules) {
        expect(run(t, sch), want, reason: '${nameOf(sch)} on $g');
      }
    }
    // Both outcomes are exercised: 25 of the 512 graphs are acyclic.
    expect(stalls, 512 - 25);
  });

  test('every schedule agrees on random graphs with dependencies out of key order', () {
    var acyclic = 0, partlyStalled = 0;
    for (final g in randomGraphs(21)) {
      final want = expected(g);
      switch (want) {
        case Family():
          acyclic++;
        case StalledError(:final keys) when keys.length < g.length:
          partlyStalled++;
      }
      final t = pathCounts(g);
      for (final sch in schedules) {
        expect(run(t, sch), want, reason: '${nameOf(sch)} on $g');
      }
    }
    // Both the defined case and a stall that leaves some entries defined occur.
    expect(acyclic, greaterThanOrEqualTo(randomInstances ~/ 2));
    expect(partlyStalled, greaterThan(0));
  });

  test('edit distance top-down memoized equals the bottom-up wavefront', () {
    // Memoized pull computes the table on demand from the first cell in key order; the
    // wavefront fills it by anti-diagonals. Both give every cell the same value.
    const pairs = [
      ('kitten', 'sitting'),
      ('flaw', 'lawn'),
      ('', 'abc'),
      ('intention', 'execution'),
      ('same', 'same'),
    ];
    for (final (a, b) in pairs) {
      final t = editDistance(a, b);
      final wave = run(t, const Rounds()) as Value;
      for (final sch in schedules) {
        expect(run(t, sch), wave, reason: '${nameOf(sch)} on "$a", "$b"');
      }
      final corner = Tuple([Int(a.length), Int(b.length)]);
      expect(wave.asFamily![corner], Int(levenshtein(a, b)), reason: '"$a", "$b"');
    }
  });

  test('a fix nested in another postpones the outer entry on an outer read', () {
    // Each department's cost is a running total over its three budget lines, computed by an
    // inner fix; line 0 starts from the cost of the department it reports to. A read of an
    // undefined outer entry inside the inner fix must postpone the outer entry, not stall the
    // inner fix, under every schedule.
    final reportsTo = lit(strings([('ops', 'hq'), ('eng', 'ops'), ('web', 'eng')]));
    final lines = lit(Family.set([const Int(0), const Int(1), const Int(2)]));
    final depts = lit(
      Family.set([
        for (final d in ['web', 'eng', 'ops', 'hq']) s(d),
      ]),
    );
    final cost = fixDefined(depts, (outer, d) {
      final running = fixDefined(lines, (inner, l) {
        final parent = get(outer, get(reportsTo, d));
        final start = Match(parent, [
          (const AtomP('notFound'), lit(100)),
          (const BindP('p'), var_('p')),
        ]);
        return if_(eq(l, lit(0)), start, add(get(inner, sub(l, lit(1))), mul(l, lit(10))));
      });
      return get(running, lit(2));
    });
    // hq: 100 + 10 + 20 = 130; ops: 130 + 30 = 160; eng: 190; web: 220.
    final want = Family.of([
      for (final (d, c) in const [('eng', 190), ('hq', 130), ('ops', 160), ('web', 220)])
        (s(d), Int(c)),
    ]);
    for (final sch in schedules) {
      expect(run(cost, sch), want, reason: nameOf(sch));
    }
  });

  test('a cycle through a nested fix stalls the outer entries only', () {
    // Two departments that report to each other: the outer fix stalls on both, and the inner
    // fix, whose own reads are all defined, is never the one reported.
    final reportsTo = lit(strings([('a', 'b'), ('b', 'a')]));
    final depts = lit(
      Family.set([
        for (final d in ['a', 'b', 'c']) s(d),
      ]),
    );
    final cost = fixDefined(depts, (outer, d) {
      final running = fixDefined(lit(Family.set([const Int(0), const Int(1)])), (inner, l) {
        return if_(
          eq(l, lit(0)),
          add(get(outer, get(reportsTo, d)), lit(0)),
          add(get(inner, sub(l, lit(1))), lit(1)),
        );
      });
      return get(running, lit(1));
    });
    for (final sch in schedules) {
      final got = run(cost, sch);
      expect(got, isA<StalledError>(), reason: nameOf(sch));
      expect((got as StalledError).keys.toSet(), {s('a'), s('b')}, reason: nameOf(sch));
    }
  });
}
