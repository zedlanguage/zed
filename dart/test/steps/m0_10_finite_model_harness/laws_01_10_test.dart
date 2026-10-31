/// Laws 1–10 of the catalog: the reindex, discard and fold equations, the join and packing
/// rules, the fold permissions, scan, and rank.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/check.dart';
import '../../support/instances.dart';
import '../../support/kernel.dart';
import 'harness.dart';

Term plus() => const PrimFn(Prim.add);

/// The two-argument function `(p, v) -> body(p, v)` a reindex or discard takes.
Term kv(Term Function(Term p, Term v) body) => func(2, (x) => body(x[0], x[1]));

/// Applies a two-argument function to a key and a value.
Term call(Term f, Term p, Term v) => app(f, [p, v]);

// Law 4: a fold of a group is reduce-by-key.

/// Reduce-by-key written directly: for each class `j`, the fold of the entries `f` sends to
/// `j`.
Term reduceByKey(Term m, Term Function(Term) f, Term op) {
  final classes = keyset(groupBy(m, f));
  return famWith(classes, (j) => fold(discardWith(m, (_, e) => eq(f(e), j)), op));
}

// Law 5: the entrywise forms distribute over a disjoint union.

/// Every split of the maps over the keys `0..3` into two domain-disjoint parts.
List<(IntMap, IntMap)> splits() => [
  for (final m in partialMaps([0, 1, 2], [-2, -1, 0, 1, 2]))
    for (var mask = 0; mask < 1 << m.length; mask++)
      (
        [
          for (var i = 0; i < m.length; i++)
            if (mask & (1 << i) != 0) m[i],
        ],
        [
          for (var i = 0; i < m.length; i++)
            if (mask & (1 << i) == 0) m[i],
        ],
      ),
];

// Law 6: a join is the disjoint union of its per-region discards.

enum Region { keep, drop, assertEmpty }

/// `true` unless `e` is the atom `#name`.
Term notAtom(Term e, String name) =>
    Match(e, [(AtomP(name), lit(false)), (const WildP(), lit(true))]);

Term pair(Term x, Term y) => prim(Prim.tuple, [x, y]);

/// `joinR(t)(a, b)` by its definition: each key of either operand is classified by region and
/// kept with its value pair, dropped, or, in an asserted-empty region, reported as
/// `#assertEmpty`, the failure the assertion stands for.
Term joinByDefinition(List<Region> t, Term a, Term b) {
  Term cell(Region r, Term pair) => switch (r) {
    Region.keep => pair,
    Region.drop => atom('drop'),
    Region.assertEmpty => atom('assertEmpty'),
  };
  final both = prim(Prim.union, [keyset(a), keyset(b)]);
  final classified = famWith(both, (k) {
    final (inA, inB) = (found(get(a, k)), found(get(b, k)));
    return if_(
      and(inA, inB),
      cell(t[1], pair(get(a, k), get(b, k))),
      if_(
        inA,
        cell(t[0], pair(get(a, k), atom('none'))),
        cell(t[2], pair(atom('none'), get(b, k))),
      ),
    );
  });
  return discardWith(classified, (_, e) => notAtom(e, 'drop'));
}

/// `joinR(t)(a, b)` as the disjoint union of the kept regions, each a discard of one operand.
Term joinByRegions(List<Region> t, Term a, Term b) {
  Term only(Term x, Term y, bool left) {
    final region = discardWith(x, (p, _) => not(found(get(y, key(p, 0)))));
    return famWith(
      region,
      (k) => left ? pair(get(x, k), atom('none')) : pair(atom('none'), get(x, k)),
    );
  }

  final inner = famWith(
    discardWith(a, (p, _) => found(get(b, key(p, 0)))),
    (k) => pair(get(a, k), get(b, k)),
  );
  final regions = [only(a, b, true), inner, only(b, a, false)];
  Term out = lit(const Family.empty());
  for (var i = 0; i < 3; i++) {
    if (t[i] == Region.keep) out = disjointUnion(out, regions[i], 1);
  }
  return out;
}

// Law 7: a catalog-bijective reindex and its inverse cancel.

const w = 3;

/// `(i, j) -> i * W + j`, packing a two-level family into one level.
Term pack() => kv((p, _) => path([add(mul(key(p, 0), lit(w)), key(p, 1))]));

/// `k -> (k div W, k mod W)`, Euclidean, or truncated toward zero when `truncated`.
Term unpack(bool truncated) => kv((p, _) {
  final k = key(p, 0);
  final Term q;
  if (truncated) {
    // Truncated division rounds a negative quotient up.
    final floor = idiv(k, lit(w));
    final inexact = not(eq(modulo(k, lit(w)), lit(0)));
    q = if_(and(lt(k, lit(0)), inexact), add(floor, lit(1)), floor);
  } else {
    q = idiv(k, lit(w));
  }
  return path([q, sub(k, mul(q, lit(w)))]);
});

typedef Cells = List<(int, int, int)>;

/// Grids `row -> column -> v` with rows `-2..=1`, columns `0..W` and every cell present with
/// probability one half.
List<Cells> grids() {
  final rng = Rng(7);
  return [
    for (var n = 0; n < 512; n++)
      [
        for (var i = -2; i <= 1; i++)
          for (var j = 0; j < w; j++)
            if (rng.below(2) == 0) (i, j, rng.int_(-8, 8)),
      ],
  ];
}

Term grid(Cells g) => lit(
  Family.fromLeaves([
    for (final (i, j, v) in g) ([Int(i), Int(j)], Int(v)),
  ]),
);

// Law 8: a fold may regroup, reorder and dedup, given the Boom row.

/// The map's values in chunks of two by key rank: `(rank div 2) -> rank -> v`.
Term chunked(IntMap m) => lit(
  Family.fromLeaves([
    for (var r = 0; r < m.length; r++) ([Int(r ~/ 2), Int(r)], Int(m[r].$2)),
  ]),
);

// Law 9: scan is the prefix-fold family.

/// The scan as the sequential recurrence `acc[0] = xs[0]`, `acc[i] = op(acc[i-1], xs[i])`.
Term scanSequential(Term xs, Term op) => fixDefined(xs, (self, i) {
  return if_(eq(i, lit(0)), get(xs, lit(0)), app(op, [get(self, sub(i, lit(1))), get(xs, i)]));
});

// Law 10: rank is a widen.

/// The dense rank each entry's class gets, read off the evaluated widen: `key -> rank`.
List<(int, int)> ranksOf(Value ranked) {
  final out = [for (final (kp, _) in ranked.asFamily!.leaves()) (kp[1].asInt!, kp[0].asInt!)];
  out.sort((x, y) => x.$1 != y.$1 ? x.$1.compareTo(y.$1) : x.$2.compareTo(y.$2));
  return out;
}

/// A sort key and a comparator on it, in Dart.
typedef SortKey = (int Function(int), bool Function(int, int));

/// Whether the widen by sort key `f` and comparator `less` ranks a map as a total preorder
/// does: one entry per key, dense ranks from 0, equal ranks exactly for entries whose keys
/// tie, and a lower rank exactly for a smaller key. `fDart` and `lessDart` are `f` and `less`
/// in Dart. Returns why it does not, or null.
String? rankedAsAPreorder(
  IntMap m,
  SortKey key,
  Term Function(Term) f,
  Term Function(Term, Term) less,
) {
  final (fDart, lessDart) = key;
  final Value out;
  try {
    out = eval(rankWiden(ints(m), f, less));
  } on KernelError catch (e) {
    return '$e';
  }
  final ranks = ranksOf(out);
  if (ranks.length != m.length) return '${ranks.length} entries ranked, ${m.length} given';
  final used = {for (final r in ranks) r.$2}.toList()..sort();
  for (var i = 0; i < used.length; i++) {
    if (used[i] != i) return 'ranks $used are not dense';
  }
  for (var i = 0; i < m.length; i++) {
    for (var j = 0; j < m.length; j++) {
      final (x, rx, y, ry) = (m[i].$2, ranks[i].$2, m[j].$2, ranks[j].$2);
      final (fx, fy) = (fDart(x), fDart(y));
      final tied = !lessDart(fx, fy) && !lessDart(fy, fx);
      if ((rx == ry) != tied || (rx < ry) != lessDart(fx, fy)) {
        return '$x at rank $rx and $y at rank $ry';
      }
    }
  }
  return null;
}

void main() {
  // Law 1: composed reindexes.

  test('law 1: a composed reindex reads the value the first stage produced', () {
    // Move each account to a new id, triple its balance, then file it under its new balance.
    final kg = kv((p, _) => path([add(key(p, 0), lit(10))]));
    final vg = kv((_, v) => mul(v, lit(3)));
    final kf = kv((p, v) => path([v, key(p, 0)]));
    final vf = kv((_, v) => add(v, lit(1)));
    Term twoStage(IntMap m) => reindex(reindex(ints(m), kg, vg), kf, vf);
    (Term, Term) fusedWith(bool firstValue) => (
      kv((p, v) => call(kf, call(kg, p, v), firstValue ? call(vg, p, v) : v)),
      kv((p, v) => call(vf, call(kg, p, v), call(vg, p, v))),
    );
    var (k, wf) = fusedWith(true);
    final n = holds(intMaps(1), (m) => (twoStage(m), reindex(ints(m), k, wf)));
    expect(n, greaterThanOrEqualTo(1800));
    // The counterexample: the fused key map reads the value from before the first stage.
    (k, wf) = fusedWith(false);
    final (m, _, _) = refuted(intMaps(1), (m) => (twoStage(m), reindex(ints(m), k, wf)));
    expect(m.any((e) => e.$2 != 0), isTrue);
  });

  test('law 1: the identity reindex is the identity on levels that are not empty', () {
    final idK = kv((p, _) => p);
    final idV = kv((_, v) => v);
    final n = holds(intMaps(2), (m) => (reindex(ints(m), idK, idV), ints(m)));
    expect(n, greaterThanOrEqualTo(1800));
    // The nonempty-level condition has no counterexample among kernel values: a key over an
    // empty level has no keypath, so a value never holds one (sec:values_morphisms). It
    // constrains a guaranteed domain, which may claim a key whose level turns out empty; the
    // `card` facts that discharge it are checked at steps L1.24 and L3.6.
    Value warehouses(bool east) => eval(
      family([
        (s('west'), Family.of([(s('bolts'), const Int(40))])),
        if (east) (s('east'), const Family.empty()),
      ]),
    );
    expect(warehouses(true), warehouses(false));
  });

  // Law 2: a discard moves below a reindex as the composed predicate.

  test('law 2: a filter after a reindex moves below it', () {
    // Negate each key and square each value, then keep the entries whose new key is below the
    // new value.
    final kf = kv((p, _) => path([sub(lit(0), key(p, 0))]));
    final vf = kv((_, v) => mul(v, v));
    final sel = kv((p, e) => lt(key(p, 0), e));
    Term lhs(IntMap m) => discard(reindex(ints(m), kf, vf), sel);
    Term pushed(Term composed, IntMap m) => reindex(discard(ints(m), composed), kf, vf);
    final composed = kv((p, v) => call(sel, call(kf, p, v), call(vf, p, v)));
    final n = holds(intMaps(3), (m) => (lhs(m), pushed(composed, m)));
    expect(n, greaterThanOrEqualTo(1800));
    // Composing with the key map only, so the predicate reads the old value, is wrong.
    final keyOnly = kv((p, v) => call(sel, call(kf, p, v), v));
    refuted(intMaps(3), (m) => (lhs(m), pushed(keyOnly, m)));
  });

  test('law 2: right to left needs the reindex collision-free on all of F', () {
    // File readings under their value: two equal readings collide, unless the filter that was
    // pushed below drops both.
    final kf = kv((_, v) => path([v]));
    final vf = kv((_, v) => v);
    final sel = kv((_, e) => not(eq(e, lit(1))));
    final composed = kv((p, v) => call(sel, call(kf, p, v), call(vf, p, v)));
    final (m, a, b) = refuted(
      intMaps(4),
      (m) => (discard(reindex(ints(m), kf, vf), sel), reindex(discard(ints(m), composed), kf, vf)),
    );
    expect(a, isA<CollisionError>());
    expect(b, isA<Value>());
    expect(m.where((e) => e.$2 == 1).length, 2);
  });

  // Law 3: a fold of a map is the fused fold.

  test('law 3: a fold of a map is the fused fold on integers', () {
    Term f(Term v) => add(mul(v, v), lit(1));
    final n = holds(
      intMaps(5),
      (m) => (
        fold(map(ints(m), f), plus(), lit(0)),
        fold(famWith(ints(m), (k) => f(get(ints(m), k))), plus(), lit(0)),
      ),
    );
    expect(n, greaterThanOrEqualTo(1800));
  });

  test('law 3: a fold of a map is the fused fold on floats', () {
    // A float `+` fold is the exact sum rounded once on both sides.
    final floats = shortlex(bmcFloatValues(), 3);
    Term shift(Term v) => add(v, lit(Float(0.1)));
    final n = holds(
      floats,
      (xs) => (
        fold(map(seq(xs), shift), plus()),
        fold(famWith(seq(xs), (k) => shift(get(seq(xs), k))), plus()),
      ),
    );
    expect(n, 1 + 9 + 81 + 729);
  });

  test('law 4: a fold of a group is reduce-by-key', () {
    Term byResidue(Term v) => modulo(v, lit(3));
    for (final op in [plus(), const PrimFn(Prim.min), const PrimFn(Prim.sub)]) {
      final n = holds(
        intMaps(6),
        (m) => (foldAt(groupBy(ints(m), byResidue), 2, op), reduceByKey(ints(m), byResidue, op)),
      );
      expect(n, greaterThanOrEqualTo(1800));
    }
    // `-` holds too: both sides fold each class in key order. The Boom-row condition is for
    // the implementations that do not, such as a fold split across workers (law 8).
  });

  test('law 5: group, map and filter distribute over a disjoint union', () {
    Term du(IntMap a, IntMap b) => disjointUnion(ints(a), ints(b), 1);
    Term parity(Term v) => modulo(v, lit(2));
    final n = holds(
      splits(),
      (s) => (
        groupBy(du(s.$1, s.$2), parity),
        disjointUnion(groupBy(ints(s.$1), parity), groupBy(ints(s.$2), parity), 2),
      ),
    );
    // Each map over three keys splits in 2^|m| ways: (1 + 5 * 2)^3 instances.
    expect(n, 1331);
    Term tripled(Term v) => mul(v, lit(3));
    holds(
      splits(),
      (s) => (
        map(du(s.$1, s.$2), tripled),
        disjointUnion(map(ints(s.$1), tripled), map(ints(s.$2), tripled), 1),
      ),
    );
    Term positive(Term _, Term e) => lt(lit(0), e);
    holds(
      splits(),
      (s) => (
        discardWith(du(s.$1, s.$2), positive),
        disjointUnion(discardWith(ints(s.$1), positive), discardWith(ints(s.$2), positive), 1),
      ),
    );
    // A key map that collides across `a` and `b` is rejected on both sides.
    final byValue = kv((_, v) => path([v]));
    final idV = kv((_, v) => v);
    (Term, Term) collide((IntMap, IntMap) s) => (
      reindex(du(s.$1, s.$2), byValue, idV),
      disjointUnion(reindex(ints(s.$1), byValue, idV), reindex(ints(s.$2), byValue, idV), 1),
    );
    final IntMap left = [(0, 5)], right = [(1, 5)];
    expect(outcome(collide((left, right)).$1), isA<CollisionError>());
    holds([(left, right)], collide);
  });

  test('law 5: a filter that reads rank is not linear', () {
    // `take(1)`: keep the entry with the least key, which reads the entry's rank in its
    // family, so it differs on the parts and on the whole.
    Term takeFirst(Term f) => discardWith(f, (p, _) {
      return eq(count(discardWith(f, (q, _) => lt(key(q, 0), key(p, 0)))), lit(0));
    });
    final (_, a, b) = refuted(
      splits(),
      (s) => (
        takeFirst(disjointUnion(ints(s.$1), ints(s.$2), 1)),
        disjointUnion(takeFirst(ints(s.$1)), takeFirst(ints(s.$2)), 1),
      ),
    );
    expect(a, isNot(b));
  });

  test('law 6: a join is the union of its regions', () {
    final ms = partialMaps([0, 1, 2], [1, 2]);
    final pairs = [
      for (final a in ms)
        for (final b in ms) (a, b),
    ];
    bool regionsEmpty(List<Region> t, (IntMap, IntMap) s) {
      final ka = {for (final e in s.$1) e.$1}, kb = {for (final e in s.$2) e.$1};
      final nonempty = [
        ka.any((k) => !kb.contains(k)),
        ka.any(kb.contains),
        kb.any((k) => !ka.contains(k)),
      ];
      return [for (var i = 0; i < 3; i++) t[i] != Region.assertEmpty || !nonempty[i]]
          .every((x) => x);
    }

    const keep = Region.keep, drop = Region.drop, assertEmpty = Region.assertEmpty;
    const triples = [
      [drop, keep, drop], // inner
      [keep, keep, drop], // left outer
      [keep, keep, keep], // full outer
      [keep, drop, keep], // symmetric difference
      [keep, drop, drop], // difference
      [keep, assertEmpty, keep], // disjoint union
      [assertEmpty, keep, assertEmpty], // equality join (zip)
      [assertEmpty, keep, drop], // foreign key
    ];
    for (final t in triples) {
      (Term, Term) sides((IntMap, IntMap) s) =>
          (joinByDefinition(t, ints(s.$1), ints(s.$2)), joinByRegions(t, ints(s.$1), ints(s.$2)));
      final ok = pairs.where((p) => regionsEmpty(t, p));
      final n = holds(ok, sides);
      expect(n, greaterThanOrEqualTo(8), reason: '$t ran on $n instances');
      if (t.contains(assertEmpty)) {
        // The side condition: on operands where an asserted region is not empty, the regions'
        // union silently loses its keys.
        final bad = pairs.where((p) => !regionsEmpty(t, p));
        final (_, a, _) = refuted(bad, sides);
        expect((a as Value).toString(), contains('#assertEmpty'));
      }
    }
  });

  test('law 7: affine packing round-trips with euclidean division', () {
    final idV = kv((_, v) => v);
    (Term, Term) roundTrip(bool truncated, Cells g) {
      final packed = reindex(grid(g), pack(), idV);
      return (reindex(packed, unpack(truncated), idV), grid(g));
    }

    expect(holds(grids(), (g) => roundTrip(false, g)), 512);
    // The other direction, on one level over the packed keys `-8..=8`.
    final n = holds(intMaps(8), (m) {
      final IntMap shifted = [for (final (k, v) in m) (k - 2, v)];
      final unpacked = reindex(ints(shifted), unpack(false), idV);
      return (reindex(unpacked, pack(), idV), ints(shifted));
    });
    expect(n, greaterThanOrEqualTo(1800));
    // Truncated division sends a negative row's cells to the wrong row.
    final (g, _, _) = refuted(grids(), (g) => roundTrip(true, g));
    expect(g.any((c) => c.$1 < 0 && c.$2 != 0), isTrue);
  });

  test('law 8: an associative fold regroups', () {
    for (final op in [plus(), const PrimFn(Prim.max)]) {
      final n = holds(intMaps(9), (m) => (fold(foldAt(chunked(m), 2, op), op), fold(ints(m), op)));
      expect(n, greaterThanOrEqualTo(1800));
    }
    // `-` is not associative.
    const minus = PrimFn(Prim.sub);
    final (m, _, _) = refuted(
      intMaps(9),
      (m) => (fold(foldAt(chunked(m), 2, minus), minus), fold(ints(m), minus)),
    );
    expect(m.length, greaterThanOrEqualTo(3));
  });

  test('law 8: regrouping a float sum rounds more than once', () {
    // A float `+` fold is the exact sum rounded once; partial sums round each chunk.
    final xs = [Float(0.1), Float(0.2), Float(0.3)];
    final chunks = lit(
      Family.fromLeaves([
        ([const Int(0), const Int(0)], xs[0]),
        ([const Int(0), const Int(1)], xs[1]),
        ([const Int(1), const Int(2)], xs[2]),
      ]),
    );
    final (_, a, b) = refuted([()], (_) {
      return (fold(foldAt(chunks, 2, plus()), plus()), fold(seq(xs), plus()));
    });
    expect((a, b), (Float(0.1 + 0.2 + 0.3), Float(0.6)));
  });

  test('law 8: a commutative fold reorders', () {
    Term reversed(IntMap m) =>
        reindex(ints(m), kv((p, _) => path([sub(lit(0), key(p, 0))])), kv((_, v) => v));
    holds(intMaps(10), (m) => (fold(reversed(m), plus()), fold(ints(m), plus())));
    // `first` is associative but not commutative.
    final first = func(2, (x) => x[0]);
    refuted(intMaps(10), (m) => (fold(reversed(m), first), fold(ints(m), first)));
  });

  test('law 8: an idempotent fold dedups', () {
    Term distinct(IntMap m) => keyset(groupBy(ints(m), (v) => v));
    const max = PrimFn(Prim.max);
    holds(intMaps(11), (m) => (fold(keyset(distinct(m)), max), fold(ints(m), max)));
    // `+` is not idempotent: a repeated value counts twice.
    final (m, _, _) = refuted(
      intMaps(11),
      (m) => (fold(keyset(distinct(m)), plus()), fold(ints(m), plus())),
    );
    final vs = [for (final e in m) e.$2];
    expect(vs.any((v) => vs.where((x) => x == v).length > 1), isTrue);
  });

  test('law 9: scan is the prefix-fold family', () {
    final seqs = shortlex([-2, -1, 0, 1, 2, 5], 4);
    for (final op in [plus(), const PrimFn(Prim.max)]) {
      final n = holds(seqs, (xs) => (scan(seq(xs), op), scanSequential(seq(xs), op)));
      expect(n, 1 + 6 + 36 + 216 + 1296);
    }
    // `-` is not associative, so the prefix folds' trees disagree with the recurrence.
    const minus = PrimFn(Prim.sub);
    final (xs, _, _) = refuted(
      seqs,
      (xs) => (scan(seq(xs), minus), scanSequential(seq(xs), minus)),
    );
    expect(xs.length, greaterThanOrEqualTo(3));
  });

  test('law 10: rank groups tied entries under a dense rank', () {
    final SortKey byValue = ((x) => x, (x, y) => x < y);
    final n = property(intMaps(12), (m) => rankedAsAPreorder(m, byValue, (v) => v, lt));
    expect(n, greaterThanOrEqualTo(1800));
    // By absolute value: `-2` and `2` tie, and share a rank.
    Term abs(Term v) => if_(lt(v, lit(0)), sub(lit(0), v), v);
    final SortKey byAbs = ((x) => x.abs(), (x, y) => x < y);
    property(intMaps(12), (m) => rankedAsAPreorder(m, byAbs, abs, lt));
    // A near-tie relation, `y - x >= 2`, is not a preorder whose ties are an equivalence: 0
    // ties 1 and 1 ties 2, but 0 is below 2.
    final SortKey near = ((x) => x, (x, y) => y - x >= 2);
    final (m, _) = propertyRefuted(
      intMaps(12),
      (m) => rankedAsAPreorder(m, near, (v) => v, (x, y) => le(lit(2), sub(y, x))),
    );
    expect(m.length, greaterThanOrEqualTo(2));
  });
}
