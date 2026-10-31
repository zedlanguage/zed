/// Laws 21–28 of the catalog: folds over a recursive union, bisection, tupling, lookup
/// through reduce-by-key, fix fusion, generation fusion, the update laws of `with`, and
/// reversal.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/check.dart';
import '../../support/instances.dart';
import '../../support/kernel.dart';
import 'harness.dart';

Term plus() => pf(Prim.add);

Term tuple(List<Term> items) => prim(Prim.tuple, items);

/// `first`: the entry with the least key.
Term first() => func(2, (x) => x[0]);

/// The last frame of a `gen` result.
Term lastFrame(Term frames, Term Function(Term) then) {
  final g = fresh('g');
  final last = get(var_(g), sub(count(var_(g)), lit(1)));
  return let_(g, frames, then(last));
}

// Law 21: fold uniqueness and fusion over a recursive union.

/// A binary tree as a node table `i -> (v, left, right)` with the root at 0 and -1 for an
/// absent child: the recursive union `Node(v, l, r) | Empty` with each node named by its
/// preorder number.
typedef Tree = List<(int, int, int)>;

/// Every shape of `n` nodes numbered in preorder from `o`, as each node's children.
List<List<(int, int)>> shapes(int n, int o) {
  if (n == 0) return [[]];
  return [
    for (var a = 0; a < n; a++)
      for (final l in shapes(a, o + 1))
        for (final r in shapes(n - 1 - a, o + 1 + a))
          [(a > 0 ? o + 1 : -1, n - 1 - a > 0 ? o + 1 + a : -1), ...l, ...r],
  ];
}

/// Every tree of one to three nodes with values in `-2..=2`, then random trees of up to
/// eight nodes with values in `-8..=8`.
List<Tree> trees() {
  final out = <Tree>[
    for (var n = 1; n <= 3; n++)
      for (final shape in shapes(n, 0))
        for (final vs in shortlex(const [-2, -1, 0, 1, 2], n))
          if (vs.length == n) [for (var i = 0; i < n; i++) (vs[i], shape[i].$1, shape[i].$2)],
  ];
  final rng = Rng(21);
  final bySize = [for (var n = 0; n <= 8; n++) shapes(n, 0)];
  for (var i = 0; i < 256; i++) {
    final shape = rng.pick(bySize[rng.int_(1, 8)]);
    out.add([for (final (l, r) in shape) (rng.int_(-8, 8), l, r)]);
  }
  return out;
}

Term tree(Tree t) => lit(
  Family.of([
    for (var i = 0; i < t.length; i++) (Int(i), Tuple([Int(t[i].$1), Int(t[i].$2), Int(t[i].$3)])),
  ]),
);

/// `t.fold(alg)` at the root: `empty` at an absent child, `node(v, l, r)` with the children's
/// results at a node, as the definedness fix over the node table.
Term treeFold(Term t, Term empty, Term Function(Term v, Term l, Term r) node) {
  final all = fixDefined(t, (self, k) {
    final n = get(t, k);
    Term child(Term c) => if_(eq(c, lit(-1)), empty, get(self, c));
    return node(nth(n, 0), child(nth(n, 1)), child(nth(n, 2)));
  });
  return get(all, lit(0));
}

Term treeSum(Term t) => treeFold(t, lit(0), (v, l, r) => add(add(v, l), r));

/// The heap-shaped tree over a sequence: node `i` holds `xs[i]` with children `2i + 1` and
/// `2i + 2` where those are in range.
Term heapBuild(Term xs) {
  final n = count(xs);
  return famWith(xs, (i) {
    Term child(Term c) => if_(lt(c, n), c, lit(-1));
    return tuple([
      get(xs, i),
      child(add(mul(lit(2), i), lit(1))),
      child(add(mul(lit(2), i), lit(2))),
    ]);
  });
}

// Law 22: bisection.

/// The least `xs[i]` with `p(xs[i])`, found by halving the range of ranks `lo..hi`.
Term bisect(Term xs, Term Function(Term) p) {
  final n = count(xs);
  final step = func(1, (x) {
    final (lo, hi) = (nth(x[0], 0), nth(x[0], 1));
    final mid = idiv(add(lo, hi), lit(2));
    return if_(p(get(xs, mid)), tuple([lo, mid]), tuple([add(mid, lit(1)), hi]));
  });
  final frames = Gen(
    tuple([lit(0), n]),
    step,
    func(1, (x) => lt(nth(x[0], 0), nth(x[0], 1))),
    GuardPos.before,
  );
  return lastFrame(frames, (last) {
    final lo = nth(last, 0);
    return if_(lt(lo, n), get(xs, lo), atom('empty'));
  });
}

/// Each ascending sequence of at most four values in `-3..=3`, with each threshold in
/// `-4..=4`.
List<(List<int>, int)> sortedWithThresholds() => [
  for (final xs in shortlex([for (var v = -3; v <= 3; v++) v], 4))
    if ([for (var i = 1; i < xs.length; i++) xs[i - 1] <= xs[i]].every((b) => b))
      for (var t = -4; t <= 4; t++) (xs, t),
];

// Law 23: tupling.

/// The two folds of a level, and the one fold at the pair.
(Term, Term) tupled(Term m, Term? sumId, Term? maxId) {
  final pairId = sumId != null && maxId != null ? tuple([sumId, maxId]) : null;
  final both = func(2, (x) {
    final (a, b) = (x[0], x[1]);
    return tuple([
      add(nth(a, 0), nth(b, 0)),
      prim(Prim.max, [nth(a, 1), nth(b, 1)]),
    ]);
  });
  Term square(Term v) => mul(v, v);
  return (
    tuple([
      fold(map(m, square), plus(), sumId),
      fold(map(m, (v) => sub(lit(0), v)), pf(Prim.max), maxId),
    ]),
    fold(map(m, (v) => tuple([square(v), sub(lit(0), v)])), both, pairId),
  );
}

// Law 25: fix fusion.

/// The row `s` of a relation, as a set of nodes.
Term row(Term r, int s) =>
    discardWith(famWith(nodes(), (w) => found(get(get(r, lit(s)), w))), (_, e) => e);

/// `v · E` for a set of nodes `v`: the successors of the nodes of `v`.
Term successors(Term v, Term e) => discardWith(
  famWith(nodes(), (w) {
    final via = discardWith(v, (p, _) => found(get(get(e, key(p, 0)), w)));
    return lt(lit(0), count(via));
  }),
  (_, x) => x,
);

// Law 26: generation fusion.

/// A loan simulation: frames `(month, balance, audit)` from `(0, x0, y0)`, each month adding
/// the month number to the balance and doubling the audit counter.
Term loan(int x0, int y0, Term guard) {
  final step = func(1, (x) {
    final f = x[0];
    return tuple([add(nth(f, 0), lit(1)), add(nth(f, 1), nth(f, 0)), mul(nth(f, 2), lit(2))]);
  });
  return Gen(lit(Tuple([const Int(0), Int(x0), Int(y0)])), step, guard, GuardPos.before);
}

Term abstractLoan(int x0) {
  final step = func(1, (x) {
    final f = x[0];
    return tuple([add(nth(f, 0), lit(1)), add(nth(f, 1), nth(f, 0))]);
  });
  return Gen(
    lit(Tuple([const Int(0), Int(x0)])),
    step,
    func(1, (x) => lt(nth(x[0], 0), lit(4))),
    GuardPos.before,
  );
}

List<(int, int)> seeds() => [
  for (var x = -2; x <= 2; x++)
    for (var y = 1; y <= 4; y++) (x, y),
];

// Law 27: the update laws of `with`.

/// An inventory record `{"price" -> {item -> n}, "stock" -> {item -> n}}`, as its two maps.
typedef Record = (List<(int, int)>, List<(int, int)>);

/// A `with` path: a field step, then an optional key step.
typedef UpdatePath = (String, int?);

List<Record> records() {
  final maps = partialMaps(const [0, 1], const [1, 2]);
  return [
    for (final p in maps)
      for (final s in maps) (p, s),
  ];
}

Term record(Record r) => lit(
  Family.fromLeaves([
    for (final (field, m) in [('price', r.$1), ('stock', r.$2)])
      for (final (k, v) in m) ([s(field), Int(k)], Int(v)),
  ]),
);

List<UpdatePath> paths() => [
  for (final field in const ['price', 'stock']) ...[
    (field, null),
    for (var k = 0; k < 3; k++) (field, k),
  ],
];

List<Term> steps(UpdatePath p) => [lit(s(p.$1)), if (p.$2 case final k?) lit(k)];

/// Whether every key step of `p` is present in `r`; a field is present while its map is
/// nonempty, since an empty level drops its key.
bool present(Record r, UpdatePath p) {
  final m = p.$1 == 'price' ? r.$1 : r.$2;
  return m.isNotEmpty && (p.$2 == null || m.any((e) => e.$1 == p.$2));
}

bool prefixRelated(UpdatePath p, UpdatePath q) =>
    p.$1 == q.$1 && (p.$2 == null || q.$2 == null || p.$2 == q.$2);

/// The value a test writes at `p`: a price list at a field path, a number at a key path.
Term written(UpdatePath p, int n) =>
    p.$2 == null ? lit(Family.of([(const Int(0), Int(n))])) : lit(n);

Term read(Term v, List<Term> p) => p.fold(v, get);

/// `v with { p = a }`: a key step rebuilds its level with the key's entry updated, and is
/// `#missing` where the key is absent. A failure in `v` flows out unchanged.
Term update(Term v, List<Term> p, Term a) {
  if (p.isEmpty) return a;
  final k = p.first;
  final inner = update(get(v, k), p.sublist(1), a);
  final level = famWith(v, (j) => if_(eq(j, k), inner, get(v, j)));
  return unlessAtom(v, if_(found(get(v, k)), level, atom('missing')));
}

List<(Record, UpdatePath)> withPaths() => [
  for (final r in records())
    for (final p in paths()) (r, p),
];

List<(Record, UpdatePath, UpdatePath)> withPathPairs() => [
  for (final r in records())
    for (final p in paths())
      for (final q in paths()) (r, p, q),
];

// Law 28: reversal.

/// `xs` read in the reverse of its order, as the sequence `i -> xs[n - 1 - i]`.
Term rev(Term xs) {
  final n = count(xs);
  return reindex(
    xs,
    func(2, (x) => path([sub(sub(n, lit(1)), key(x[0], 0))])),
    func(2, (x) => x[1]),
  );
}

void main() {
  test('law 21: two functions that satisfy one fold equation are equal', () {
    // The number of employees under a manager in an org chart: the table's count satisfies
    // `size(Node(v, l, r)) = 1 + size(l) + size(r)` and `size(Empty) = 0`, so it is the fold.
    final n = holds(trees(), (t) {
      return (count(tree(t)), treeFold(tree(t), lit(0), (_, l, r) => add(add(lit(1), l), r)));
    });
    expect(n, 5 + 2 * 25 + 5 * 125 + 256);
  });

  test('law 21: a function of a fold is a fold when it commutes with one layer', () {
    // Converting a cost tree's total to another unit, `h(x) = 3x`, is the fold that converts
    // each node's own cost: `h(v + l + r) = 3v + h(l) + h(r)` and `h(0) = 0`.
    final n = holds(trees(), (t) {
      return (
        mul(lit(3), treeSum(tree(t))),
        treeFold(tree(t), lit(0), (v, l, r) => add(add(mul(lit(3), v), l), r)),
      );
    });
    expect(n, greaterThan(900));
    // `x * x` does not commute with the layer: the square of a sum is not the sum of squares.
    Term square(Term x) => mul(x, x);
    final (t, _, _) = refuted(trees(), (t) {
      return (
        square(treeSum(tree(t))),
        treeFold(tree(t), lit(0), (v, l, r) => add(add(square(v), l), r)),
      );
    });
    expect(t.length, greaterThanOrEqualTo(2));
  });

  test('law 21: over a mutual recursion the equations hold componentwise', () {
    // Two mutually recursive functions over the levels of a tree: `even(n)` sums the values
    // at even depth below and at `n`, `odd(n)` those at odd depth, as one fold at the pair.
    // Their difference, the alternating sum, is the fold `v - h(l) - h(r)`.
    final n = holds(trees(), (t) {
      final pair = treeFold(tree(t), tuple([lit(0), lit(0)]), (v, l, r) {
        return tuple([add(add(v, nth(l, 1)), nth(r, 1)), add(nth(l, 0), nth(r, 0))]);
      });
      final p = fresh('p');
      return (
        let_(p, pair, sub(nth(var_(p), 0), nth(var_(p), 1))),
        treeFold(tree(t), lit(0), (v, l, r) => sub(sub(v, l), r)),
      );
    });
    expect(n, greaterThan(900));
  });

  test('law 21: a fold of a build is the recursion on seeds', () {
    // The height of a binary heap built from an array, computed without the heap: `go(i)`
    // recurses on the array indices the build would make children of.
    Term height(Term _, Term l, Term r) => add(lit(1), prim(Prim.max, [l, r]));
    final n = holds(shortlex(const [-2, -1, 0, 1, 2], 4), (vs) {
      final xs = seq(vs);
      final n = count(xs);
      final go = fixDefined(xs, (self, i) {
        Term at(Term c) => if_(lt(c, n), get(self, c), lit(0));
        return add(
          lit(1),
          prim(Prim.max, [at(add(mul(lit(2), i), lit(1))), at(add(mul(lit(2), i), lit(2)))]),
        );
      });
      return (treeFold(heapBuild(xs), lit(0), height), get(go, lit(0)));
    });
    expect(n, 1 + 5 + 25 + 125 + 625);
  });

  test('law 22: a monotone predicate on a sorted level bisects', () {
    // The first delivery slot at or after a requested time, in a sorted timetable.
    final n = holds(sortedWithThresholds(), (c) {
      final (xs, t) = c;
      Term atLeast(Term v) => le(lit(t), v);
      return (fold(discardWith(seq(xs), (_, v) => atLeast(v)), first()), bisect(seq(xs), atLeast));
    });
    expect(n, 330 * 9);
    // `v == t` is not monotone along the order: bisection skips past an equal entry.
    final ((xs, t), _, _) = refuted(sortedWithThresholds(), (c) {
      final (xs, t) = c;
      Term equal(Term v) => eq(v, lit(t));
      return (fold(discardWith(seq(xs), (_, v) => equal(v)), first()), bisect(seq(xs), equal));
    });
    expect(xs, contains(t));
  });

  test('law 23: two folds of one level are one pass', () {
    // The sum of squared errors and the largest negative error of a batch, in one pass.
    final nonempty = [
      for (final m in intMaps(23))
        if (m.isNotEmpty) m,
    ];
    expect(holds(nonempty, (m) => tupled(ints(m), null, null)), greaterThanOrEqualTo(1800));
    // On an empty level, the fused fold gives one `#empty` where the pair has two.
    final (m, a, _) = refuted(intMaps(23), (m) => tupled(ints(m), null, null));
    expect(m, isEmpty);
    expect(a, const Tuple([Atom('empty'), Atom('empty')]));
    // With identities, the empty case is the pair of the two identities.
    final n = holds(intMaps(23), (m) => tupled(ints(m), lit(0), lit(-100)));
    expect(n, greaterThanOrEqualTo(1800));
  });

  test('law 23: a float component keeps its own exact accumulator', () {
    // The exact float sum of `fold(+)` is not the canonical-tree sum a fused fold with a
    // pairing operator computes; the fusion keeps the accumulator per component.
    final nonempty = shortlex(bmcFloatValues(), 3).where((xs) => xs.isNotEmpty);
    final both = func(2, (x) {
      final (a, b) = (x[0], x[1]);
      return tuple([add(nth(a, 0), nth(b, 0)), add(nth(a, 1), nth(b, 1))]);
    });
    final (xs, _, _) = refuted(nonempty, (xs) {
      return (
        tuple([fold(seq(xs), plus()), fold(seq(xs), plus())]),
        fold(map(seq(xs), (v) => tuple([v, v])), both),
      );
    });
    expect(xs.length, 3);
  });

  test('law 23: over a recursive union two folds are one fold at the pair', () {
    // A cost tree's node count and total cost in one traversal.
    final n = holds(trees(), (t) {
      return (
        tuple([treeFold(tree(t), lit(0), (_, l, r) => add(add(lit(1), l), r)), treeSum(tree(t))]),
        treeFold(tree(t), tuple([lit(0), lit(0)]), (v, l, r) {
          return tuple([add(add(lit(1), nth(l, 0)), nth(r, 0)), add(add(v, nth(l, 1)), nth(r, 1))]);
        }),
      );
    });
    expect(n, greaterThan(900));
  });

  test('law 24: one class of a reduce-by-key is the fold of its fiber', () {
    // Total sales in one region, `v mod 3`, without computing the other regions.
    Term region(Term v) => modulo(v, lit(3));
    final cases = [
      for (final m in partialMaps(const [0, 1, 2, 3], const [-2, -1, 0, 1, 2]))
        for (var j = 0; j < 3; j++) (m, j),
    ];
    (Term, Term) sides((List<(int, int)>, int) c) {
      final (m, j) = c;
      return (
        get(foldAt(groupBy(ints(m), region), 2, plus()), lit(j)),
        fold(discardWith(ints(m), (_, v) => eq(region(v), lit(j))), plus()),
      );
    }

    bool inImage((List<(int, int)>, int) c) => c.$1.any((e) => e.$2 % 3 == c.$2);
    expect(holds(cases.where(inImage), sides), greaterThan(2000));
    // Outside the image the class is absent, while the fiber is an empty level.
    final (_, a, b) = refuted(cases, sides);
    expect((a, b), (const Atom('notFound'), const Atom('empty')));
  });

  test('law 25: one row of a closure is a search from its source', () {
    // The stations reachable from station 0, without the whole reachability table.
    final n = holds(relations(), (pairs) {
      final e = relation(pairs);
      return (
        row(fixLattice(e, func(1, (r) => compose(r[0], e)), pf(Prim.union)), 0),
        fixLattice(row(e, 0), func(1, (v) => successors(v[0], e)), pf(Prim.union)),
      );
    });
    expect(n, 512 + 256);
  });

  test('law 25: a left-multiplied step takes the invariant form', () {
    // `r[s]` does not commute with `r -> E · r` on every relation.
    final rs = relations();
    final pairs = [for (var i = 0; i < rs.length; i++) (rs[i], rs[(i * 7 + 3) % rs.length])];
    refuted(pairs, (c) {
      final (e, r) = (relation(c.$1), relation(c.$2));
      return (row(compose(e, r), 0), successors(row(r, 0), e));
    });
    // On the iterates of `x -> x ∪ E · x` from `E`, `E · x = x · E` holds, and with it the
    // one identity the invariant form needs.
    final n = holds(relations(), (pairs) {
      final e = relation(pairs);
      final checks = <Term>[];
      final binds = <(String, Term)>[];
      var x = e;
      for (var i = 0; i < relationNodes; i++) {
        final name = fresh('x');
        binds.add((name, x));
        final xv = var_(name);
        final next = union(xv, compose(e, xv));
        final commutes = eq(compose(e, xv), compose(xv, e));
        final fused = eq(row(next, 0), union(row(xv, 0), successors(row(xv, 0), e)));
        checks.add(and(commutes, fused));
        x = next;
      }
      final all = checks.reduce(and);
      final term = binds.reversed.fold(all, (body, b) => let_(b.$1, b.$2, body));
      return (term, lit(true));
    });
    expect(n, 512 + 256);
  });

  test('law 26: a loop runs on an abstraction of its state', () {
    Term h(Term f) => tuple([nth(f, 0), nth(f, 1)]);
    final byMonth = func(1, (x) => lt(nth(x[0], 0), lit(4)));
    final n = holds(seeds(), (c) => (map(loan(c.$1, c.$2, byMonth), h), abstractLoan(c.$1)));
    expect(n, 20);
    // A guard on the audit counter, which `h` drops, agrees with the month guard only when
    // the counter starts at 1.
    final byAudit = func(1, (x) => lt(nth(x[0], 2), lit(16)));
    final ((_, y0), _, _) = refuted(
      seeds(),
      (c) => (map(loan(c.$1, c.$2, byAudit), h), abstractLoan(c.$1)),
    );
    expect(y0, 2);
  });

  test('law 27: reading back and writing back', () {
    bool ok((Record, UpdatePath) c) => present(c.$1, c.$2);
    (Term, Term) back((Record, UpdatePath) c) {
      final (r, p) = c;
      final a = written(p, 7);
      return (read(update(record(r), steps(p), a), steps(p)), a);
    }

    expect(holds(withPaths().where(ok), back), greaterThan(300));
    (Term, Term) writeBack((Record, UpdatePath) c) {
      final (r, p) = c;
      final v = record(r);
      return (update(v, steps(p), read(v, steps(p))), v);
    }

    holds(withPaths().where(ok), writeBack);
    (Term, Term) overwrite((Record, UpdatePath) c) {
      final (r, p) = c;
      final v = record(r);
      return (
        update(update(v, steps(p), written(p, 7)), steps(p), written(p, 9)),
        update(v, steps(p), written(p, 9)),
      );
    }

    // Overwriting holds on absent keys too, where both sides are `#missing`.
    expect(holds(withPaths(), overwrite), 81 * 8);
    // An absent key gives `#missing` there, so neither reading back nor writing back holds.
    final (_, a, _) = refuted(withPaths(), back);
    expect(a, const Atom('missing'));
    final ((r, p), _, _) = refuted(withPaths(), writeBack);
    expect(present(r, p), isFalse);
  });

  test('law 27: reading elsewhere and commuting updates', () {
    (Term, Term) elsewhere((Record, UpdatePath, UpdatePath) c) {
      final (r, p, q) = c;
      final v = record(r);
      return (read(update(v, steps(p), written(p, 7)), steps(q)), read(v, steps(q)));
    }

    bool apart((Record, UpdatePath, UpdatePath) c) =>
        present(c.$1, c.$2) && present(c.$1, c.$3) && !prefixRelated(c.$2, c.$3);
    final n = holds(withPathPairs().where(apart), elsewhere);
    expect(n, greaterThan(500));
    (Term, Term) commute((Record, UpdatePath, UpdatePath) c) {
      final (r, p, q) = c;
      final v = record(r);
      final (a, b) = (written(p, 7), written(q, 9));
      return (
        update(update(v, steps(p), a), steps(q), b),
        update(update(v, steps(q), b), steps(p), a),
      );
    }

    expect(holds(withPathPairs().where(apart), commute), n);
    // Paths that are equal or prefix-related once their keys are evaluated overwrite one
    // another, the outer the inner.
    bool related((Record, UpdatePath, UpdatePath) c) =>
        present(c.$1, c.$2) && present(c.$1, c.$3) && prefixRelated(c.$2, c.$3);
    final ((_, p, q), _, _) = refuted(withPathPairs().where(related), commute);
    expect(prefixRelated(p, q), isTrue);
  });

  test('law 28: a fold in sequence reads either direction with its operator flipped', () {
    // A bank balance from a ledger written newest first.
    final minus = pf(Prim.sub);
    final ledgers = shortlex(const [-2, -1, 0, 1, 2], 4);
    final n = holds(ledgers, (xs) {
      return (foldl(rev(seq(xs)), lit(100), minus), foldr(seq(xs), flip(minus), lit(100)));
    });
    expect(n, 781);
    holds(ledgers, (xs) {
      return (foldr(rev(seq(xs)), minus, lit(0)), foldl(seq(xs), lit(0), flip(minus)));
    });
    // `fold` with an associative operator that does not commute: the earliest entry of the
    // reversed ledger is the latest of the ledger.
    holds(ledgers, (xs) => (fold(rev(seq(xs)), first()), fold(seq(xs), flip(first()))));
    // A tree fold runs on the mirror image of its tree in the other direction, which only
    // associativity makes equal: `-` is not associative.
    final (xs, _, _) = refuted(
      ledgers,
      (xs) => (fold(rev(seq(xs)), minus), fold(seq(xs), flip(minus))),
    );
    expect(xs.length, greaterThanOrEqualTo(3));
  });

  test('law 28: a float canonical-tree fold is not moved', () {
    // A float `+` given as a function, not the primitive, folds on the canonical tree, whose
    // mirror rounds differently.
    final floatAdd = func(2, (x) => add(x[0], x[1]));
    final (xs, _, _) = refuted(shortlex(bmcFloatValues(), 3), (xs) {
      return (fold(rev(seq(xs)), floatAdd), fold(seq(xs), flip(floatAdd)));
    });
    expect(xs.length, 3);
  });
}
