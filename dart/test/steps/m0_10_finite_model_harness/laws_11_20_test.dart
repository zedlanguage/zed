/// Laws 11–20 of the catalog: dead-structure deletion, distribution and promotion of folds,
/// prefix differences, step powers, semi-naive fixpoints, refinement hoisting, rollup,
/// contraction, and naturality.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/check.dart';
import '../../support/instances.dart';
import '../../support/kernel.dart';
import 'harness.dart';

Term plus() => const PrimFn(Prim.add);

Term empty() => lit(const Family.empty());

/// The maps of `intMaps` that have at least one entry.
List<IntMap> nonemptyMaps(int seed) => [
  for (final m in intMaps(seed))
    if (m.isNotEmpty) m,
];

/// The value `t` computes; fails on an error.
Value value(Term t) => eval(t);

// Law 12: a distributing constant hoists out of a fold.

/// `fold(⊕)(map(v -> c ⊗ v)(m))` and `c ⊗ fold(⊕)(m)`.
(Term, Term) hoisted(IntMap m, int c, Prim sum, Prim times, Term? identity) => (
  fold(map(ints(m), (v) => bin(times, lit(c), v)), pf(sum), identity),
  bin(times, lit(c), fold(ints(m), pf(sum), identity)),
);

// Law 13: a range fold is a prefix difference in a group.

/// A permutation of `0..3` as the tuple of its images.
Value perm(List<int> p) => Tuple([for (final x in p) Int(x)]);

List<Value> s3() => [
  for (final p in const [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
  ])
    perm(p),
];

/// `p ⊕ q`: apply `p`, then `q`, so `(p ⊕ q)[i] = q[p[i]]`.
Term then() => func(2, (x) {
  final (p, q) = (x[0], x[1]);
  return prim(Prim.tuple, [
    for (var i = 0; i < 3; i++) prim(Prim.tupleGet, [q, nth(p, i)]),
  ]);
});

/// The inverse permutation: the `j` with `p[j] == i`, for each `i`.
Term inverse(Term p) => prim(Prim.tuple, [
  for (var i = 0; i < 3; i++)
    if_(eq(nth(p, 0), lit(i)), lit(0), if_(eq(nth(p, 1), lit(i)), lit(1), lit(2))),
]);

/// Each sequence of at most three permutations, with each range `i..=j` in it.
List<(List<Value>, int, int)> ranges() => [
  for (final xs in shortlex(s3(), 3))
    for (var j = 0; j < xs.length; j++)
      for (var i = 0; i <= j; i++) (xs, i, j),
];

/// The range fold, and the prefix difference with the inverse on the left or the right.
(Term, Term) rangeSides(List<Value> xs, int i, int j, bool inverseLeft) {
  final range = fold(
    discardWith(seq(xs), (p, _) => and(le(lit(i), key(p, 0)), le(key(p, 0), lit(j)))),
    then(),
  );
  final prefix = scan(seq(xs), then());
  final before = i == 0 ? lit(perm([0, 1, 2])) : get(prefix, lit(i - 1));
  final upto = get(prefix, lit(j));
  final diff = inverseLeft
      ? app(then(), [inverse(before), upto])
      : app(then(), [upto, inverse(before)]);
  return (range, diff);
}

// Law 14: a counted run of a step is the step's power, by repeated squaring.

/// The affine map `x -> a * x + b` as the tuple `(a, b)`, and its composition: `(f ; g)`
/// applies `f` first.
Term affineThen(Term f, Term g) {
  // g(f(x)) = ga * (fa * x + fb) + gb
  return prim(Prim.tuple, [mul(nth(g, 0), nth(f, 0)), add(mul(nth(g, 0), nth(f, 1)), nth(g, 1))]);
}

/// `step^n` by repeated squaring, built for the static `n`.
Term power(Term step, int n) {
  Term acc = lit(const Tuple([Int(1), Int(0)]));
  var square = step;
  for (var k = n; k > 0; k >>= 1) {
    if (k & 1 == 1) acc = affineThen(acc, square);
    square = affineThen(square, square);
  }
  return acc;
}

/// The loop `gen` from `(0, x0)`, stepping `(t, x) -> (t + 1, next(t, x))` while `t < n`, and
/// the state at generation `n`.
Term counted(int x0, int n, Term Function(Term, Term) next) {
  final step = func(1, (x) {
    final f = x[0];
    return prim(Prim.tuple, [add(nth(f, 0), lit(1)), next(nth(f, 0), nth(f, 1))]);
  });
  final frames = Gen(
    lit(Tuple([const Int(0), Int(x0)])),
    step,
    func(1, (x) => lt(nth(x[0], 0), lit(n))),
    GuardPos.before,
  );
  return nth(get(frames, lit(n)), 1);
}

List<(int, int, int, int)> affineCases() => [
  for (var a = -2; a <= 2; a++)
    for (var b = -2; b <= 2; b++)
      for (var x0 = -2; x0 <= 2; x0++)
        for (var n = 0; n <= 10; n++) (a, b, x0, n),
];

// Law 15: fix runs semi-naive.

/// `a` less the pairs of `b`.
Term minus(Term a, Term b) => discardWith(a, (p, _) {
  return not(and(eq(prim(Prim.pathLen, [p]), lit(2)), found(get(get(b, key(p, 0)), key(p, 1)))));
});

/// The relation the frontier loop reaches: frames `(old, delta)` from `({}, e)`, each round's
/// candidates `cand(delta, old, old ∪ delta)` less what is known, until the delta is empty.
Term semiNaive(Term e, Term Function(Term delta, Term old, Term new_) cand) {
  final step = func(1, (x) {
    final (old, delta) = (nth(x[0], 0), nth(x[0], 1));
    final new_ = union(old, delta);
    final freshPairs = minus(cand(delta, old, new_), new_);
    return prim(Prim.tuple, [new_, freshPairs]);
  });
  final frames = Gen(
    prim(Prim.tuple, [empty(), e]),
    step,
    func(1, (x) => lt(lit(0), count(nth(x[0], 1)))),
    GuardPos.before,
  );
  final g = fresh('g');
  final last = get(var_(g), sub(count(var_(g)), lit(1)));
  return let_(g, frames, union(nth(last, 0), nth(last, 1)));
}

// Law 16: a refinement hoists backward through an operation.

/// The values a refinement is tried on: the rung 6 integers and a failure atom.
List<Term> refineInputs() => [for (final i in bmcInts()) lit(i), atom('badRecord')];

/// `op(x).refine(p)` and `x.refine(p ∘ op)`.
(Term, Term) hoist(Term Function(Term) op, Term p, Term x) {
  final composed = func(1, (y) => app(p, [op(y[0])]));
  return (refine(op(x), p), op(refine(x, composed)));
}

// Law 17: fold promotion.

/// `h(fold(⊕)(m))` and `fold(⊗)(map(h)(m))`.
(Term, Term) promoted(
  Term m,
  Term Function(Term) h,
  Prim sum,
  Term? sumId,
  Prim times,
  Term? timesId,
) => (h(fold(m, pf(sum), sumId)), fold(map(m, h), pf(times), timesId));

// Law 18: rollup.

/// Reduce-by-key along the key map `f`: entry `k -> v` goes to class `f(k)`.
Term rollupBy(Term m, Term Function(Term) f, Term op) {
  final kf = func(2, (x) => path([f(key(x[0], 0)), key(x[0], 0)]));
  return foldAt(reindex(m, kf, func(2, (x) => x[1])), 2, op);
}

/// The aggregate along `g ∘ f`, and the one along `g` of the aggregate along `f`.
(Term, Term) rolled(IntMap m, Term Function(Term) f, Term Function(Term) g, Term op) =>
    (rollupBy(ints(m), (k) => g(f(k)), op), rollupBy(rollupBy(ints(m), f, op), g, op));

// Law 19: contraction is associative.

const d = 2;

Term dims() => lit(Family.set([for (var i = 0; i < d; i++) Int(i)]));

typedef Matrix = List<(int, int, Value)>;

/// A `D × D` matrix with some cells absent, as `i -> j -> v`.
Term matrix(Matrix cells) => lit(
  Family.fromLeaves([
    for (final (i, j, v) in cells) ([Int(i), Int(j)], v),
  ]),
);

Term present(Term m, Term i, Term j) => found(get(get(m, i), j));

/// `(a · b)[i][k]`: the `⊕`-fold over `j` of `a[i][j] ⊗ b[j][k]`, over the `j` where both
/// cells are present.
Term contract(Term a, Term b, Term sum, Term times) {
  final joined = famWith(dims(), (i) {
    return famWith(dims(), (k) {
      final shared = discardWith(dims(), (p, _) {
        return and(present(a, i, key(p, 0)), present(b, key(p, 0), k));
      });
      return famWith(shared, (j) => app(times, [get(get(a, i), j), get(get(b, j), k)]));
    });
  });
  return foldAt(joined, 3, sum);
}

/// Random triples of matrices over `values`, each cell absent with probability 1/4.
List<(Matrix, Matrix, Matrix)> triples(int seed, List<Value> values) {
  final rng = Rng(seed);
  Matrix one() => [
    for (var i = 0; i < d; i++)
      for (var j = 0; j < d; j++)
        if (rng.below(4) != 0) (i, j, rng.pick(values)),
  ];
  return [for (var n = 0; n < 512; n++) (one(), one(), one())];
}

(Term, Term) chainSides((Matrix, Matrix, Matrix) t, Term sum, Term times) {
  final (a, b, c) = (matrix(t.$1), matrix(t.$2), matrix(t.$3));
  return (
    contract(contract(a, b, sum, times), c, sum, times),
    contract(a, contract(b, c, sum, times), sum, times),
  );
}

/// `false` on the atom `#name`, `true` on anything else.
Term notAtomNamed(Term e, String name) =>
    Match(e, [(AtomP(name), lit(false)), (const WildP(), lit(true))]);

/// Whether some `q` in `0..D` has `pred(q)`.
Term some(Term Function(Term) pred) =>
    lt(lit(0), count(discardWith(dims(), (p, _) => pred(key(p, 0)))));

List<Value> smallInts() => [for (var i = -3; i <= 3; i++) Int(i)];

void main() {
  // Law 11: unconsumed structure deletes.

  test('law 11: a binding no demand reaches deletes', () {
    // A report that computes a sorted copy, a per-class total and a ratio, then returns only
    // the grand total: the three dead bindings delete.
    Term total(IntMap m) => fold(ints(m), plus(), lit(0));
    final dead = <Term Function(IntMap)>[
      (m) => rankWiden(ints(m), (v) => v, lt),
      (m) => foldAt(groupBy(ints(m), (v) => modulo(v, lit(3))), 2, plus()),
      (m) => map(ints(m), (v) => idiv(lit(12), v)),
    ];
    for (final dd in dead) {
      final n = holds(intMaps(13), (m) => (let_(fresh('unused'), dd(m), total(m)), total(m)));
      expect(n, greaterThanOrEqualTo(1800));
    }
    // A dead binding past the 64-bit range is an unread number: `int` is unbounded
    // (reference semantics (b); widened by step L1.17).
    final big = let_('unused', mul(lit(0x7fffffffffffffff), lit(2)), lit(1));
    expect(value(big), const Int(1));
  });

  test('law 11: a push is demanded even when its acknowledgment is not', () {
    // The demand roots include the ports: deleting an unread push to `log` loses the line.
    (Object, List<Value>) run(Term t) {
      final ev = Evaluator(World().output('log'));
      Object out;
      try {
        out = ev.run(t);
      } on KernelError catch (e) {
        out = e;
      }
      return (out, List.of(ev.world.log('log')));
    }

    final withPush = let_('ack', Push('log', lit(s('checkpoint'))), lit(1));
    final deleted = lit(1);
    final (a, b) = (run(withPush), run(deleted));
    expect(a.$1, b.$1);
    expect(a.$2, [s('checkpoint')]);
    expect(b.$2, isEmpty);
  });

  test('law 12: a constant factor leaves the sum', () {
    // Prices in cents times a quantity of 3: the total of the line items is 3 times the total.
    // `*` distributes over `+`, and 0 absorbs, so the empty order is covered too.
    for (final c in [-2, 0, 3]) {
      final n = holds(intMaps(14), (m) => hoisted(m, c, Prim.add, Prim.mul, lit(0)));
      expect(n, greaterThanOrEqualTo(1800));
    }
  });

  test('law 12: on a possibly empty level the identity must absorb', () {
    // `+` distributes over `max`, but the identity of `max`, here -100, does not absorb under
    // `+`: on an empty level the hoisted side adds the constant to it.
    final n = holds(nonemptyMaps(15), (m) => hoisted(m, 5, Prim.max, Prim.add, lit(-100)));
    expect(n, greaterThanOrEqualTo(1800));
    final (m, a, b) = refuted(intMaps(15), (m) => hoisted(m, 5, Prim.max, Prim.add, lit(-100)));
    expect(m, isEmpty);
    expect((a, b), (const Int(-100), const Int(-95)));
  });

  test('law 12: a factor that does not distribute stays inside', () {
    // `max` does not distribute over `+`: `max(c, a + b) != max(c, a) + max(c, b)`. The
    // instances are nonempty, so the refutation is not the identity's.
    final (m, _, _) = refuted(nonemptyMaps(16), (m) => hoisted(m, 1, Prim.add, Prim.max, lit(0)));
    expect(m.length, greaterThanOrEqualTo(2));
  });

  test('law 13: a range of a group fold is a prefix difference', () {
    // Composing the shuffles applied to a deck between two steps of a log, from the running
    // compositions: the permutations of three cards are a group that is not abelian.
    final n = holds(ranges(), (r) => rangeSides(r.$1, r.$2, r.$3, true));
    expect(n, 6 + 36 * 3 + 216 * 6);
    // The other orientation, the inverse on the right, holds only on abelian carriers.
    final ((xs, i, _), _, _) = refuted(ranges(), (r) => rangeSides(r.$1, r.$2, r.$3, false));
    expect(i > 0 && xs.length >= 2, isTrue);
  });

  test('law 14: a counted affine loop is one power of its step', () {
    // Compound interest with a fee, `x -> a * x + b`, run for n periods.
    final n = holds(affineCases(), (c) {
      final (a, b, x0, n) = c;
      final p = power(lit(Tuple([Int(a), Int(b)])), n);
      return (
        counted(x0, n, (_, x) => add(mul(lit(a), x), lit(b))),
        add(mul(nth(p, 0), lit(x0)), nth(p, 1)),
      );
    });
    expect(n, 5 * 5 * 5 * 11);
    // A step that reads the step index, `x -> x + t`, applies a different action each step, so
    // no single action has a power: the power of its first action, the identity, misses every
    // later one.
    final (_, a, b) = refuted(affineCases(), (c) {
      final (_, _, x0, n) = c;
      final p = power(lit(const Tuple([Int(1), Int(0)])), n);
      return (counted(x0, n, add), add(mul(nth(p, 0), lit(x0)), nth(p, 1)));
    });
    expect(a, isNot(b));
  });

  test('law 15: a linear step runs on the frontier', () {
    // Every station reachable along a rail network: `r -> r · e` is linear over union.
    final n = holds(relations(), (pairs) {
      final e = relation(pairs);
      return (
        fixLattice(e, func(1, (r) => compose(r[0], e)), pf(Prim.union)),
        semiNaive(e, (delta, _, _) => compose(delta, e)),
      );
    });
    expect(n, 512 + 256);
  });

  test('law 15: a quadratic step reads the old and new values around the delta', () {
    // Transitive closure by path doubling, `r -> r · r`: semi-naive in a distributive dioid
    // steps by `Δ · r_old ⊔ r_new · Δ`.
    Term lattice(List<(int, int)> pairs) =>
        fixLattice(relation(pairs), func(1, (r) => compose(r[0], r[0])), pf(Prim.union));
    final n = holds(relations(), (pairs) {
      return (
        lattice(pairs),
        semiNaive(
          relation(pairs),
          (delta, old, new_) => union(compose(delta, old), compose(new_, delta)),
        ),
      );
    });
    expect(n, 512 + 256);
    // The delta alone, `Δ · Δ`, misses a path whose halves were found in different rounds.
    final (pairs, _, _) = refuted(relations(), (pairs) {
      return (lattice(pairs), semiNaive(relation(pairs), (delta, _, _) => compose(delta, delta)));
    });
    expect(pairs.length, greaterThanOrEqualTo(3));
  });

  test('law 16: a check on the output is a check on the input', () {
    // A dosage check, `0 < v`, on a computed dose, moved to the input it is computed from.
    final positive = func(1, (v) => lt(lit(0), v[0]));
    final ops = <Term Function(Term)>[
      (x) => add(mul(lit(2), x), lit(1)),
      (x) => idiv(lit(12), x),
      (x) => modulo(x, lit(3)),
      (x) => mul(x, x),
      // Along the first argument of `x - y`, with `y` held at 4.
      (x) => sub(x, lit(4)),
    ];
    for (final op in ops) {
      expect(holds(refineInputs(), (x) => hoist(op, positive, x)), 18);
    }
    // A predicate that narrows a failure, here sending `#divByZero` to `false`, sees the
    // failure only on the hoisted side, where it is the input's preimage.
    final narrowing = func(1, (v) {
      return Match(v[0], [
        (const AtomP('divByZero'), lit(false)),
        (const WildP(), lt(lit(0), v[0])),
      ]);
    });
    Term div(Term x) => idiv(lit(12), x);
    final (x, a, b) = refuted(refineInputs(), (x) => hoist(div, narrowing, x));
    expect(value(x), const Int(0));
    expect((a, b), (const Atom('divByZero'), const Atom('invalid')));
  });

  test('law 17: a monotone map moves inside a max', () {
    // The best score after a curve `2v + 1` is the curve of the best score.
    Term curve(Term v) => add(mul(lit(2), v), lit(1));
    final n = holds(intMaps(17), (m) => promoted(ints(m), curve, Prim.max, null, Prim.max, null));
    expect(n, greaterThanOrEqualTo(1800));
    // `v * v` is not monotone on the negative scores.
    Term square(Term v) => mul(v, v);
    final (m, _, _) = refuted(
      intMaps(17),
      (m) => promoted(ints(m), square, Prim.max, null, Prim.max, null),
    );
    expect(m.any((e) => e.$2 < 0), isTrue);
  });

  test('law 17: on an empty level the map must carry identity to identity', () {
    // `v + 1` is monotone, but sends the identity -100 to -99.
    Term next(Term v) => add(v, lit(1));
    (Term, Term) sides(IntMap m) =>
        promoted(ints(m), next, Prim.max, lit(-100), Prim.max, lit(-100));
    expect(holds(nonemptyMaps(18), sides), greaterThanOrEqualTo(1800));
    final (m, a, b) = refuted(intMaps(18), sides);
    expect(m, isEmpty);
    expect((a, b), (const Int(-99), const Int(-100)));
  });

  test('law 17: a float sum premise is the n-ary equation bitwise', () {
    // Negation is a homomorphism of binary `+` up to the sign of zero, and the n-ary equation
    // fails bitwise there: the exact sum of `0.0` and `-0.0` is `+0.0`, and so is the exact
    // sum of their negations.
    Term neg(Term v) => prim(Prim.neg, [v]);
    final floats = shortlex(bmcFloatValues(), 2);
    final (xs, a, b) = refuted(
      floats,
      (xs) => promoted(seq(xs), neg, Prim.add, null, Prim.add, null),
    );
    expect(xs.where((x) => x is Float && x.x == 0.0).length, 2);
    expect((a, b), (Float(-0.0), Float(0.0)));
  });

  test('law 18: a coarse total comes from the fine totals', () {
    // Sales by day `k`, rolled up to weeks `k div 2`, then to the parity of the week.
    Term week(Term k) => idiv(k, lit(2));
    Term parity(Term w) => modulo(w, lit(2));
    expect(holds(intMaps(19), (m) => rolled(m, week, parity, plus())), greaterThanOrEqualTo(1800));
  });

  test('law 18: a fold that does not commute needs a monotone fine map', () {
    // `first`: the earliest sale of each class. With the fine map monotone, the earliest fine
    // class holds the earliest entry; the coarse map is unconstrained.
    final first = func(2, (x) => x[0]);
    Term week(Term k) => idiv(k, lit(2));
    Term third(Term w) => modulo(w, lit(3));
    expect(holds(intMaps(20), (m) => rolled(m, week, third, first)), greaterThanOrEqualTo(1800));
    // A fine map that reverses the order picks the latest entry of each coarse class.
    Term reversed(Term k) => sub(lit(0), k);
    Term parity(Term w) => modulo(w, lit(2));
    final (m, _, _) = refuted(intMaps(20), (m) => rolled(m, reversed, parity, first));
    expect(m.length, greaterThanOrEqualTo(2));
  });

  test('law 19: a chain of contractions reorders in every semiring', () {
    final ints = smallInts();
    const bools = [Bool(false), Bool(true)];
    final semirings = [
      (pf(Prim.add), pf(Prim.mul), ints), // counting
      (pf(Prim.min), pf(Prim.add), ints), // shortest paths
      (pf(Prim.max), pf(Prim.min), ints), // widest paths
      (pf(Prim.or), pf(Prim.and), bools), // reachability
    ];
    for (var k = 0; k < semirings.length; k++) {
      final (sum, times, values) = semirings[k];
      expect(holds(triples(19 + k, values), (t) => chainSides(t, sum, times)), 512);
    }
  });

  test('law 19: contraction needs distribution and a commutative sum', () {
    final ints = smallInts();
    // `max` does not distribute over `+`.
    refuted(triples(23, ints), (t) => chainSides(t, pf(Prim.add), pf(Prim.max)));
    // `first` is associative and `*` distributes over it, but it does not commute: the two
    // orders take the first `k` of the first `j` and the first `j` of the first `k`.
    final first = func(2, (x) => x[0]);
    refuted(triples(24, ints), (t) => chainSides(t, first, pf(Prim.mul)));
  });

  test('law 19: a star join folds each arm before the join', () {
    // Orders `a[i][j]` of customer i for product j, with the product's prices `b[j][k]` and
    // discounts `c[j][l]` per variant: the sum over all triples is the sum over `j` of the
    // order times the arms' totals. A product with no prices or no discounts drops out.
    final n = holds(triples(25, smallInts()), (t) {
      final (a, b, c) = (matrix(t.$1), matrix(t.$2), matrix(t.$3));
      Term cell(Term i, Term j, Term k, Term l) => if_(
        and(and(present(a, i, j), present(b, j, k)), present(c, j, l)),
        mul(mul(get(get(a, i), j), get(get(b, j), k)), get(get(c, j), l)),
        atom('drop'),
      );
      final all = famWith(dims(), (i) {
        return famWith(dims(), (j) {
          return famWith(dims(), (k) {
            return discardWith(
              famWith(dims(), (l) => cell(i, j, k, l)),
              (_, e) => notAtomNamed(e, 'drop'),
            );
          });
        });
      });
      final lhs = foldAt(foldAt(foldAt(all, 4, plus()), 3, plus()), 2, plus());
      final rhs = famWith(dims(), (i) {
        final js = discardWith(dims(), (p, _) {
          final j = key(p, 0);
          return and(
            present(a, i, j),
            and(some((q) => present(b, j, q)), some((q) => present(c, j, q))),
          );
        });
        return fold(
          famWith(js, (j) {
            return mul(mul(get(get(a, i), j), fold(get(b, j), plus())), fold(get(c, j), plus()));
          }),
          plus(),
        );
      });
      return (lhs, discardWith(rhs, (_, e) => notAtomNamed(e, 'empty')));
    });
    expect(n, 512);
  });

  test('law 20: a map moves past a function that ignores values', () {
    Term g(Term v) => mul(v, v);
    // `first`: the entry with the least key.
    final first = func(2, (x) => x[0]);
    final n = holds(intMaps(26), (m) => (g(fold(ints(m), first)), fold(map(ints(m), g), first)));
    expect(n, greaterThanOrEqualTo(1800));
    // A key restriction: the readings before the cutoff.
    Term early(Term f) => discardWith(f, (p, _) => lt(key(p, 0), lit(2)));
    holds(intMaps(26), (m) => (map(early(ints(m)), g), early(map(ints(m), g))));
  });

  test('law 20: past an equality test the map must preserve and reflect it', () {
    // The number of distinct readings, an `int`, which the map leaves alone.
    Term distinct(Term f) => count(keyset(groupBy(f, (v) => v)));
    Term injective(Term v) => add(mul(lit(2), v), lit(1));
    holds(intMaps(27), (m) => (distinct(map(ints(m), injective)), distinct(ints(m))));
    // `v * v` merges `-1` and `1`.
    Term square(Term v) => mul(v, v);
    final (m, _, _) = refuted(
      intMaps(27),
      (m) => (distinct(map(ints(m), square)), distinct(ints(m))),
    );
    final vs = [for (final e in m) e.$2];
    expect(vs.any((v) => vs.contains(-v) && v != 0), isTrue);
  });

  test('law 20: past an order the map must preserve and reflect it', () {
    // Ranking scores, then rescaling them, against rescaling first.
    (Term, Term) sides(IntMap m, Term Function(Term) g) =>
        (rankWiden(map(ints(m), g), (v) => v, lt), map(rankWiden(ints(m), (v) => v, lt), g));
    Term rescale(Term v) => add(mul(lit(2), v), lit(1));
    expect(holds(intMaps(28), (m) => sides(m, rescale)), greaterThanOrEqualTo(1800));
    // `v div 2` is monotone but merges `2` and `3` into one tie, so their ranks merge.
    Term halve(Term v) => idiv(v, lit(2));
    final (m, _, _) = refuted(intMaps(28), (m) => sides(m, halve));
    expect(m.length, greaterThanOrEqualTo(2));
  });
}
