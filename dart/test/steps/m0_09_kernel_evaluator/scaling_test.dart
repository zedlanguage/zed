/// The evaluator's values at the rule of low complexity (DESIGN.md Part G). A family is
/// shared, not copied, when a variable, a literal or a lookup yields it, so reading a family
/// of `n` entries once per entry costs `O(n log n)`, not `O(n²)`. A union shares the larger
/// family's entries, so a `foldl` that adds one entry per step costs `O(n log n)` too. The
/// names in scope sit in a persistent map, so a name read past `n` later bindings costs
/// `O(log n)`, not `O(n)`.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/instances.dart';
import '../../support/kernel.dart';
import '../../support/scaling.dart' as scaling;

/// The keys `0..n`, each mapped to itself.
Family keys(int n) => Family.set([for (var i = 0; i < n; i++) Int(i)]);

Value run(Term t) => Evaluator(World()).run(t);

/// `fam(F, k -> F[k])`, reading the family `F` once per key: through a literal, or through a
/// variable bound to it, or through a family nested in a tuple.
Term reads(int n, int how) {
  final f = lit(keys(n));
  switch (how) {
    case 0:
      return famWith(f, (k) => get(f, k));
    case 1:
      return app(lam(['f'], famWith(var_('f'), (k) => get(var_('f'), k))), [f]);
    default:
      final t = prim(Prim.tuple, [f, lit(1)]);
      return app(lam(['t'], famWith(nth(var_('t'), 0), (k) => get(nth(var_('t'), 0), k))), [t]);
  }
}

/// `xs.foldl({}, (acc, x) -> acc ∪ {x -> x})` over the keys `0..n`.
Term accumulate(int n) {
  final one = reindex(lit(keys(1)), lam(['p', 'w'], path([var_('x')])), lam(['p', 'w'], var_('x')));
  final op = lam(['acc', 'x'], prim(Prim.union, [var_('acc'), one]));
  return foldl(lit(keys(n)), lit(const Family.empty()), op);
}

/// The union as the leaves of `a` and then those of `b`, a leaf of `b` that `a` already has
/// at its keypath left out: the definition the persistent union must agree with.
Family unionByLeaves(Family a, Family b) {
  final leaves = a.leaves();
  for (final (path, v) in b.leaves()) {
    if (!leaves.any((l) => Path(l.$1) == Path(path) && l.$2 == v)) leaves.add((path, v));
  }
  return Family.fromLeaves(leaves);
}

/// The family, or the error building it throws.
Object attempt(Family Function() build) {
  try {
    return build();
  } on KernelError catch (e) {
    return e;
  }
}

/// A random family of up to three levels over the keys `0..3` and the leaves `0..2`, so that
/// two of them often share keypaths, sometimes with the same leaf.
Family randomFamily(Rng rng, int depth) {
  final leaves = <(Keypath, Value)>[
    for (var i = rng.below(4); i > 0; i--)
      (() {
        final len = 1 + rng.below(depth);
        final Keypath path = [for (var j = 0; j < len; j++) Int(rng.int_(0, 2))];
        return (path, Int(rng.int_(0, 1)) as Value);
      })(),
  ];
  for (var n = leaves.length; n >= 0; n--) {
    if (attempt(() => Family.fromLeaves(leaves.sublist(0, n))) case Family f) return f;
  }
  throw StateError('no leaves build the empty family');
}

/// `let x0 = 0 in let x1 = x0 + 1 in … let x(n) = x0 + n in x0 + x(n)`: each `let` reads the
/// first name past all the names bound after it.
Term lets(int n) {
  var body = add(var_('x0'), var_('x$n'));
  for (var i = n; i >= 1; i--) {
    body = Let('x$i', add(var_('x0'), lit(i)), body);
  }
  return Let('x0', lit(0), body);
}

/// `discard(F, (p, w) -> true)`, keeping every entry of `F`.
Term keepAll(Family f) => discard(lit(f), lam(['p', 'w'], lit(true)));

void main() {
  test('reading a family once per entry scales', () {
    for (final (how, what) in [(0, 'a literal'), (1, 'a variable'), (2, 'a tuple')]) {
      scaling.check('reading $what once per entry, by entries', 2000, (n) => run(reads(n, how)));
    }
  });

  test('each read yields the family', () {
    for (var how = 0; how < 3; how++) {
      expect(run(reads(100, how)), keys(100), reason: 'read $how');
    }
  });

  test('a union adding one entry per step scales', () {
    // Each union rebuilt both families from their leaves, and the family of the `n`
    // accumulators was built from all `n²/2` of their leaves.
    scaling.check('a foldl of unions, by steps', 1000, (n) => run(accumulate(n)));
    expect(run(accumulate(50)), keys(50));
  });

  test('the union agrees with the union of the leaves', () {
    final rng = Rng(17);
    var collisions = 0, overlaps = 0;
    for (var i = 0; i < 20000; i++) {
      final a = randomFamily(rng, 3), b = randomFamily(rng, 3);
      final want = attempt(() => unionByLeaves(a, b));
      expect(attempt(() => a.union(b)), want, reason: '$a ∪ $b');
      if (want is KernelError) collisions++;
      if (want is Family && a.keys.any((k) => b[k] != null)) overlaps++;
    }
    expect(
      collisions > 2000 && overlaps > 2000,
      isTrue,
      reason: '$collisions collisions, $overlaps overlaps',
    );
  });

  test('families are ordered by their entries', () {
    // A family of families is ordered by its keys, so the order of two families must stay
    // the order of their entries in key order.
    final rng = Rng(5);
    final both = [0, 0, 0];
    int entries(Family a, Family b) {
      final x = a.entries.toList(), y = b.entries.toList();
      for (var i = 0; i < x.length && i < y.length; i++) {
        final c = x[i].$1.compareTo(y[i].$1);
        if (c != 0) return c.sign;
        final d = x[i].$2.compareTo(y[i].$2);
        if (d != 0) return d.sign;
      }
      return x.length.compareTo(y.length);
    }

    for (var i = 0; i < 20000; i++) {
      final a = randomFamily(rng, 2), b = randomFamily(rng, 2);
      final want = entries(a, b);
      expect(a.compareTo(b).sign, want, reason: '$a against $b');
      both[want + 1]++;
    }
    expect(both.every((n) => n > 1000), isTrue, reason: '$both');
  });

  test('a family built with families as leaves agrees with its leaves', () {
    // A family given as a leaf is kept whole where nothing else is written beneath its
    // keypath; the result, and the first collision, are those of its leaves given one by one.
    final rng = Rng(29);
    var built = 0, collisions = 0;
    for (var i = 0; i < 20000; i++) {
      final parts = <(Keypath, Value)>[
        for (var j = 1 + rng.below(3); j > 0; j--)
          (() {
            final Keypath path = [for (var k = 1 + rng.below(2); k > 0; k--) Int(rng.int_(0, 2))];
            final Value v = rng.below(3) == 0 ? Int(rng.int_(0, 1)) : randomFamily(rng, 2);
            return (path, v);
          })(),
      ];
      final flat = [
        for (final (p, v) in parts)
          if (v is Family)
            for (final (q, w) in v.leaves()) ([...p, ...q], w)
          else
            (p, v),
      ];
      final want = attempt(() => Family.fromLeaves(flat));
      expect(attempt(() => Family.fromLeaves(parts)), want, reason: '$parts');
      if (want is Family) built++;
      if (want is KernelError) collisions++;
    }
    expect(
      built > 2000 && collisions > 2000,
      isTrue,
      reason: '$built built, $collisions collisions',
    );
  });

  test('a name read past many bindings scales', () {
    // Each lookup walked the frames from the innermost binding out: a chain of `n` lets cost
    // `n²/2` comparisons of names.
    scaling.check('a chain of lets reading the first name, by lets', 2000, (n) {
      expect(run(lets(n)), Int(n));
    });
  });

  test('an inner binding hides an outer one within its scope only', () {
    // `let x = 1 in (let x = 2 in x) * 10 + x` is 21.
    final scoped = let_('x', lit(1), add(mul(let_('x', lit(2), var_('x')), lit(10)), var_('x')));
    expect(run(scoped), const Int(21));
    // `let x = 1 in let f = y -> x + y in let x = 10 in f(0) * 100 + x` is 110: the closure
    // keeps the `x` it captured.
    final captured = let_(
      'x',
      lit(1),
      let_(
        'f',
        lam(['y'], add(var_('x'), var_('y'))),
        let_('x', lit(10), add(mul(app(var_('f'), [lit(0)]), lit(100)), var_('x'))),
      ),
    );
    expect(run(captured), const Int(110));
    // A parameter hides the name it shares: `let x = 1 in (x -> x)(5) + x` is 6.
    final param = let_('x', lit(1), add(app(lam(['x'], var_('x')), [lit(5)]), var_('x')));
    expect(run(param), const Int(6));
  });

  test('a discard scales with its entries and the keypaths it gives', () {
    // Each level of a discard was rebuilt from the leaves of the levels below it: a family of
    // depth `d` cost `O(L·d²)`. Now a level keeps each kept family whole. A discard gives
    // the selector the keypath of each entry, so a chain of depth `d` with a leaf beside each
    // level gives keypaths of lengths 1 to `d`, `d²` keys in all: work of order `d²`, which
    // it is allowed. Rebuilding each level from its leaves cost `d³/3`.
    Family wide(int n) => Family.fromLeaves([
      for (var i = 0; i < n; i++)
        for (var j = 0; j < 2; j++) ([Int(i), Int(j)], Int(i + j)),
    ]);
    scaling.check('a discard of n pairs, by n', 2000, (n) {
      final f = wide(n);
      expect(run(keepAll(f)), f);
    });
    // The leaf `i` at the keypath of `i` zeros and then a one.
    Family caterpillar(int d) => Family.fromLeaves([
      for (var i = 0; i < d; i++)
        ([for (var j = 0; j < i; j++) const Int(0), const Int(1)], Int(i)),
    ]);
    scaling.checkOrder('a discard of a caterpillar, by depth', 200, 2, (d) {
      final f = caterpillar(d);
      expect(run(keepAll(f)), f);
    });
  });
}
