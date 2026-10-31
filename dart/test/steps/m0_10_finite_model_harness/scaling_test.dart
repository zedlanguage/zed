/// The definedness `fix` at the rule of low complexity (DESIGN.md Part G). Each attempt at an
/// entry reads the family defined so far; copying the domain and that family into every
/// attempt made a `fix` over `D` keys cost `O(D²)` even when each entry is tried at most twice.
/// An entry postponed on an undefined key waits on it, so a chain, such as the accumulators of
/// a `foldl`, costs `D` attempts under every schedule rather than `D²/2` in rounds.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/kernel.dart';
import '../../support/scaling.dart' as scaling;

/// The keys `from..to`, as a set.
Term keys(int from, int to) => lit(Family.set([for (var k = from; k < to; k++) Int(k)]));

/// The family `k -> k` over `0..d`, each entry above 0 reading entry 0 (`star`) or the entry
/// before it (`chain`).
Term counts(int d, bool chain) => fixDefined(keys(0, d), (self, k) {
  final from = chain ? sub(k, lit(1)) : lit(0);
  final step = chain ? lit(1) : k;
  return if_(eq(k, lit(0)), lit(0), add(get(self, from), step));
});

Value run(Term t, Schedule schedule) => Evaluator(World(), schedule: schedule).run(t);

/// The family over `0..d` whose entry 0 sums the entries `1..d`, each `k` itself.
Term fanIn(int d) => fixDefined(keys(0, d), (self, k) {
  final sum = fold(famWith(keys(1, d), (j) => get(self, j)), const PrimFn(Prim.add), lit(0));
  return if_(eq(k, lit(0)), sum, k);
});

/// The family over `0..2d` whose entry `k < d` reads the leaf `d + k`, then the entry
/// after it: `f[k] = f[d + k] + f[k + 1]`, with `f[d - 1] = f[2d - 1]` and `f[d + k] = k`.
Term reverseChain(int d) => fixDefined(keys(0, 2 * d), (self, k) {
  final leaf = get(self, add(k, lit(d)));
  final next = get(self, add(k, lit(1)));
  return if_(lt(k, lit(d - 1)), add(leaf, next), if_(lt(k, lit(d)), leaf, sub(k, lit(d))));
});

/// `Σ_{j=k}^{d-1} j`, the entry `k < d` of [reverseChain].
int tailSum(int d, int k) => (k + d - 1) * (d - k) ~/ 2;

/// The ascent from `{}` whose step is the key `count(x)` alone, joined to `x`, until `x`
/// has `n` keys.
Term ascent(int n) {
  final step = func(1, (x) {
    final c = count(x[0]);
    final one = reindex(
      lit(Family.set([const Int(0)])),
      func(2, (_) => c),
      func(2, (_) => lit(true)),
    );
    return if_(lt(c, lit(n)), one, lit(const Family.empty()));
  });
  return fixLattice(lit(const Family.empty()), step, const PrimFn(Prim.union));
}

/// `"ab…"`, the `n` letters of the sequence `0..n -> letter` joined by a `foldl` of `++`.
Term joined(int n) {
  final letters = Family.of([
    for (var i = 0; i < n; i++) (Int(i), s(const ['a', 'b', 'c'][i % 3])),
  ]);
  return foldl(lit(letters), lit(s('')), const PrimFn(Prim.concat));
}

void main() {
  test('the definedness fix scales', () {
    // Two rounds: every entry but 0 is postponed once.
    scaling.check('rounds, entries reading entry 0, by keys', 1000, (d) {
      run(counts(d, false), const Rounds());
    });
    scaling.check('chaotic, entries reading entry 0, by keys', 1000, (d) {
      run(counts(d, false), Chaotic(7));
    });
    // Each entry waits on, or demands, the one before it.
    for (final (name, schedule) in [
      ('Rounds', const Rounds()),
      ('Chaotic(7)', Chaotic(7)),
      ('Pull', const Pull()),
    ]) {
      scaling.check('$name, a chain, by keys', 1000, (d) => run(counts(d, true), schedule));
    }
  });

  test('every schedule defines the counts', () {
    final want = Family.of([for (var k = 0; k < 50; k++) (Int(k), Int(k))]);
    for (final chain in [false, true]) {
      for (final schedule in [const Rounds(), const Pull(), Chaotic(3)]) {
        expect(run(counts(50, chain), schedule), want, reason: '$schedule, chain $chain');
      }
    }
  });

  test('a Jacobi round reads the family as the round began', () {
    // Each round is one unit of fuel. A chain of 40 entries defines one entry per round, so
    // it takes 40 rounds and a 41st that finds nothing left; a round that read the entries
    // defined earlier in the same round would define the whole chain in one.
    final chain = counts(40, true);
    Value withFuel(int fuel) => Evaluator(World(), fuel: fuel).run(chain);
    expect(() => withFuel(40), throwsA(isA<KernelError>()));
    withFuel(41);
  });

  test('an entry reading many undefined entries scales under demand', () {
    // Each read of an undefined entry stopped the attempt, and the entry was tried again from
    // the start once the entry read was defined: entry 0 of `fanIn(d)` was tried `d` times
    // and read `d²/2` entries. Now the entry read is evaluated where it is read.
    scaling.check('pull, one entry reading every other, by keys', 1000, (d) {
      final v = run(fanIn(d), const Pull());
      expect(v.asFamily![const Int(0)], Int(d * (d - 1) ~/ 2));
    });
    scaling.check('pull, entries reading the ones after them, by keys', 1000, (d) {
      final v = run(reverseChain(d), const Pull());
      expect(v.asFamily![const Int(0)], Int(tailSum(d, 0)));
    });
  });

  test('a demanded entry has the value it has in rounds', () {
    // A chain longer than the depth of nested demands falls back to the stack of demands.
    // (Its facts are compared with those of rounds once provenance is ported, step L1.20.)
    for (final d in [5, 40, maxDepth + 500]) {
      final t = reverseChain(d);
      final v = run(t, const Pull());
      expect(run(t, const Rounds()), v, reason: 'd = $d');
      final f = v.asFamily!;
      for (final k in [0, d ~/ 2, d - 1]) {
        expect(f[Int(k)], Int(tailSum(d, k)), reason: 'd = $d, k = $k');
      }
    }
  });

  test('a lattice ascent by one key a round scales', () {
    // The test for the fixpoint compared the iterate with the one before in the total order
    // of values, reading both in full each round: `n` rounds took `O(n²)` steps. Families
    // are equal by their maps, which differ at once in size.
    scaling.check('a lattice ascent adding a key a round, by keys', 1000, (n) {
      expect(run(ascent(n), const Rounds()).asFamily!.length, n);
    });
  });

  test('a string joined by a fold scales', () {
    // `++` copied both strings, and a `foldl` keeps every accumulator, so joining `n` pieces
    // took `O(n²)` time and memory. A join is the node of its two parts, written out once
    // when it is read as text.
    scaling.check('a foldl of ++, by pieces', 8000, (n) {
      final v = run(joined(n), const Rounds()) as Str;
      expect(v.text.length, n);
      expect(v.text.text.startsWith('abcab'), isTrue);
    });
  });
}
