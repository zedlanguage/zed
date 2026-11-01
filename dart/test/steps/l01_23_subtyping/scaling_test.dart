/// Step L1.23: the tuple and morphism parts at the rule of low complexity (DESIGN.md Part G).
/// The union of `C` differences `m(i) - m(i + 1000)` has a decision diagram of `2^C` nodes,
/// since every `m(i)` is ordered before every `m(i + 1000)`. A connective whose diagram would
/// have more nodes than its operands keeps its operands instead, so building the union and its
/// complement stay linear in `C`, and the queries on them are decided exactly: `b <: b | a` by
/// expanding on `b`, which both sides share, and `!b & a` by passing over paths whose taken
/// types are disjoint. A product of tuple types covered by many negated ones is split into
/// disjoint pieces, and a negated type disjoint from a piece is passed over.
library;

import 'dart:isolate';
import 'dart:math' as math;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/scaling.dart';

Type lit(int i) => Type.lit(Int(i))!;

Type morphism(int i) => Type.morphism(Type.empty, Type.top, lit(i));

Type pair(int i) => Type.tuple([lit(i), Type.top]);

/// The union of `c` differences of the atoms `atom` makes.
Type union(int c, Type Function(int) atom) =>
    [for (var i = 0; i < c; i++) i].fold(Type.empty, (u, i) => u | (atom(i) - atom(i + 1000)));

void run(int c, Type Function(int) atom) {
  final b = union(c, atom);
  final n = ~b;
  expect((n & atom(5000)).isEmpty, isFalse);
  expect(b.subtype(b | atom(5000)), isTrue);
}

Type range(int from, int to) => Type.unionAll([for (var i = from; i < to; i++) lit(i)]);

/// The tuples `(i, b + j)` for `i, j < n`, as a product and as the union of its `n²` cells.
(Type, Type) grid(int n, int b) {
  final cells = Type.unionAll([
    for (var k = 0; k < n * n; k++) Type.tuple([lit(k ~/ n), lit(b + k % n)]),
  ]);
  return (Type.tuple([range(0, n), range(b, b + n)]), cells);
}

/// The tuple `(… ((b, b), b + 1) …, b + d - 1)`, nested `d` deep.
Type nested(int d, int b) {
  var t = lit(b);
  for (var i = 0; i < d; i++) {
    t = Type.tuple([t, lit(b + i)]);
  }
  return t;
}

Type atom(int i) => Type.atom('a$i');

void main() {
  test('the parts scale', () {
    check('morphism differences, by count', 16, (c) => run(c, morphism));
    check('tuple differences, by count', 16, (c) => run(c, pair));
  });

  test('small unions are still decided', () {
    // The answers `the parts scale` times, at a count small enough that unions of diagrams
    // stay diagrams.
    for (final atom in [morphism, pair]) {
      final b = union(6, atom);
      expect(b.subtype(b | atom(5000)), isTrue, reason: '$b');
      expect(b.subtype(atom(0)), isFalse, reason: '$b');
      expect((b - b).isEmpty, isTrue, reason: '$b');
    }
  });

  test('a product covered by its cells scales', () {
    // Each cell is disjoint from all but one piece of the split, and contains that piece, so
    // the split of the product makes one piece per cell; splitting on every cell in turn made
    // `n^(n²)` pieces in the worst order. Building the cells one at a time made `O(n⁴)`
    // nodes. Each run takes a new `b`, so no run reads another's results. Below about 512
    // cells fixed costs dominate building the grid.
    var fresh = 1;
    check('a grid and its cells, by cell count', 512, (c) {
      final n = math.sqrt(c).round();
      final (p, cells) = grid(n, 10000 * fresh++);
      expect((p - cells).isEmpty, isTrue, reason: 'the cells cover the grid at n = $n');
    });
  });

  test('a cell left out is found', () {
    for (final n in [2, 3, 5, 8]) {
      final (p, cells) = grid(n, 0);
      final hole = Type.tuple([lit(n ~/ 2), lit(n - 1)]);
      final rest = (p - cells) | hole;
      expect((p - (cells - hole)).isEmpty, isFalse, reason: 'n = $n');
      expect((rest - hole).isEmpty, isTrue, reason: 'n = $n');
    }
  });

  test('negated types disjoint from the product are passed over', () {
    // The decoy `(bits(i), 1000 + i)`, with `bits(i)` the numbers below 8192 with bit `i` set,
    // misses `(0..8192, 0)` in the second component, and splitting on it would cut every piece
    // in two in the first: `2^13` pieces for the 13 decoys, unless a disjoint one is passed
    // over. The pieces are all met only when the answer is `true`, here once the two halves
    // of the product are reached.
    Type bits(int i) => Type.unionAll([
      for (var x = 0; x < 8192; x++)
        if (x >> i & 1 == 1) lit(x),
    ]);
    final p = Type.tuple([range(0, 8192), lit(0)]);
    final halves = Type.tuple([range(0, 4096), lit(0)]) | Type.tuple([range(4096, 8192), lit(0)]);
    final decoys = Type.unionAll([
      for (var i = 0; i < 13; i++) Type.tuple([bits(i), lit(1000 + i)]),
    ]);
    expect((p - decoys).isEmpty, isFalse);
    expect((p - (decoys | halves)).isEmpty, isTrue);
  });

  test('passing over disjoint negated types scales', () {
    // As above with `k` decoys, the first component a tuple of `k` bits so that a meet costs
    // `O(k)`: the decoy `(bits(i), b + 1 + i)` has bit `i` set, and misses `(U, b)` in the
    // second component. The pieces are all met only when the answer is `true`, here once the
    // two halves on bit 0 are reached. Passed over, `k` decoys cost `O(k²)`; split on, `2^k`
    // pieces. Each run takes a new `b`, so no run reads another's results.
    final bit = lit(0) | lit(1);
    Type bits(int k, int i) => Type.tuple([for (var j = 0; j < k; j++) j == i ? lit(1) : bit]);
    final made = {
      for (final k in [2, 16])
        k: (Type.tuple(List.filled(k, bit)), [for (var i = 0; i < k; i++) bits(k, i)]),
    };
    var next = 0;
    checkOrder('decoys passed over, by count', 2, 2, (k) {
      next += 100;
      final b = 1000000 + next;
      final (u, bs) = made[k]!;
      final p = Type.tuple([u, lit(b)]);
      final decoys = Type.unionAll([
        for (final (i, s) in bs.indexed) Type.tuple([s, lit(b + 1 + i)]),
      ]);
      // The two halves on bit 0 cover `(U, b)`, so every piece must be met.
      Type half(int v) => Type.tuple([
        Type.tuple([lit(v), ...List.filled(k - 1, bit)]),
        lit(b),
      ]);
      final cover = decoys | half(0) | half(1);
      expect((p - decoys).isEmpty, isFalse);
      expect((p - cover).isEmpty, isTrue);
    });
  });

  test('many negated types passed over scale', () {
    // The product `P` of the sets `b + 10_000·k + (0..n)` for `k < 5`, then `b`, less the
    // `n` tuples `T_i` of `b + 10_000·k + i`, then `b - 1`. Each `T_i` meets `P` in the first
    // five components and misses it in the last, so it is passed over, after five non-empty
    // intersections. Only the emptiness results decided since a query began are dropped when
    // one is found non-empty, so the `5n` results cost `O(n)`, not a scan of all of them each.
    // Each run takes a new `b`, so no run reads another's results.
    var fresh = 1;
    check('a product less n tuples passed over, by n', 1000, (n) {
      final b = 100000 * fresh++;
      final p = Type.tuple([
        for (var k = 0; k < 5; k++) range(b + 10000 * k, b + 10000 * k + n),
        lit(b),
      ]);
      final decoys = Type.unionAll([
        for (var i = 0; i < n; i++)
          Type.tuple([for (var k = 0; k < 5; k++) lit(b + 10000 * k + i), lit(b - 1)]),
      ]);
      expect((p - decoys).isEmpty, isFalse, reason: 'the decoys miss the product at n = $n');
    });
  });

  test('nested tuples scale', () {
    // Types and nodes are ordered by a hash of their contents, kept in each when it is made,
    // so placing a tuple among others does not read down the nested tuples to where they
    // differ, which made building a tuple nested `d` deep take `O(d²)` steps.
    var fresh = 1;
    check('a nested tuple and a query on it, by depth', 400, (d) {
      final b = 100000 * fresh++;
      final x = nested(d, b);
      expect(x.subtype(nested(d, b) | lit(1)), isTrue, reason: 'at depth $d');
      expect(x.subtype(nested(d, b + 1)), isFalse, reason: 'at depth $d');
    });
  });

  test('a type built in another isolate is the same type', () async {
    // The two copies are distinct objects, and are equal by their contents.
    Type make() => nested(20, 7) | Type.morphism(Type.empty, Type.top, nested(5, 3));
    final here = make();
    final there = await Isolate.run(make);
    expect(identical(here, there), isFalse);
    expect(here, there);
    expect('$here', '$there');
    expect(here.subtype(there) && there.subtype(here), isTrue);
    expect(here.subtype(nested(20, 8)), isFalse);
  });

  test('literals and atoms joined one at a time scale', () {
    // The sets of literals and atom names are persistent, each operation walks the smaller
    // one, and the hash of a set is a sum kept as it changes, so joining `n` of them one at a
    // time does not copy both sets or rehash every member each time, `O(n²)`.
    check('literals joined one at a time, by count', 1000, (n) {
      var u = Type.empty;
      for (var i = 0; i < n; i++) {
        u = u | lit(i);
      }
      expect(lit(n ~/ 2).subtype(u) && !lit(n).subtype(u), isTrue);
      expect(u, Type.unionAll([for (var i = n - 1; i >= 0; i--) lit(i)]));
    });
    check('atoms joined one at a time, by count', 1000, (n) {
      var u = Type.empty;
      for (var i = 0; i < n; i++) {
        u = u | atom(i);
      }
      expect(atom(n ~/ 2).subtype(u) && !atom(n).subtype(u), isTrue);
      expect(u, Type.unionAll([for (var i = n - 1; i >= 0; i--) atom(i)]));
    });
    check('literals and atoms removed one at a time, by count', 1000, (n) {
      var left =
          Type.unionAll([for (var i = 0; i < n; i++) lit(i)]) |
          Type.unionAll([for (var i = 0; i < n; i++) atom(i)]);
      for (var i = 1; i < n; i++) {
        left = left - lit(i) - atom(i);
      }
      expect(left, lit(0) | atom(0));
    });
  });

  test('literal and atom sets combine exactly', () {
    // Every pair of signs and both connectives, with sets of unequal sizes in either order.
    Type set(int from, int to) =>
        range(from, to) | Type.unionAll([for (var i = from; i < to; i++) atom(i)]);
    final (a, b) = (set(0, 6), set(4, 5));
    final both = lit(4) | atom(4);
    for (final (x0, y0) in [(a, b), (b, a)]) {
      for (final (nx, ny) in [(false, false), (false, true), (true, false), (true, true)]) {
        final x = nx ? ~x0 : x0;
        final y = ny ? ~y0 : y0;
        final (or, and) = (x | y, x & y);
        for (final v in [
          for (var i = 0; i < 8; i++) ...[lit(i), atom(i)],
        ]) {
          final (inX, inY) = (v.subtype(x), v.subtype(y));
          expect(v.subtype(or), inX || inY, reason: '$v in $x | $y');
          expect(v.subtype(and), inX && inY, reason: '$v in $x & $y');
        }
        expect((or - and) | and, or);
      }
    }
    expect(a & b, both);
    expect((a - b) | both, a);
  });

  test('listing values past the cap stops early', () {
    // `(S, S)` for a set `S` of `n` literals has `n²` values, past a cap of `n`; the product
    // of the components' values is compared with the cap before it is built, not after.
    check('the values of a square past the cap, by n', 200, (n) {
      final s = range(0, n);
      final square = Type.tuple([s, s]);
      expect(square.values(n), isNull, reason: 'n = $n');
      expect(s.values(n)?.length, n);
    });
    final s = range(0, 3);
    final square = Type.tuple([s, s]);
    expect(square.values(9)?.length, 9);
    expect(square.values(8), isNull);
    // A path is listed when the product of its positive parts is within the cap, before the
    // negated tuples are taken out, so 8 values from a product of 9 need a cap of 9.
    final rest = square - Type.tuple([lit(0), lit(0)]);
    expect(rest.values(8), isNull);
    expect(rest.values(9)?.length, 8);
  });
}
