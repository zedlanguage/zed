/// Witness-catalog bijectivity (DESIGN.md sec:grouping): each of the eight entries that need
/// no layer, run on finite domains. A witnessed key map must never collide, and a map the
/// catalog states with its inverse must give back the family it started from. Each side
/// condition comes with the domain on which dropping it collides or breaks the inverse.
///
/// The reference evaluator checks the collision rule on every reindex, so a key map is
/// injective on a domain exactly when its reindex of that domain is not a collision.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/check.dart';
import '../../support/kernel.dart';

/// A one-level family `k -> v` over the integers `lo..=hi`, each entry its key's reading.
Family readings(int lo, int hi) =>
    Family.of([for (var k = lo; k <= hi; k++) (Int(k), Int(100 + k))]);

/// A two-level family `i -> j -> v` over the box `rows × cols`: a pixel grid whose entry is
/// its brightness.
Family grid((int, int) rows, (int, int) cols) => Family.fromLeaves([
  for (var i = rows.$1; i <= rows.$2; i++)
    for (var j = cols.$1; j <= cols.$2; j++) ([Int(i), Int(j)], Int((i * 7 + j * 3) % 256)),
]);

/// Rekeys `f` by `keys(path)`, keeping each entry's value.
Term rekey(Term f, List<Term> Function(Term p) keys) =>
    reindex(f, func(2, (x) => path(keys(x[0]))), func(2, (x) => x[1]));

/// Whether the rekey ran without a collision.
bool injective(Term t) => switch (outcome(t)) {
  Value() => true,
  CollisionError() => false,
  final e => throw StateError('the rekey failed with $e'),
};

/// The rekey's result, which must exist.
Value value(Term t) => eval(t);

/// The family `f` with each leaf moved to `to(keypath)`.
Family moved(Family f, Keypath Function(Keypath) to) =>
    Family.fromLeaves([for (final (k, v) in f.leaves()) (to(k), v)]);

/// `(k1, k2) ↦ k1·s + k2`.
Term pack(Term f, int s) => rekey(f, (p) => [add(mul(key(p, 0), lit(s)), key(p, 1))]);

/// `k ↦ (k div s, k mod s)`.
Term unpack(Term f, int s) => rekey(f, (p) => [idiv(key(p, 0), lit(s)), modulo(key(p, 0), lit(s))]);

void main() {
  // Literal key occurrence.

  test('literal key occurrence keeps every key, and dropping one collides', () {
    final g = lit(grid((0, 3), (0, 4)));
    final same = rekey(g, (p) => [key(p, 0), key(p, 1)]);
    expect(value(same), grid((0, 3), (0, 4)));
    // Keeping only the row puts the five pixels of a row at one keypath.
    expect(injective(rekey(g, (p) => [key(p, 0)])), isFalse);
  });

  // Tupling and permutation.

  test('transposing twice gives back the grid', () {
    Term swap(Term f) => rekey(f, (p) => [key(p, 1), key(p, 0)]);
    final g = grid((-2, 2), (0, 3));
    final t = value(swap(lit(g)));
    expect(t, moved(g, (k) => [k[1], k[0]]));
    expect(value(swap(lit(t))), g);
  });

  // Componentwise maps.

  test('componentwise witnessed maps are injective and a noninjective component collides', () {
    // Shift the rows by one and double the columns: a product of injections.
    final g = lit(grid((-3, 3), (-3, 3)));
    final shifted = rekey(g, (p) => [add(key(p, 0), lit(1)), mul(key(p, 1), lit(2))]);
    expect(injective(shifted), isTrue);
    // Back again: subtract one, halve.
    final back = rekey(shifted, (p) => [sub(key(p, 0), lit(1)), idiv(key(p, 1), lit(2))]);
    expect(value(back), grid((-3, 3), (-3, 3)));
    // Squaring a column is not injective on columns of both signs.
    expect(injective(rekey(g, (p) => [key(p, 0), mul(key(p, 1), key(p, 1))])), isFalse);
  });

  // Widening.

  test('widening by the value keeps the old key and never collides', () {
    // File each reading under (station, reading): the new key contains the old one, so two
    // stations with equal readings stay apart.
    final f = lit(
      Family.of([for (var k = 0; k < 6; k++) (Int(k), Int(k % 2)), (const Int(6), const Int(0))]),
    );
    final widened = reindex(f, func(2, (x) => path([key(x[0], 0), x[1]])), func(2, (x) => x[1]));
    expect(injective(widened), isTrue);
    // Keying by the reading alone collides on the repeated reading.
    final byValue = reindex(f, func(2, (x) => path([x[1]])), func(2, (x) => x[1]));
    expect(injective(byValue), isFalse);
  });

  // Strictly monotone arithmetic.

  test('strictly monotone arithmetic on a range is injective', () {
    final r = lit(readings(-8, 8));
    for (final step in <Term Function(Term)>[
      (k) => add(k, lit(1)),
      (k) => mul(k, lit(2)),
      (k) => sub(mul(k, lit(3)), lit(5)),
    ]) {
      expect(injective(rekey(r, (p) => [step(key(p, 0))])), isTrue);
    }
    // Monotone but not strictly: halving collides on -8..=8 (k = 0 and k = 1 both give 0).
    expect(injective(rekey(r, (p) => [idiv(key(p, 0), lit(2))])), isFalse);
    // Strictly monotone on half the range only: squaring collides on -1 and 1.
    expect(injective(rekey(r, (p) => [mul(key(p, 0), key(p, 0))])), isFalse);
    // Squaring is injective on the nonnegative half, where it is strictly monotone.
    expect(injective(rekey(lit(readings(0, 8)), (p) => [mul(key(p, 0), key(p, 0))])), isTrue);
  });

  // Modulo over a range no wider than the modulus.

  test('a ring buffer slot is injective on at most p contiguous timestamps', () {
    // Timestamps go into a ring buffer of p slots by t mod p. Any window of p contiguous
    // timestamps, negative ones included, fills each slot once; one wider, two share a slot.
    for (var p = 1; p <= 5; p++) {
      for (var base = -7; base <= 3; base++) {
        Term slot(int w) =>
            rekey(lit(readings(base, base + w - 1)), (q) => [modulo(key(q, 0), lit(p))]);
        for (var w = 1; w <= p; w++) {
          expect(injective(slot(w)), isTrue, reason: 'p = $p, base = $base, width $w');
        }
        expect(injective(slot(p + 1)), isFalse, reason: 'p = $p, base = $base, width ${p + 1}');
      }
    }
  });

  // Affine packing and unpacking.

  test('row-major packing and its euclidean unpacking are inverse with negative rows', () {
    // A grid whose rows run from -4, so the packed offsets and the quotients are negative.
    for (var s = 1; s <= 5; s++) {
      final g = grid((-4, 3), (0, s - 1));
      final packed = pack(lit(g), s);
      expect(injective(packed), isTrue, reason: 'stride $s');
      expect(value(unpack(packed, s)), g, reason: 'stride $s');
      // The other direction: unpack a buffer of offsets -20..=20 and pack it back.
      final buffer = readings(-20, 20);
      expect(value(pack(unpack(lit(buffer), s), s)), buffer, reason: 'stride $s');
    }
  });

  test('a stride one short of the span collides', () {
    // Columns 0..s need stride s; stride s - 1 sends (i, s - 1) and (i + 1, 0) to one offset.
    for (var s = 2; s <= 5; s++) {
      expect(
        injective(pack(lit(grid((-2, 2), (0, s - 1))), s - 1)),
        isFalse,
        reason: 'stride ${s - 1}',
      );
    }
  });

  test('truncated division fails the inverse law on negative quotients', () {
    // Truncated division rounds the quotient toward zero, and its remainder takes the sign of
    // the dividend: -3 = 0·4 + (-3) instead of (-1)·4 + 1.
    const s = 4;
    Term truncDiv(Term k) =>
        if_(lt(k, lit(0)), sub(lit(0), idiv(sub(lit(0), k), lit(s))), idiv(k, lit(s)));
    Term truncUnpack(Term f) => rekey(f, (p) {
      final k = key(p, 0);
      return [truncDiv(k), sub(k, mul(truncDiv(k), lit(s)))];
    });
    // On rows 0.. the truncated and Euclidean pairs agree.
    final rowsUp = grid((0, 3), (0, 3));
    expect(value(truncUnpack(pack(lit(rowsUp), s))), rowsUp);
    // On row -1 they do not: (-1, 1) packs to -3 and comes back as (0, -3).
    final rowsDown = grid((-1, 0), (0, 3));
    final back = value(truncUnpack(pack(lit(rowsDown), s)));
    expect(back, isNot(rowsDown));
    final row = back.asFamily![const Int(0)];
    expect(row?.asFamily?[const Int(-3)], isNotNull);
  });

  test('packing applies lexicographically at depth three', () {
    // A tiled image: (tile row, row in tile, column) with 3 rows a tile and 4 columns,
    // packed to one offset by ((t·3) + r)·4 + c and unpacked by two Euclidean divisions.
    final tiles = Family.fromLeaves([
      for (var t = -2; t <= 1; t++)
        for (var r = 0; r < 3; r++)
          for (var c = 0; c < 4; c++) ([Int(t), Int(r), Int(c)], Int(t * 12 + r * 4 + c)),
    ]);
    final packed = rekey(lit(tiles), (p) {
      final row = add(mul(key(p, 0), lit(3)), key(p, 1));
      return [add(mul(row, lit(4)), key(p, 2))];
    });
    expect(injective(packed), isTrue);
    // Each entry lands at the offset its value records.
    final flat = value(packed).asFamily!;
    expect(flat.leaves().every((l) => l.$1[0] == l.$2), isTrue);
    final unpacked = rekey(packed, (p) {
      final k = key(p, 0);
      final row = idiv(k, lit(4));
      return [idiv(row, lit(3)), modulo(row, lit(3)), modulo(k, lit(4))];
    });
    expect(value(unpacked), tiles);
  });

  // Integer affine maps of full column rank.

  test('the wavefront skew is a bijection with an integer inverse', () {
    // (i, j) ↦ (i, i + j) has determinant 1; its inverse is (a, c) ↦ (a, c - a). No range
    // condition: it holds on a box of both signs.
    final g = grid((-4, 4), (-4, 4));
    final skew = rekey(lit(g), (p) => [key(p, 0), add(key(p, 0), key(p, 1))]);
    expect(injective(skew), isTrue);
    final unskew = rekey(skew, (p) => [key(p, 0), sub(key(p, 1), key(p, 0))]);
    expect(value(unskew), g);
  });

  test('a tall map of full column rank is injective and a rank-deficient one collides', () {
    final g = lit(grid((-4, 4), (-4, 4)));
    // (i, j) ↦ (i + j, i - 2j, 3i + j): three rows, two independent columns.
    expect(
      injective(
        rekey(g, (p) {
          final (i, j) = (key(p, 0), key(p, 1));
          return [add(i, j), sub(i, mul(j, lit(2))), add(mul(i, lit(3)), j)];
        }),
      ),
      isTrue,
    );
    // (i, j) ↦ i + j, the anti-diagonal sum, has rank 1 and is rejected: (0, 1) and (1, 0).
    expect(injective(rekey(g, (p) => [add(key(p, 0), key(p, 1))])), isFalse);
    // (i, j) ↦ (i + j, 2i + 2j): two rows but dependent columns, so still rank 1.
    expect(
      injective(
        rekey(g, (p) {
          final s = add(key(p, 0), key(p, 1));
          return [s, mul(s, lit(2))];
        }),
      ),
      isFalse,
    );
  });
}
