/// The unit checks of the affine hull and its join.
library;

import 'dart:math';

import 'package:test/test.dart';
import 'package:zed/src/store/hull.dart';
import 'package:zed/src/store/presburger.dart';

import '../support/scaling.dart' as scaling;

/// `sum of c * name` plus `k`.
Lin lin(Map<String, int> terms, [int k = 0]) => terms.entries.fold(
  Lin.constant(BigInt.from(k)),
  (t, e) => t.plus(Lin.atom(Sym(e.key)).times(BigInt.from(e.value))),
);

/// The hull of one point.
Hull point(List<String> names, List<int> v) => Hull.of([
  for (var i = 0; i < names.length; i++) lin({names[i]: 1}, -v[i]),
]);

/// A hull of `n` rows.
Hull rowsOf(int n) => Hull.of([
  for (var i = 0; i < n; i++) lin({'y$i': 1, 'z$i': -1}),
]);

/// `n` joins as at a loop head, each of the hull `h` of `n` rows with itself and one more row;
/// with `copy`, each joins a copy of the hull that shares nothing with it.
void loopJoins(Hull h, int n, {bool copy = false}) {
  for (var i = 0; i < n; i++) {
    final b = h.and(lin({'x$i': 1}, -i));
    h = (copy ? Hull.of(h.rows) : h).join(b);
  }
  expect(h.rows, hasLength(n));
}

/// The rank of the integer vectors, by elimination over the rationals kept fraction-free.
int rank(List<List<BigInt>> vs) {
  final rows = [
    for (final v in vs) [...v],
  ];
  var r = 0;
  for (var col = 0; rows.isNotEmpty && col < rows.first.length; col++) {
    final p = [for (var i = r; i < rows.length; i++) i].where((i) => rows[i][col] != BigInt.zero);
    if (p.isEmpty) continue;
    final t = rows[p.first];
    rows[p.first] = rows[r];
    rows[r] = t;
    for (var i = r + 1; i < rows.length; i++) {
      final c = rows[i][col];
      if (c == BigInt.zero) continue;
      rows[i] = [for (var j = 0; j < t.length; j++) rows[i][j] * t[col] - t[j] * c];
    }
    r++;
  }
  return r;
}

/// Whether `h` is the affine hull of `points`: each row is zero at each point, and the rows
/// number the dimension less the dimension the points span.
void isHullOf(Hull h, List<String> names, List<List<int>> points) {
  final at = [
    for (final p in points)
      {for (var i = 0; i < names.length; i++) Sym(names[i]) as Atom: BigInt.from(p[i])},
  ];
  for (final t in h.rows) {
    for (final m in at) {
      expect(t.eval(m), BigInt.zero, reason: '$t at $m');
    }
  }
  final spanned = rank([
    for (final p in points.skip(1))
      [for (var i = 0; i < names.length; i++) BigInt.from(p[i] - points.first[i])],
  ]);
  expect(h.rows.length, names.length - spanned, reason: '$h');
}

/// The points `x0 + M t` for random small `M`, `x0` and `t`, of dimension at most `k`.
List<List<int>> onPlane(Random rnd, int d, int k, int n) {
  final x0 = [for (var i = 0; i < d; i++) rnd.nextInt(7) - 3];
  final m = [
    for (var i = 0; i < d; i++)
      [for (var j = 0; j < k; j++) rnd.nextInt(3) == 0 ? rnd.nextInt(5) - 2 : 0],
  ];
  return [
    for (var s = 0; s < n; s++)
      () {
        final t = [for (var j = 0; j < k; j++) rnd.nextInt(9) - 4];
        return [
          for (var i = 0; i < d; i++)
            x0[i] + [for (var j = 0; j < k; j++) m[i][j] * t[j]].fold<int>(0, (a, b) => a + b),
        ];
      }(),
  ];
}

void main() {
  test('the textbook join keeps exactly i + j - n', () {
    // {i == 0, j == n} and {i == 1, j == n - 1} both hold i + j == n, and nothing else.
    final a = Hull.of([
      lin({'i': 1}),
      lin({'j': 1, 'n': -1}),
    ]);
    final b = Hull.of([
      lin({'i': 1}, -1),
      lin({'j': 1, 'n': -1}, 1),
    ]);
    expect('${a.join(b)}', 'i + j - n == 0');
    expect('${b.join(a)}', 'i + j - n == 0');
  });

  test('a contradiction is the empty hull, and the identity of join', () {
    final e = Hull.of([
      lin({'x': 1}),
      lin({'x': 1}, -1),
    ]);
    expect(e.isEmpty, isTrue);
    final a = Hull.of([
      lin({'x': 2, 'y': -4}, 6),
    ]);
    expect('$a', 'x - 2 * y + 3 == 0');
    expect(e.join(a), same(a));
    expect(a.join(e), same(a));
  });

  test('the join of point hulls is the hull of the points', () {
    // Random points on random planes; the hulls of the points are joined one at a time, in
    // either order of the names, so the rows that differ lie first or last.
    final rnd = Random(7);
    for (var trial = 0; trial < 200; trial++) {
      final d = 1 + rnd.nextInt(7), k = rnd.nextInt(d + 1), n = 1 + rnd.nextInt(6);
      final names = [for (var i = 0; i < d; i++) 'x$i'];
      final pts = onPlane(rnd, d, k, n);
      for (final order in [names, names.reversed.toList()]) {
        final cols = [for (final s in order) names.indexOf(s)];
        final ps = [
          for (final p in pts) [for (final c in cols) p[c]],
        ];
        final h = ps.map((p) => point(order, p)).reduce((x, y) => x.join(y));
        isHullOf(h, order, ps);
      }
    }
  });

  test('a join of hulls that differ in a few names is exact', () {
    // As at a loop head: the second side is the first with a few names moved by one, and the
    // join is the hull of both sides' points.
    final rnd = Random(11);
    for (var trial = 0; trial < 100; trial++) {
      final d = 4 + rnd.nextInt(8), k = 1 + rnd.nextInt(3);
      final names = [for (var i = 0; i < d; i++) 'x$i'];
      final a = onPlane(rnd, d, k, k + 2);
      final moved = {for (var i = 0; i < 2; i++) rnd.nextInt(d)};
      final b = [
        for (final p in a) [for (var i = 0; i < d; i++) p[i] + (moved.contains(i) ? 1 : 0)],
      ];
      Hull of(List<List<int>> ps) => ps.map((p) => point(names, p)).reduce((x, y) => x.join(y));
      isHullOf(of(a).join(of(b)), names, [...a, ...b]);
    }
  });

  test('a join costs near the rows that differ', () {
    // n joins of hulls of n rows differing in one: near n log² n in all.
    final hulls = {
      for (final m in [256, scaling.factor * 256]) m: rowsOf(m),
    };
    scaling.check('the join of hulls', 256, (m) => loopJoins(hulls[m]!, m));
  });

  test('control: the scaling check catches a join that reads every row', () {
    final hulls = {
      for (final m in [64, scaling.factor * 64]) m: rowsOf(m),
    };
    expect(
      () => scaling.check('the join of copies', 64, (m) => loopJoins(hulls[m]!, m, copy: true)),
      throwsStateError,
    );
  });
}
