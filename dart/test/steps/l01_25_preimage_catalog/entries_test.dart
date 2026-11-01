/// The catalog's entries on ordinary preconditions and guards. Each preimage is printed and
/// checked against the interpreter over a window of each domain.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/store.dart';

import 'support.dart';

/// The preimage of `true` under `src` over `ds`, printed, after checking it on the window
/// `-60..=60`.
String holds(String src, List<Dom> ds) {
  final p = pre(src, ds, const BoolDemand(true));
  check(function(src).$2, doms(ds), const BoolDemand(true), p, (-60, 60));
  return shown(p);
}

Dom any(String n) => (n, null, null);

void main() {
  test('a square bound is read as a power and inverted exactly', () {
    // The z3 fixture of sec:constraints gives `-9 <= x <= 9`.
    expect(holds('ok(x) = x * x <= 99;\n', [any('x')]), 'x [-9..=9]; exact');
    expect(holds('ok(x) = x * x * x > 26;\n', [any('x')]), 'x [3..]; exact');
    expect(holds('ok(x) = x ** 2 >= 50;\n', [any('x')]), 'x [..=-8, 8..]; exact');
  });

  test('shifts and scalings by a constant invert exactly', () {
    expect(holds('ok(n) = 3 * n + 1 >= 10;\n', [any('n')]), 'n [3..]; exact');
    expect(holds('ok(n) = 10 - n > 4;\n', [any('n')]), 'n [..=5]; exact');
    expect(holds('ok(n) = -2 * n < 7;\n', [any('n')]), 'n [-3..]; exact');
    expect(holds('ok(n) = n * 0 == 1;\n', [any('n')]), 'n []; exact');
  });

  test('Euclidean division and remainder by a constant invert exactly', () {
    expect(holds('ok(i) = i div 4 == 2;\n', [any('i')]), 'i [8..=11]; exact');
    expect(holds('ok(i) = i div -4 == 2;\n', [any('i')]), 'i [-8..=-5]; exact');
    // Within two periods, the remainder pieces of each, exactly.
    expect(holds('ok(i) = i mod 10 == 3;\n', [('i', 0, 19)]), 'i [3..=3, 13..=13]; exact');
    // Over more periods, the first and last are listed and those between are one piece, so
    // the set is necessary only, however small the domain.
    expect(holds('ok(i) = i mod 10 == 3;\n', [('i', 0, 40)]), 'i [3..=3, 13..=33]; necessary');
    expect(
      holds('ok(i) = i mod 10 == 3;\n', [('i', 0, 1000000000)]),
      'i [3..=3, 13..=999999993]; necessary',
    );
    // With no bound on `i`, the remainders are not a finite union: necessary only.
    expect(holds('ok(i) = i mod 10 == 3;\n', [any('i')]), 'i [..]; necessary');
    // Every remainder of 10 is below 10.
    expect(holds('ok(i) = i mod 10 < 10;\n', [any('i')]), 'i [..]; exact');
    expect(holds('ok(i) = i mod 0 == 0;\n', [any('i')]), 'i []; exact');
  });

  test('abs and negation invert at their endpoints', () {
    expect(holds('ok(d) = abs(d) < 4;\n', [any('d')]), 'd [-3..=3]; exact');
    expect(holds('ok(d) = abs(d) > 2;\n', [('d', -5, 10)]), 'd [-5..=-3, 3..=10]; exact');
    expect(holds('ok(d) = -d <= -3;\n', [any('d')]), 'd [3..]; exact');
  });

  test('tests combine by meet and union', () {
    expect(
      holds('ok(x, y) = x >= 0 && y < 10;\n', [any('x'), any('y')]),
      'x [0..]; y [..=9]; exact',
    );
    expect(holds('ok(x) = x < 0 || x > 9;\n', [any('x')]), 'x [..=-1, 10..]; exact');
    // A union over two inputs is not a box: the join is necessary only.
    expect(
      holds('ok(x, y) = x < 0 || y < 0;\n', [any('x'), any('y')]),
      'x [..]; y [..]; necessary',
    );
    expect(holds('ok(x) = !(x > 3 && x < 7);\n', [any('x')]), 'x [..=3, 7..]; exact');
  });

  test('a branch is the union of its arms', () {
    expect(holds('ok(x) = if x > 0 { x < 5 } else { x > -3 };\n', [any('x')]), 'x [-2..=4]; exact');
  });

  test('a comparison of two terms constrains their difference', () {
    // `x < y` on boxes is a relation, which L1.38 keeps; the box is its projection.
    expect(
      holds('ok(x, y) = x < y;\n', [('x', 5, null), ('y', null, 8)]),
      'x [5..=7]; y [6..=8]; necessary',
    );
  });

  test('a listed box is enumerated and a range is not', () {
    // Each piece holds no more members than its endpoints, so the box is listed.
    const src = 'ok(x) = x * x mod 10 == 9;\n';
    final ds = listed([
      ('x', [0, 1, 3, 4, 7, 13, 14, 17, 18]),
    ]);
    final p = preimage(function(src).$2, ds, const BoolDemand(true));
    check(function(src).$2, ds, const BoolDemand(true), p, (0, 20));
    expect(shown(p), 'x [3..=3, 7..=7, 13..=13, 17..=17]; exact; enumerated');
    // The same members within a range are left to the catalog, however few they are.
    expect(holds(src, [('x', 0, 18)]), 'x [3..=3, 5..=17]; necessary');
    // Not a box: the projection, necessary only.
    expect(
      holds('ok(x, y) = x + y == 3;\n', [('x', 0, 3), ('y', 0, 3)]),
      'x [0..=3]; y [0..=3]; necessary',
    );
  });

  test('a division that can fail keeps only the points that do not', () {
    // `100 div d` fails at `d == 0`, which no preimage of a demand holds.
    const src = 'ok(d) = 100 div d >= 20;\n';
    final ds = listed([
      ('d', [-10, -1, 0, 2, 5, 6, 10]),
    ]);
    final p = preimage(function(src).$2, ds, const BoolDemand(true));
    check(function(src).$2, ds, const BoolDemand(true), p, (-10, 10));
    expect(shown(p), 'd [2..=2, 5..=5]; exact; enumerated');
  });

  test('a call is read through', () {
    expect(
      holds('ok(x) = sq(x + 1) <= 16;\nsq(positional v) = v * v;\n', [any('x')]),
      'x [-5..=3]; exact',
    );
  });

  // A summary reached again from another call keeps only the inputs it narrows: each call of
  // `f1` reads `f0` over the other's interval, and once kept the interval of the first call's
  // parameter with it, which cut `x = 50` from the second. The body is `4 * x + 4`, whose sum
  // of calls the catalog projects, necessary only; the linear relations of step L1.38 make it
  // exact.
  test('a summary reached from another call keeps only what it narrows', () {
    const src =
        'ok(x) = f2(x) >= 204;\nf2(positional v) = f1(v) + f1(v + 1);\n'
        'f1(positional v) = f0(v) + f0(v + 1);\nf0(positional v) = v;\n';
    expect(holds(src, [('x', 0, 50)]), 'x [0..=50]; necessary');
  });

  // Kernel integers are unbounded, so a sum past the 64-bit range is an integer like any
  // other. A lower end past the largest 64-bit integer must not round to `+inf`, which would
  // empty the interval it began, and the backward pass would then cut every input.
  test('bounds past the 64-bit range keep the box', () {
    const b = 1 << 62;
    final xy = [('x', 0, 1), ('y', -2, 2)];
    for (final src in [
      'ok(x, y) = x + $b + $b + $b - y >= 0;\n',
      'ok(x, y) = (x + $b) + (x + $b) + (x + $b) - y >= 0;\n',
      'ok(x, y) = x * $b * 4 + $b * 4 - y >= 0;\n',
      'ok(x, y) = -x - $b - $b - $b + y <= 0;\n',
      'ok(x, y) = -(x + $b + $b) - y < 0;\n',
      'ok(x, y) = (x + $b + $b + $b) div 3 - y >= 0;\n',
      'ok(x, y) = (x + $b + $b) * 2 - y > 0;\n',
    ]) {
      expect(holds(src, xy), 'x [0..=1]; y [-2..=2]; exact', reason: src);
    }
    const m = maxInt;
    // The demand's end `m + 1` is rounded to `m`, so the backward pass is not exact, and the
    // listed box is enumerated; the linear relations of step L1.38 find it first.
    expect(holds('ok(x) = x + $m > $m;\n', [('x', 0, 1)]), 'x [1..=1]; exact; enumerated');
    // Not exact: whether a point is cut is not decided, but none is.
    const src = 'ok(x, y) = x * $b * 4 - y >= 0;\n';
    expect(holds(src, xy), startsWith('x [0..=1]; y [-2..=2]'), reason: src);
  });

  test('the forward pass confirms a box the backward pass cannot', () {
    // The difference `x - y <= 0` is not inverted exactly over two inputs, but every point of
    // the box meets it, which the forward pass finds without enumerating.
    expect(
      holds('ok(x, y) = x <= y;\n', [('x', null, 3), ('y', 3, null)]),
      'x [..=3]; y [3..]; exact',
    );
    expect(
      holds('ok(x, y) = x * y >= 1;\n', [('x', 1, null), ('y', 1, null)]),
      'x [1..]; y [1..]; exact',
    );
  });

  test('a set of many pieces is kept exact', () {
    // No limit merges the pieces a program writes: nine exclusions give ten pieces.
    const src =
        'ok(x) = x != 1 && x != 3 && x != 5 && x != 7 && x != 9 && x != 11 && x != 13 '
        '&& x != 15 && x != 17;\n';
    final p = pre(src, [any('x')], const BoolDemand(true));
    expect(p.exact, isTrue, reason: shown(p));
    expect(p.domains['x']!.pieces.length, 10, reason: shown(p));
    check(function(src).$2, doms([any('x')]), const BoolDemand(true), p, (-60, 60));
  });

  test('a test that can fail is not combined as a boolean', () {
    // At `x == 0` both sides fail, and `==` finds two equal failures equal.
    const src = 'ok(x) = (10 div x < 100) == (10 div x < 50);\n';
    expect(holds(src, [('x', -3, 3)]), 'x [-3..=3]; necessary');
    final ds = listed([
      ('x', [-3, 0, 3]),
    ]);
    final p = preimage(function(src).$2, ds, const BoolDemand(true));
    check(function(src).$2, ds, const BoolDemand(true), p, (-3, 3));
    expect(shown(p), 'x [-3..=-3, 0..=0, 3..=3]; exact; enumerated');
  });

  test('a strict disjunction with a failing side is necessary only', () {
    // The kernel's `||` passes a failure through: `x div 0 > 1` fails at every `x`, so no
    // point meets the test, though the left side alone holds on `[0..]`.
    const x = Var('x');
    Term n(int v) => Lit(Int(v));
    final t = PrimApp(Prim.or, [
      PrimApp(Prim.ge, [x, n(0)]),
      PrimApp(Prim.gt, [
        PrimApp(Prim.intDiv, [x, n(0)]),
        n(1),
      ]),
    ]);
    final ds = doms([any('x')]);
    final p = preimage(t, ds, const BoolDemand(true));
    expect(check(t, ds, const BoolDemand(true), p, (-60, 60)), 0);
    expect(shown(p), 'x [0..]; necessary');
  });
}
