/// `@exact` scopes: the scope is bottom exactly when no point of its names' intervals and
/// classes meets the written constraints. The names keep their algebraic bounds; a question
/// about the exact set is a test assumed in the scope.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart' hide Lattice;
import 'package:zed/store.dart';

import 'support.dart';

/// The scope of integer names `ns`, each within `lo..=hi`, exact or not.
Scope within(List<(String, int, int)> ns, bool exact) {
  final names = [for (final (n, _, _) in ns) (n, Product.ofType(Type.integer))];
  var s = exact ? Scope.exact(names) : Scope(names);
  for (final (n, lo, hi) in ns) {
    final range = prim(Prim.and, [
      prim(Prim.ge, [Var(n), lit(lo)]),
      prim(Prim.le, [Var(n), lit(hi)]),
    ]);
    s = s.assume(range, true, none);
  }
  return s;
}

/// `a * b mod 10 == r`.
Term productMod10(String a, String b, int r) => prim(Prim.eq, [
  prim(Prim.mod, [
    prim(Prim.mul, [Var(a), Var(b)]),
    lit(10),
  ]),
  lit(r),
]);

Scope written(Scope s, List<Term> ts) {
  for (final t in ts) {
    s.write(t);
  }
  return s..reduce();
}

/// `n == v`.
Term isTerm(String n, int v) => prim(Prim.eq, [Var(n), lit(v)]);

/// The values of `n` in `lo..=hi` that the scope allows, each found by assuming `n == v`.
List<int> allowed(Scope s, String n, int lo, int hi) => [
  for (var v = lo; v <= hi; v++)
    if (!s.assume(isTerm(n, v), true, none).bottom) v,
];

void main() {
  test('an exact scope allows only the points that meet a written constraint', () {
    final exact = written(within([('n', 0, 30)], true), [productMod10('n', 'n', 9)]);
    // The bounds stay algebraic: nothing lists the exact set.
    expect('${exact.get('n').ints}', '[0..=30]');
    expect(allowed(exact, 'n', 0, 30), [3, 7, 13, 17, 23, 27]);
  });

  test('a constraint through a shared name decides the other name', () {
    // `m * n mod 10 == 1` alone allows every odd `m` not a multiple of 5; with `n` among
    // 3, 7, 13, 17, 23 and 27, only `m` ending in 3 or 7 has a partner.
    final ts = [productMod10('m', 'n', 1), productMod10('n', 'n', 9)];
    final s = written(within([('m', 0, 20), ('n', 0, 30)], true), ts);
    expect(s.bottom, isFalse);
    expect(allowed(s, 'm', 0, 20), [3, 7, 13, 17]);
  });

  test('an exact scope with no point meeting its constraints is bottom', () {
    // `n * n` never ends in 9 when `n` ends in 5.
    final five = prim(Prim.eq, [
      prim(Prim.mod, [const Var('n'), lit(10)]),
      lit(5),
    ]);
    final ts = [productMod10('n', 'n', 9), five];
    final plain = written(within([('n', 0, 30)], false), ts);
    expect(!plain.bottom && !plain.get('n').isEmpty, isTrue);
    final s = written(within([('n', 0, 30)], true), ts);
    expect(s.bottom || s.get('n').isEmpty, isTrue, reason: '${s.get('n')}');
  });

  test('a point inside a huge range is excluded without listing the range', () {
    // Over `0..=10^12` the exact set of `n * n mod 10 == 9` has 4·10^11 members; excluding
    // 4 assumes `n == 4`, a box of one point, and a witness for the whole range is found by
    // halving toward the first point.
    final s = written(within([('n', 0, 1000000000000)], true), [productMod10('n', 'n', 9)]);
    expect(s.bottom, isFalse);
    final sw = Stopwatch()..start();
    expect(s.assume(isTerm('n', 4), true, none).bottom, isTrue);
    expect(s.assume(isTerm('n', 999999999997), true, none).bottom, isFalse);
    expect(sw.elapsed.inSeconds, lessThan(5), reason: 'took ${sw.elapsed}');
  });

  test('constraints that share no name are searched apart', () {
    // Each of `a`, `b` and `c` has 10^6 values and a set of 4·10^5; searched together the
    // box would have 10^18 points, apart each search is a halving.
    final ts = [productMod10('a', 'a', 9), productMod10('b', 'b', 9), productMod10('c', 'c', 9)];
    const r = 1000000;
    final s = written(within([('a', 0, r), ('b', 0, r), ('c', 0, r)], true), ts);
    expect(s.bottom, isFalse);
    expect(s.exactly.length, 3);
    expect(s.assume(isTerm('b', 4), true, none).bottom, isTrue);
  });

  test('a witness still within the bounds is kept', () {
    final s = written(within([('n', 0, 30)], true), [productMod10('n', 'n', 9)]);
    final w = s.exactly.values.first;
    // Narrowing to a range that keeps the witness keeps it; one that drops it finds another.
    final v = w['n']!;
    final keep = s.assume(prim(Prim.ge, [const Var('n'), lit(v)]), true, none);
    expect(keep.exactly.values.first, equals(w));
    final drop = s.assume(prim(Prim.gt, [const Var('n'), lit(v)]), true, none);
    expect(drop.bottom, isFalse);
    final w2 = drop.exactly.values.first['n']!;
    expect(w2 > v && (w2 * w2) % 10 == 9, isTrue, reason: '$w2');
  });
}
