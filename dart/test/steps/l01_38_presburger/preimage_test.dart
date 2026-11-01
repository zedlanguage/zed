/// The linear stage of the preimage: the z3 fixtures, and the relation kept where the preimage
/// is not a box.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import '../l01_25_preimage_catalog/support.dart';

/// The preimage of `true` under `ok` in `src` over `ds`, printed, with the relation kept.
String pre(String src, List<Dom> ds) {
  final p = preimage(function(src).$2, doms(ds), const BoolDemand(true));
  return p.relation == null ? shown(p) : '${shown(p)}; relation ${p.relation}';
}

void main() {
  test('the z3 fixture reproduces exactly', () {
    expect(pre('ok(x) = (x * 2 + 1) < 100;', [('x', 0, 100)]), 'x [0..=49]; exact');
    // A sum the catalog projects only as necessary, which the relation makes exact: `x + x mod
    // 5 < 50` holds for `x` in `[0..=47]` exactly.
    expect(pre('ok(x) = x + x mod 5 < 50;', [('x', 0, 1000000)]), 'x [0..=47]; exact');
    // A congruence the projection does not split is kept as a relation; the set is necessary
    // only.
    expect(
      pre('ok(x) = (x * 2 + 1) < 100 && x mod 7 != 3;', [('x', 0, 1000000)]),
      'x [0..=2, 4..=49]; necessary; relation 2 * x <= 98 && !(q1 == 3) where q0 = x div 7, '
      'q1 = x mod 7',
    );
  });

  test('a relation among two inputs is kept with its projection', () {
    // The design's example: `(a + b).refine(v -> v < 50)` needs `a + b <= 49`.
    expect(
      pre('ok(a, b) = a + b < 50;', [('a', 0, 1000), ('b', 0, 1000)]),
      'a [0..=49]; b [0..=49]; necessary; relation a + b <= 49',
    );
    // Over three inputs, the relation alone says what the box misses.
    expect(
      pre('ok(a, b, c) = a + b + c < 50;', [('a', 0, 1000), ('b', 0, 1000), ('c', 0, 1000)]),
      'a [0..=49]; b [0..=49]; c [0..=49]; necessary; relation a + b + c <= 49',
    );
    // The next index: `i <= n - 2`, with `i` and `n` narrowed to what it allows.
    expect(
      pre('ok(i, n) = 0 <= i + 1 && i + 1 < n;', [('i', 0, null), ('n', 0, 100000)]),
      'i [0..=99998]; n [2..=100000]; necessary; relation i >= -1 && i <= n - 2',
    );
  });

  test('a relation the box entails makes the preimage exact', () {
    // `x - y` over boxes where the catalog's projection is the whole answer once tested.
    expect(
      pre('ok(x, y) = x - y >= 0;', [('x', 10, 20000), ('y', 0, 5)]),
      'x [10..=20000]; y [0..=5]; exact',
    );
    // No point at all: the empty preimage is exact.
    expect(
      pre('ok(x, y) = x < y && y < x;', [('x', null, null), ('y', null, null)]),
      'x []; y []; exact',
    );
  });
}
