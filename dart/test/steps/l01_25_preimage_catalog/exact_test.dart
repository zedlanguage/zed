/// `@exact`: the projection of the points that meet the demand, by branch and prune
/// (docs/thresholds.md, "`@exact`"), against the ordinary preimage of the same term.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

import 'support.dart';

/// The ordinary preimage of `true` under `src` over `ds`, and the one under `@exact` with
/// `classes`.
(String, String) both(String src, List<Dom> ds, Classes classes) {
  final body = function(src).$2;
  final d = doms(ds);
  const t = BoolDemand(true);
  return (shown(preimage(body, d, t)), shown(exactPreimage(body, d, classes, t)));
}

void main() {
  test('exact preimages of ranges', () {
    final cases = <(String, List<Dom>, String, String)>[
      (
        'ok(x) = x * x mod 10 == 9;\n',
        [('x', 0, 30)],
        'x [3..=3, 5..=29]; necessary',
        'x [3..=3, 7..=7, 13..=13, 17..=17, 23..=23, 27..=27]; exact; enumerated',
      ),
      (
        // `x * 7` in `[3..=3, 13..=203]`, so `x` in `[2..=29]`; the linear relations of step
        // L1.38 narrow it to the hull of `7 * x = 10 * q + 3`, `[9..=29]`.
        'ok(x) = x * 7 mod 10 == 3;\n',
        [('x', 0, 30)],
        'x [2..=29]; necessary',
        'x [9..=9, 19..=19, 29..=29]; exact; enumerated',
      ),
      (
        // Every `x` and every `y` in 1..=6 has a partner, but not every pair meets it.
        'ok(x, y) = x * y mod 7 == 3;\n',
        [('x', 1, 6), ('y', 1, 6)],
        'x [1..=6]; y [1..=6]; necessary',
        'x [1..=6]; y [1..=6]; necessary; enumerated',
      ),
      (
        // An unbounded input is not searched.
        'ok(x) = x * x mod 10 == 9;\n',
        [('x', 0, null)],
        'x [0..]; necessary',
        'x [0..]; necessary',
      ),
    ];
    for (final (src, ds, plain, exact) in cases) {
      expect(both(src, ds, {}), (plain, exact), reason: src);
    }
  });

  test('an exact preimage searches only the members of each class', () {
    // Of 3, 7, 13, 17, 23 and 27, only 13 and 17 are 1 mod 4.
    final (_, exact) = both(
      'ok(x) = x * x mod 10 == 9;\n',
      [('x', 0, 30)],
      {'x': Congruence(4, 1)},
    );
    expect(exact, 'x [13..=13, 17..=17]; exact; enumerated');
  });

  test('a witness is the first point found or none', () {
    const t = BoolDemand(true);
    final body = function('ok(x) = x * x mod 10 == 9;\n').$2;
    ({Point? point})? w(int? lo, int? hi, Classes c) => witness(body, doms([('x', lo, hi)]), c, t);
    // A point that meets the term, in a range of 10^15 points.
    const top = 1000000000000000;
    final found = w(0, top, {})!.point!;
    final x = found['x']!;
    expect((x * x) % 10 == 9 && 0 <= x && x <= top, isTrue, reason: '$x');
    // None at all: `x * x` never ends in 9 when `x` ends in 5.
    final five = {'x': Congruence(10, 5)};
    expect(w(0, 1000000, five), (point: null));
    // Unbounded: not searched.
    expect(w(0, null, {}), isNull);
  });

  test('the classes alone decide a box of any size', () {
    // With `x` in `5 mod 10`, `x * x mod 10` is 5 at every point, so the arithmetic of the
    // classes shows no point meets `== 9` and every point meets `!= 9`, over 10^15 points.
    const t = BoolDemand(true);
    final five = {'x': Congruence(10, 5)};
    final d = doms([('x', 0, 1000000000000000)]);
    final no = function('ok(x) = x * x mod 10 == 9;\n').$2;
    final yes = function('ok(x) = x * x mod 10 != 9;\n').$2;
    final sw = Stopwatch()..start();
    expect(witness(no, d, five, t), (point: null));
    expect(witness(yes, d, five, t)!.point!['x'], 5);
    expect(sw.elapsed.inSeconds, lessThan(1), reason: 'took ${sw.elapsed}');
  });
}
