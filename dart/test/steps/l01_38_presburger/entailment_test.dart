/// Rung 2 on the facts the design names, written as Zed functions over the same parameters.
library;

import 'package:test/test.dart';
import 'package:zed/presburger.dart';

import '../l01_25_preimage_catalog/support.dart' show function;
import 'support.dart';

/// What rung 2 concludes from the body of `ok` in `premise` to the body of `ok` in `goal`.
Entailment rung2(String premise, String goal) => entails(relation(premise).$2, relation(goal).$2);

const goal = 'ok(y, w, x, h) = y * w + x < h * w;';

void main() {
  test('a row-major index is in bounds from the bounds on its factors', () {
    final e = rung2('ok(y, w, x, h) = 0 <= y && y < h && 0 <= x && x < w;', goal);
    if (e is! Proved) fail('not proved: $e');
    // The certificate holds the premises and the product `(h - 1 - y)·w >= 0` of the premises
    // on `y` and `w`, as `h * w - w * y - w >= 0`: the step the linear test cannot take alone.
    final shown = [for (final f in e.premises) '$f'];
    expect(shown[0], 'y >= 0 && h >= y + 1 && x >= 0 && w >= x + 1');
    expect(shown, contains('h + w + w * y <= y + h * w + 1'));
  });

  test('the same goal from y at most h is refuted with a countermodel', () {
    const premise = 'ok(y, w, x, h) = 0 <= y && y <= h && 0 <= x && x < w;';
    final e = rung2(premise, goal);
    expect('$e', 'refuted: countermodel h = 0, w = 1, x = 0, y = 0');
    // The countermodel is one: the interpreter runs both functions there.
    final (ps, p) = function(premise);
    final (_, g) = function(goal);
    final q = point((e as Refuted).model, ps);
    expect(holds(p, ps, q) && !holds(g, ps, q), isTrue, reason: '$q');
  });

  test('a product is bounded only through the premises on its factors', () {
    // The product of the premises `y >= 0` and `w >= 0`.
    final e = rung2('ok(y, w, x, h) = 0 <= y && 0 <= w;', 'ok(y, w, x, h) = 0 <= y * w;');
    expect(e, isA<Proved>(), reason: '$e');
    // With no premise on `w`, nothing bounds `h * w - w * y`: the linear reading fails at a
    // point whose product atoms are not the products, so the goal is not proved, and not
    // refuted either (it is false at `w = -1`, which rung 2 does not search for).
    expect(
      '${rung2('ok(y, w, x, h) = y <= h;', 'ok(y, w, x, h) = y * w <= h * w;')}',
      'not proved: the linear reading fails at h = 0, h * w = -1',
    );
  });

  test('the next index is not in bounds from the current one', () {
    // The z3 fixture for `xs[i + 1]`, before L3 brings lists: from `0 <= i < n` the next index
    // can be `n`, at `n = 1, i = 0`.
    expect(
      '${rung2('ok(i, n) = 0 <= i && i < n;', 'ok(i, n) = 0 <= i + 1 && i + 1 < n;')}',
      'refuted: countermodel i = 0, n = 1',
    );
    // From `0 <= i < n - 1` it is.
    final e = rung2('ok(i, n) = 0 <= i && i < n - 1;', 'ok(i, n) = 0 <= i + 1 && i + 1 < n;');
    expect(e, isA<Proved>(), reason: '$e');
  });

  test('contradictory premises entail anything', () {
    final e = rung2('ok(x, y) = x < y && y < x;', 'ok(x, y) = x == y + 7;');
    expect(e, isA<Proved>(), reason: '$e');
  });

  test('Euclidean division and remainder are stated exactly', () {
    // `x mod 4` is in `[0..=3]` for every `x`, negative ones included, and `x div 4 * 4 + x mod
    // 4` is `x`.
    for (final goal in [
      'ok(x) = 0 <= x mod 4 && x mod 4 <= 3;',
      'ok(x) = x div 4 * 4 + x mod 4 == x;',
      'ok(x) = x mod -4 >= 0;',
    ]) {
      final e = rung2('ok(x) = true;', goal);
      expect(e, isA<Proved>(), reason: '$goal: $e');
    }
    // `x mod 4 == 3` does not follow from `x` odd: `x = 1` is a countermodel.
    expect(
      '${rung2('ok(x) = x mod 2 == 1;', 'ok(x) = x mod 4 == 3;')}',
      'refuted: countermodel x = 1',
    );
  });

  test('abs and branches are stated through their cases', () {
    // `min` and `max` are kernel primitives with no surface word; the random terms of `random`
    // take them.
    for (final (premise, goal) in [
      ('ok(a, b) = true;', 'ok(a, b) = abs(a - b) >= 0;'),
      ('ok(a, b) = a < 0;', 'ok(a, b) = abs(a) == -a;'),
      ('ok(a, b) = true;', 'ok(a, b) = (if a < b { b - a } else { a - b }) == abs(a - b);'),
    ]) {
      final e = rung2(premise, goal);
      expect(e, isA<Proved>(), reason: '$goal: $e');
    }
    expect(
      '${rung2('ok(a, b) = true;', 'ok(a, b) = abs(a) == a;')}',
      'refuted: countermodel a = -1',
    );
  });
}
