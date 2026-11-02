/// The design's examples (DESIGN.md Part G, step L1.39).
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart' hide Lattice;
import 'package:zed/query.dart' show Db;
import 'package:zed/store.dart';

import 'support.dart';

/// The front end accepts `src` with no diagnostic.
void accepted(String src) => Db().front(src);

void main() {
  test('an arm that fixes n mod 4 == 1 within 0 to 10 holds 1 to 9', () {
    const src = 'ok = (n) -> if n >= 0 && n <= 10 && n mod 4 == 1 { n } else { 0 };';
    accepted(src);
    final (_, _, a) = armsOf(src);
    final n = arm(a, '((n mod 4) == 1)', true).scope.get('n');
    // The hull is `int[1..=9]`, and the congruence keeps the members exactly: 1, 5 and 9.
    expect('${n.ints.hull()}', '[1..=9]');
    expect('${n.cell.congruence.element}', '1 mod 4');
    // The other arm loses the two ends; 5 is not listed, so it is kept.
    final other = arm(a, '((n mod 4) == 1)', false).scope.get('n');
    expect('${other.ints}', '[..=0, 2..=8, 10..]');
  });

  test('an arm no value reaches is unreachable and the program is accepted', () {
    const src = 'ok = (n) -> if n >= 2 && n <= 4 && n mod 4 == 1 { n } else { 0 };';
    accepted(src);
    final (_, _, a) = armsOf(src);
    final then = arm(a, '((n mod 4) == 1)', true);
    expect(then.reachable, isFalse);
    expect('${then.scope}', 'unreachable\n');
    // The other arm is reached by every integer.
    final other = arm(a, '((n mod 4) == 1)', false);
    expect(other.reachable, isTrue);
    expect('${other.scope.get('n')}', 'ints [..]\ntype int\n');
  });

  test('a binding read from a static if is static', () {
    const src = 'debug = false;\nmode = if debug { 1 } else { 2 };';
    accepted(src);
    final t = binding(src, 'mode');
    final a = arms(t, Scope([]));
    expect(a, hasLength(2));
    expect(arm(a, 'debug', true).reachable, isFalse);
    expect(
      '${arm(a, 'debug', false).scope}',
      'debug:\n  finite {false}\n  type false\n  time build\n',
    );
    expect(
      '${Scope([]).forward(t)}',
      'ints [2..=2]\ncongruence 2\nfinite {2}\ntype 2\ntime build\n',
    );
  });

  test('a negated equality excludes the literal by complement', () {
    // Types, intervals and finite sets are exact, so `!=` removes the one value from each.
    const src = 'ok = (n) -> if n >= 0 && n <= 3 { if n != 2 { n } else { 0 } } else { 0 };';
    accepted(src);
    final (_, _, a) = armsOf(src);
    final n = arm(a, '(n != 2)', true).scope.get('n');
    expect('${n.ints}', '[0..=1, 3..=3]');
    expect('$n'.split('\n')[1], 'finite {0, 1, 3}');
    expect(arm(a, '(n != 2)', false).scope.get('n').value, const Int(2));
  });

  test('a relation between two names bounds each', () {
    // `x < y` and `y <= 5` with `x >= 3` leave `x` in `3..=4` and `y` in `4..=5`.
    const src = 'ok = (x, y) -> if x >= 3 && x < y && y <= 5 { x + y } else { 0 };';
    accepted(src);
    final (_, _, a) = armsOf(src);
    final s = arm(a, '(y <= 5)', true).scope;
    expect('${s.get('x').ints}', '[3..=4]');
    expect('${s.get('y').ints}', '[4..=5]');
    expect('$s', contains('relation '));
  });

  test('a meet takes the earlier binding time and a join the later', () {
    expect(Time.build.meet(Time.run), Time.build);
    expect(Time.build.join(Time.run), Time.run);
    expect(Time.values.first, Time.never);
    // A binding computed from a parameter is known only when the program runs.
    final (_, _, a) = armsOf('ok = (n) -> { k = n + 1; if k > 0 { k } else { 0 } };');
    final k = arm(a, '(k > 0)', true).scope.get('k');
    expect(k.time.element, Time.run);
    expect('${k.ints}', '[1..]');
  });

  test('a join keeps the affine relation of its sides', () {
    // Each side fixes `i` to one value, so `i + j == n` holds on both; the join keeps it.
    const src =
        'ok = (i, j, n) -> if (i == 0 && j == n) || (i == 1 && j == n - 1) '
        '{ if i + j != n { 1 } else { 2 } } else { 0 };';
    accepted(src);
    final (_, _, a) = armsOf(src);
    expect(arm(a, '((i + j) != n)', true).reachable, isFalse);
    expect(arm(a, '((i + j) != n)', false).reachable, isTrue);
  });
}
