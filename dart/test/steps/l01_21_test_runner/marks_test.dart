/// The `// ✗` marks: a unit's expected diagnostics.
library;

import 'package:test/test.dart';

import 'runner.dart';

const rebound = 'f(x) {\n  y = x + 1;\n  y = y * 2;  // ✗ rebinding in the same scope\n  y\n}\n';

void main() {
  test('a diagnostic on a marked line passes', () {
    expect(checks(rebound), ['3:3: ok']);
  });

  test('a diagnostic off the marked line fails, and so does the mark', () {
    final src = rebound
        .replaceFirst('  // ✗ rebinding in the same scope', '')
        .replaceFirst('  y\n}', '  y  // ✗\n}');
    final got = checks(src);
    expect(got, hasLength(2));
    expect(got[0], startsWith('3:3: `y` is already bound in this scope'));
    expect(got[1], '4:1: the line is marked ✗ and has no diagnostic');
  });

  test('a mark in an accepted unit fails', () {
    expect(checks('f(x) = x + 1;  // ✗ claimed to be rejected\n'), [
      '1:1: the line is marked ✗ and the unit is accepted',
    ]);
  });

  test('a commented variant is no mark, and a rejected unit runs no row', () {
    const src =
        '// y = 2;  ✗ a variant, checked by its own fixture\n'
        'f(x) = x * 2 test { 1 -> 3 }\n'
        'g(x) {\n  y = 1;\n  y = 2;  // ✗\n  y\n}\n';
    expect(checks(src), ['5:3: ok']);
    expect(checks(src.replaceFirst('y = 2;  // ✗', 'z = 2;')), [
      '2:21: `1 -> 3` of `f`: the result is 2',
    ]);
  });

  test('a marked line is placed at its first diagnostic, and others stay failures', () {
    const src = 'a = 1;\nb = missing1 + missing2;  // ✗\nc = missing3;\nd = missing4;  // ✗\n';
    final got = checks(src);
    expect(got, hasLength(3));
    expect(got[0], '2:5: ok');
    expect(got[1], startsWith('3:5: `missing3` is not defined'));
    expect(got[2], '4:5: ok');
  });
}
