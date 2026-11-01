/// An `is` test narrows the name it tests: to the tested type where it holds, and to the
/// rest where it does not, through `not`, `&&` and `||`.
library;

import 'package:test/test.dart';

import '../l01_16_elaboration/elab.dart';
import 'support.dart';

const n = 'n(x: int | String) = if x is String { len(x) } else { x * 2 };\n';

void main() {
  test('each branch sees its part of the union', () {
    expect(sig(n, 'n'), '(x: int | String) -> int');
    expect(value('${n}y = n(x: "ab");\n', 'y'), '2');
    expect(value('${n}y = n(x: 5);\n', 'y'), '10');
  });

  test('not swaps the branches', () {
    expect(
      typeErrors('n(x: int | String) = if x is not String { x * 2 } else { len(x) };\n'),
      isEmpty,
    );
  });

  test('and narrows where both hold, and or where both fail', () {
    expect(
      typeErrors(
        'n(x: int | String, y: int | String) = if x is int && y is int { x + y } else { 0 };\n',
      ),
      isEmpty,
    );
    expect(
      typeErrors(
        'n(x: int | String, y: int | String) = '
        'if x is String || y is String { 0 } else { x + y };\n',
      ),
      isEmpty,
    );
  });

  test("the right operand sees the left one's narrowing", () {
    expect(typeErrors('long(x: int | String) = x is String && len(x) > 2;\n'), isEmpty);
    expect(typeErrors('short(x: int | String) = x is int || len(x) < 2;\n'), isEmpty);
    expect(typeErrors('long(x: int | String) = x is int && len(x) > 2;\n'), [
      '`len` does not take (int) [len(x)]',
    ]);
  });

  test('without a test the whole union must fit', () {
    expect(typeErrors('n(x: int | String) = x * 2;\n'), ['`*` does not take (String, 2) [x * 2]']);
    // The narrowed branch is checked as the narrowed type.
    expect(typeErrors('n(x) = if x is String { x + 1 } else { 0 };\n'), [
      '`+` does not take (String, 1) [x + 1]',
    ]);
  });

  test('a condition must be bool', () {
    expect(typeErrors('c = if 1 { 2 } else { 3 };\n'), [
      'the condition of `if` is 1, not bool [1]',
    ]);
  });
}
