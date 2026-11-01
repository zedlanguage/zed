/// A bare numeric literal adopts the carrier its context expects, exactly or not at all: an
/// integer literal adopts int, f64 or rat; a float literal adopts f64 or rat, never int; a
/// decorated literal such as `1r` keeps its own carrier.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../l01_16_elaboration/elab.dart';
import 'support.dart';

/// The values the literals of `text` adopt, sorted by position.
List<Value> adopted(String text) => [
  for (final e in info(
    text,
  ).adopt.entries.toList()..sort((a, b) => a.key.start.compareTo(b.key.start)))
    e.value,
];

void main() {
  test("an integer literal adopts the other operand's carrier", () {
    expect(adopted('x = 0.1 + 1;\n'), [Float(1.0)]);
    expect(adopted('x = 2 ** 0.5;\n'), [Float(2.0)]);
    expect(value('x = 0.1 + 1;\n', 'x'), '1.1');
    expect(value('x = 1r / 4r + 1;\n', 'x'), '5r/4r');
  });

  test("a literal adopts a parameter's carrier", () {
    expect(value('f(positional x: f64) = x / 4.0;\ny = f(2);\n', 'y'), '0.5');
    // Within the body too: `2` is an f64 in `half`.
    expect(value('half(x) = x / 2;\ny = half(x: 3.0);\n', 'y'), '1.5');
  });

  test('a literal that cannot adopt exactly is an error', () {
    expect(typeErrors('f(positional x: f64) = x;\ny = f(9007199254740993);\n'), [
      '`9007199254740993` is not an f64 [9007199254740993]',
    ]);
  });

  test('a float literal never adopts int', () {
    expect(typeErrors('f(positional x: int) = x;\ny = f(2.0);\n'), [
      '`f` does not take (2.0) [f(2.0)]',
    ]);
    expect(typeErrors('x = 7 div 2.0;\n'), ['`div` does not take (7, 2.0) [7 div 2.0]']);
  });

  test('a decorated literal keeps its carrier', () {
    // The integer literal adopts rat; `1r` itself adopts nothing.
    expect(adopted('x = 1r + 1;\n'), hasLength(1));
    expect(adopted('x = 1r + 2r;\n'), isEmpty);
    expect(value('x = 1r + 1;\n', 'x'), '2r');
    expect(value('y = 0.1 + 1r;\n', 'y'), '11r/10r');
  });

  test('equality compares across carriers', () {
    // A divisor that cannot be zero adds no `#divByZero`, so the quotient passes as a rat.
    expect(typeErrors('f(positional x: rat) = x;\ny = f(3r/2r);\n'), isEmpty);
    // A divisor that may be zero adds `#divByZero`, a loose atom, which passes through `f`.
    expect(typeErrors('f(positional x: int) = x;\ny = f(7 div 0);\n'), isEmpty);
    expect(value('f(positional x: int) = x;\ny = f(7 div 0);\n', 'y'), '#divByZero');
    expect(value('y = 1 == 1r;\n', 'y'), 'true');
    expect(value('y = 1.5 == 3r/2r;\n', 'y'), 'true');
  });

  test('a body keeps the arrows with the fewest adoptions', () {
    // `x * 2` checks at int with no adoption, so the f64 and rat arrows, which adopt `2`,
    // are not kept, and a test row at a float is an error.
    expect(typeErrors('f(positional x) = x * 2\ntest {\n  3 -> 6,\n  1.5 -> 3.0,\n}\n'), [
      '`f` does not take (1.5) [1.5]',
    ]);
  });
}
