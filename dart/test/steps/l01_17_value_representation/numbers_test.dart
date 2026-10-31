/// Unbounded integers and exact rationals, from literals through arithmetic.
library;

import 'package:test/test.dart';

import '../l01_16_elaboration/elab.dart';

void main() {
  test('integers widen past 64 bits and narrow back', () {
    var src =
        'max = 9223372036854775807;\nnext = max + 1;\nback = next - 1;\n'
        'same = back == max;\ngoogol = 10 ** 100;\n';
    expect(value(src, 'next'), '9223372036854775808');
    expect(value(src, 'same'), 'true');
    expect(value(src, 'googol'), '1${'0' * 100}', reason: '`**` past 64 bits');
    // The most negative machine integer is a literal past 64 bits, negated.
    src = 'lo = -9223372036854775808;\nn = lo - 1;\n';
    expect(value(src, 'lo'), '-9223372036854775808');
    expect(value(src, 'n'), '-9223372036854775809');
  });

  test('big literals in any base and Euclidean division', () {
    const src =
        'mask = 0xffff_ffff_ffff_ffff_ffff;\n'
        'bits = 0b1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;\n'
        'q = -100000000000000000000 div 7;\nr = -100000000000000000000 mod 7;\n'
        'check = q * 7 + r;\nz = 100000000000000000000 div 0;\n';
    expect(value(src, 'mask'), '1208925819614629174706175');
    expect(value(src, 'bits'), '18446744073709551616');
    expect(value(src, 'q'), '-14285714285714285715');
    expect(value(src, 'r'), '5', reason: 'a Euclidean remainder is never negative');
    expect(value(src, 'check'), '-100000000000000000000');
    expect(value(src, 'z'), '#divByZero');
  });

  test('powers of zero, one and minus one stay small', () {
    const src =
        'a = 1 ** 100000000000000000000;\nb = (-1) ** 100000000000000000001;\n'
        'c = 0 ** 100000000000000000000;\nd = 7 ** 0;\n';
    expect(value(src, 'a'), '1');
    expect(value(src, 'b'), '-1');
    expect(value(src, 'c'), '0');
    expect(value(src, 'd'), '1');
  });

  test('a number past the size limit is an evaluator error', () {
    expect(
      value('huge = 3 ** 10000000;\n', 'huge'),
      "error: a number beyond the evaluator's size limit",
    );
    expect(errors('x = 1e999999r;\n'), [
      "this rational is beyond the evaluator's size limit [1e999999r]",
    ]);
  });

  test('rationals are exact', () {
    const src =
        'tenth = 0.1r;\nexact = tenth + 0.2r == 0.3r;\nfloaty = 0.1 + 0.2 == 0.3;\n'
        'third = 1r / 3r;\nwhole = third + third + third;\nneg = -third * 2r;\n'
        'fee = 2.5e-3r;\nbig = 1e30r / 7r;\n';
    expect(value(src, 'exact'), 'true');
    expect(value(src, 'floaty'), 'false');
    expect(value(src, 'third'), '1r/3r');
    expect(value(src, 'whole'), '1r');
    expect(value(src, 'neg'), '-2r/3r');
    expect(value(src, 'fee'), '1r/400r');
    expect(value(src, 'big'), '1000000000000000000000000000000r/7r');
    expect(term(src, 'third'), '(1r / 3r)');
  });

  test('rational division by zero is an atom', () {
    const src =
        'share(positional total, positional n) = total / n;\n'
        'a = share(10r, 4r);\nb = share(10r, 0r);\nc = share(10r, 0r) else 0r;\n';
    expect(value(src, 'a'), '5r/2r');
    expect(value(src, 'b'), '#divByZero');
    expect(value(src, 'c'), '0r');
  });

  test('numbers of different kinds do not mix', () {
    expect(value('a = 1r + 1;\n', 'a'), 'error: type error: Add applied to 1r, 1');
    expect(value('b = 1r < 2.0;\n', 'b'), 'error: type error: Lt applied to 1r, 2.0');
    // `==` across kinds is false: the values differ, though their order ties them by value.
    expect(value('c = 1 == 1.0;\n', 'c'), 'false');
  });
}
