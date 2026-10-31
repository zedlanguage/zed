/// The language's `==`: IEEE 754 at floats, at any depth, and structural elsewhere; and on
/// functions, an error until types give the domain to compare them on.
library;

import 'dart:typed_data';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../l01_16_elaboration/elab.dart';

/// The bits of `x`.
int bits(double x) => (ByteData(8)..setFloat64(0, x)).getUint64(0);

void main() {
  test('float equality and comparison follow IEEE', () {
    const src =
        'nan = 0.0 / 0.0;\na = nan == nan;\nb = nan != nan;\nc = 0.0 == -0.0;\n'
        'd = nan < 1.0;\ne = nan >= 1.0;\nf = -0.0 < 0.0;\ng = 1.0 <= 1.0;\n';
    expect(value(src, 'a'), 'false');
    expect(value(src, 'b'), 'true');
    expect(value(src, 'c'), 'true');
    expect(value(src, 'd'), 'false');
    expect(value(src, 'e'), 'false');
    expect(value(src, 'f'), 'false');
    expect(value(src, 'g'), 'true');
  });

  test('IEEE equality reaches inside tuples and atoms', () {
    const src =
        'nan = 0.0 / 0.0;\na = (1, nan) == (1, nan);\nb = (0.0, "x") == (-0.0, "x");\n'
        'c = #at(-0.0) == #at(0.0);\nd = #at(x: nan) == #at(x: nan);\n';
    expect(value(src, 'a'), 'false');
    expect(value(src, 'b'), 'true');
    expect(value(src, 'c'), 'true');
    expect(value(src, 'd'), 'false');
  });

  test('keys still tell signed zeros apart and read one NaN', () {
    // The identity keys and the law catalog read is bitwise (sec:keys), whatever `==` says.
    expect(Float(0.0), isNot(Float(-0.0)));
    expect(Float(double.nan), Float(-double.nan));
    expect(Float(0.0).surfaceEq(Float(double.nan)), isFalse);
    expect(bits(Float(-double.nan).x), bits(double.nan));
  });

  test('functions compare only over an enumerable domain', () {
    const src = 'inc = x -> x + 1;\nalso = x -> 1 + x;\nsame = inc == also;\n';
    expect(
      value(src, 'same'),
      contains('`==` on functions compares them at every point of an enumerable domain'),
    );
  });
}
