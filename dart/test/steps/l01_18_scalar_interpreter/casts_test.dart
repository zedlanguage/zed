/// The checked casts: `T(x)` is `x` as a `T` when it is the same number, `#inexact` when a
/// number has no equal `T`, and `#invalid` when the source is not a `T` at all.
library;

import 'package:test/test.dart';

import '../l01_16_elaboration/elab.dart' show errors;
import 'scalar.dart';

void main() {
  test('reading a quantity from a form field', () {
    expect(x('int("42")'), '42');
    expect(x('int("-7")'), '-7');
    expect(x('int("4 2")'), '#invalid');
    expect(x('int("")'), '#invalid');
    expect(x('int("+5")'), '#invalid', reason: 'a sign is only `-`, as `String` writes it');
    expect(x('int("twelve") else 1'), '1');
    expect(x('int("123456789012345678901234567890")'), '123456789012345678901234567890');
  });

  test('a float to `int` must be whole', () {
    expect(x('int(3.0)'), '3');
    expect(x('int(-2.5)'), '#inexact');
    expect(x('int(1.0e20)'), '100000000000000000000');
    expect(x('int(1.0 / 0.0)'), '#invalid');
    expect(x('int(0.0 / 0.0)'), '#invalid');
    expect(x('int(7r/2r)'), '#inexact');
    expect(x('int(rat(6) / rat(2))'), '3');
  });

  test('a float is an exact rational', () {
    expect(x('rat(0.5)'), '1r/2r');
    expect(x('rat(0.1)'), '3602879701896397r/36028797018963968r');
    expect(x('rat(-3)'), '-3r');
    expect(x('rat(1.0 / 0.0)'), '#invalid');
  });

  test('a rational reads as `String` writes it, or as a decimal', () {
    expect(x('rat("1r/3r")'), '1r/3r');
    expect(x('rat("2/4")'), '1r/2r');
    expect(x('rat("3r")'), '3r');
    expect(x('rat("0.25")'), '1r/4r');
    expect(x('rat("1/0")'), '#invalid');
    expect(x('rat(".5")'), '#invalid');
    expect(x('rat(String(5r/7r)) == 5r/7r'), 'true');
  });

  test('a number to `f64` must be exactly representable', () {
    expect(x('f64(3)'), '3.0');
    expect(
      x('f64(2 ** 60)'),
      '1152921504606847000.0',
      reason: 'the shortest digits that read back',
    );
    expect(x('f64(2 ** 60 + 1)'), '#inexact', reason: '2^60 + 1 needs 61 bits');
    expect(x('f64(3r/8r)'), '0.375');
    expect(x('f64(1r/3r)'), '#inexact');
    expect(x('f64(rat(1) / rat(2 ** 1074))'), '5.0e-324');
    expect(x('f64(rat(1) / rat(2 ** 1075))'), '#inexact');
  });

  test('a float reads correctly rounded, and overflow is inexact', () {
    expect(x('f64("0.1") == 0.1'), 'true');
    expect(x('f64("2.5e-3")'), '0.0025');
    expect(x('f64("7")'), '7.0');
    expect(x('f64("1e400")'), '#inexact');
    expect(x('f64("-1e400")'), '#inexact');
    expect(x('f64("1,5")'), '#invalid');
    expect(x('f64("infinity")'), '#invalid');
    expect(x('f64("1e")'), '#invalid');
  });

  test('a cast of a kind it does not take is a type error', () {
    expect(errors('x = int(true);\n'), ['`int` does not take (true) [int(true)]']);
    expect(errors('x = len(3);\n'), ['`len` does not take (3) [len(3)]']);
  });
}
