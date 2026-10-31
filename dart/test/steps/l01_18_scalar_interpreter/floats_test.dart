/// How `String` writes a float, and the round trip `f64(String(x)) == x`, bit for bit.
library;

import 'dart:typed_data';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import 'scalar.dart';

/// The bits of `x`.
int bitsOf(double x) => (ByteData(8)..setFloat64(0, x)).getUint64(0);

/// The float of the bits `b`.
double ofBits(int b) => (ByteData(8)..setUint64(0, b)).getFloat64(0);

/// `f64(String(x))` by the kernel's own primitives.
Value roundTrip(double v) => eval(
  prim(Prim.castF64, [
    prim(Prim.show, [lit(Float(v))]),
  ]),
);

void main() {
  test('a receipt prints floats in their shortest form', () {
    expect(x('String(0.1 + 0.2)'), '"0.30000000000000004"');
    expect(x(r'"total: ${19.99 * 3.0}"'), '"total: 59.97"');
    expect(x('String(2.0)'), '"2.0"', reason: 'a whole float keeps its point');
    expect(x('String(-0.0)'), '"-0.0"');
  });

  test('fixed notation runs from one millionth to below ten to the 21', () {
    const cases = [
      ('0.000001', '0.000001'),
      ('0.0000001', '1.0e-7'),
      ('123456789012345678901.0', '123456789012345680000.0'),
      ('1.0e21', '1.0e21'),
      ('6.02214076e23', '6.02214076e23'),
      ('5.0e-324', '5.0e-324'),
    ];
    for (final (lit, want) in cases) {
      expect(x('String($lit)'), '"$want"', reason: lit);
    }
  });

  test('infinities and NaN have names', () {
    expect(x('String(1.0 / 0.0)'), '"inf"');
    expect(x('String(-1.0 / 0.0)'), '"-inf"');
    expect(x('String(0.0 / 0.0)'), '"nan"');
    expect(x('f64("-inf") < 0.0'), 'true');
    expect(x('f64("nan") == f64("nan")'), 'false', reason: 'NaN is not == itself');
  });

  test('every float reads back to itself', () {
    final edges = <double>[
      0.0,
      -0.0,
      ofBits(0x0010000000000000),
      ofBits(0x0010000000000000) / 3.0,
      ofBits(1),
      double.maxFinite,
      -double.maxFinite,
      ofBits(0x3cb0000000000000),
      1e21,
      1e-7,
      123456.789,
      double.infinity,
      double.negativeInfinity,
    ];
    // A fixed linear congruential sequence of bit patterns, every exponent among them.
    var state = 0x2545f4914f6cdd1d;
    for (var i = 0; i < 20000; i++) {
      state = state * 6364136223846793005 + 1442695040888963407;
      final v = ofBits(state);
      if (!v.isNaN) edges.add(v);
    }
    for (final v in edges) {
      final back = roundTrip(v);
      expect(back, isA<Float>(), reason: '$v read back as $back');
      expect(bitsOf((back as Float).x), bitsOf(v), reason: '$v');
    }
    expect(switch (roundTrip(double.nan)) {
      Float(:final x) => x.isNaN,
      _ => false,
    }, isTrue);
  });
}
