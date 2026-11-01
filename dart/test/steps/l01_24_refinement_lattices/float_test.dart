/// Float classes, against the floats they hold.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

/// Floats of every kind and of each narrowest width.
const samples = [
  0.0,
  -0.0,
  1.5,
  -65504.0,
  65505.0,
  5.960464477539063e-8, // 2^-24, the least f16 subnormal
  2.9802322387695312e-8, // 2^-25, an f32 and not an f16
  1e10,
  0.1,
  double.maxFinite,
  2.2250738585072014e-308, // the least positive normal f64
  double.infinity,
  double.negativeInfinity,
  double.nan,
];

/// Every class: each set of kinds at each width.
List<FloatClass> classes() => [
  for (var mask = 0; mask < 16; mask++)
    for (final w in Width.values)
      FloatClass([
        for (var i = 0; i < 4; i++)
          if (mask & (1 << i) != 0) Kind.values[i],
      ], w),
];

/// Whether every sample in `a` is in `b`, and `a`'s width is within `b`'s.
bool allIn(FloatClass a, FloatClass b) =>
    samples.every((x) => !a.contains(x) || b.contains(x)) && a.join(b) == b;

void main() {
  test('each float has its narrowest width', () {
    const want = [
      Width.f16, Width.f16, Width.f16, Width.f16, Width.f32, Width.f16, Width.f32, //
      Width.f32, Width.f64, Width.f64, Width.f64, Width.f16, Width.f16, Width.f16,
    ];
    for (var i = 0; i < samples.length; i++) {
      expect(Width.of(samples[i]), want[i], reason: '${samples[i]}');
    }
    // Each value is in its own class and in no narrower width's.
    for (final x in samples) {
      final c = FloatClass.of(x);
      expect(c.contains(x), isTrue, reason: '$x is not in $c');
      if (Width.of(x) != Width.f16) {
        expect(FloatClass.width(Width.f16).contains(x), isFalse, reason: '$x is not an f16');
      }
    }
  });

  test('meet is exact and join holds both sides', () {
    final all = classes();
    for (final a in all) {
      for (final b in all) {
        final (m, j) = (a.meet(b), a.join(b));
        expect(j, b.join(a));
        expect(a.widen(j, Landmarks.none()), j);
        expect(j.narrow(a, Landmarks.none()), a);
        expect(a.leq(b), allIn(a, b) || a == FloatClass.bottom, reason: '$a ⊑ $b');
        for (final x in samples) {
          expect(m.contains(x), a.contains(x) && b.contains(x), reason: '$x: $a ⊓ $b = $m');
          if (a.contains(x) || b.contains(x)) {
            expect(j.contains(x), isTrue, reason: '$x: $a ⊔ $b = $j');
          }
        }
      }
    }
  });

  test('the facets a key needs read off the class', () {
    final finite = FloatClass([Kind.finite], Width.f64);
    final noNan = FloatClass([Kind.finite, Kind.posInf], Width.f32);
    expect(finite.isFinite && finite.excludesNan, isTrue);
    expect(!noNan.isFinite && noNan.excludesNan, isTrue);
    expect(FloatClass.top.excludesNan, isFalse);
    expect(noNan.toString(), 'f32{finite, inf}');
    expect(FloatClass.of(double.nan).toString(), 'f16{nan}');
    expect(FloatClass.bottom.toString(), '{}');
  });
}
