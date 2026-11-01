/// Float classes (DESIGN.md sec:domains, "float classes (finite / non-NaN facets; width
/// f16/f32/f64)"; step L1.24).
///
/// An element is the set of kinds a float may be — negative infinity, finite, positive
/// infinity, NaN — and a width: the narrowest IEEE binary format that holds each value
/// exactly. Every infinity and the NaN are in every format, and a finite value is in a format
/// when its significand fits the format's precision and its exponent the format's range.
/// Join is union of kinds and the wider width, meet intersection and the narrower; the empty
/// set of kinds is the bottom, whatever the width. The lattice has finite height, so its
/// widening is the join.
library;

import 'dart:typed_data';

import 'lattice.dart';

/// An IEEE binary format, narrowest first.
enum Width {
  /// binary16.
  f16(11, -24, 65504.0),

  /// binary32.
  f32(24, -149, 3.4028234663852886e38),

  /// binary64.
  f64(53, -1074, double.maxFinite);

  /// The significand bits, the least exponent of a subnormal's last bit, and the largest
  /// finite value.
  final int _bits, _least;
  final double _max;

  const Width(this._bits, this._least, this._max);

  /// Whether the finite `x` is exactly a value of this format.
  bool holds(double x) {
    if (x == 0) return true;
    if (x.abs() > _max) return false;
    // x = m · 2^e with m odd.
    final raw = (ByteData(8)..setFloat64(0, x.abs())).getInt64(0);
    final (field, frac) = (raw >> 52, raw & ((1 << 52) - 1));
    var (m, e) = field == 0 ? (frac, -1074) : (frac | (1 << 52), field - 1075);
    final tz = (m & -m).bitLength - 1;
    m >>= tz;
    e += tz;
    return m < (1 << _bits) && e >= _least;
  }

  /// The narrowest format holding `x`.
  static Width of(double x) => x.isFinite ? values.firstWhere((w) => w.holds(x)) : f16;

  Width _max2(Width o) => index >= o.index ? this : o;
  Width _min2(Width o) => index <= o.index ? this : o;
}

/// A kind a float may be.
enum Kind {
  /// Negative infinity.
  negInf('-inf'),

  /// A finite value, zero included.
  finite('finite'),

  /// Positive infinity.
  posInf('inf'),

  /// A NaN.
  nan('nan');

  final String _name;

  const Kind(this._name);

  int get _bit => 1 << index;

  /// The kind of `x`.
  static Kind of(double x) => switch (x) {
    _ when x.isNaN => nan,
    double.infinity => posInf,
    double.negativeInfinity => negInf,
    _ => finite,
  };
}

/// A float class.
final class FloatClass with Lattice<FloatClass> {
  final int _kinds;
  final Width _width;

  const FloatClass._(this._kinds, this._width);

  /// No float.
  static const bottom = FloatClass._(0, Width.f16);

  /// Every float.
  static final top = FloatClass.width(Width.f64);

  /// The floats of the given kinds at the given width.
  factory FloatClass(Iterable<Kind> kinds, Width width) {
    final k = kinds.fold(0, (k, x) => k | x._bit);
    return k == 0 ? bottom : FloatClass._(k, width);
  }

  /// The class of the one value `x`.
  factory FloatClass.of(double x) => FloatClass([Kind.of(x)], Width.of(x));

  /// Every float of the given width.
  factory FloatClass.width(Width width) => FloatClass(Kind.values, width);

  /// Whether `x` is in the class.
  bool contains(double x) => _kinds & Kind.of(x)._bit != 0 && (!x.isFinite || _width.holds(x));

  /// Whether no value of the class is a NaN: the condition for a float key or a sort key
  /// (sec:corner_cases).
  bool get excludesNan => _kinds & Kind.nan._bit == 0;

  /// Whether every value of the class is finite.
  bool get isFinite => _kinds & ~Kind.finite._bit == 0;

  @override
  FloatClass join(FloatClass other) => switch ((_kinds, other._kinds)) {
    (0, _) => other,
    (_, 0) => this,
    _ => FloatClass._(_kinds | other._kinds, _width._max2(other._width)),
  };

  @override
  FloatClass meet(FloatClass other) => switch (_kinds & other._kinds) {
    0 => bottom,
    final k => FloatClass._(k, _width._min2(other._width)),
  };

  @override
  FloatClass widen(FloatClass next, Landmarks marks) => join(next);

  @override
  FloatClass narrow(FloatClass next, Landmarks marks) => next;

  @override
  bool operator ==(Object other) =>
      other is FloatClass && other._kinds == _kinds && other._width == _width;

  @override
  int get hashCode => Object.hash(_kinds, _width);

  /// `f64{finite, nan}`; the bottom is `{}`.
  @override
  String toString() {
    if (_kinds == 0) return '{}';
    final names = [
      for (final k in Kind.values)
        if (_kinds & k._bit != 0) k._name,
    ];
    return '${_width.name}{${names.join(', ')}}';
  }
}
