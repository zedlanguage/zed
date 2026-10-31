// Exact numbers (step L1.17): unbounded integers, rationals, and the order of numbers by value
// across `int`, `rat` and floats (DESIGN.md sec:keys, the natural order).
//
// The semantic `int` is unbounded (sec:numeric). An integer inside the 64-bit range is an
// [Int]; one outside it is a [Big], so every integer has one representation and the fast path
// stays a machine word. A [Rat] is reduced, with a positive denominator, so equal rationals
// are equal values.
part of 'value.dart';

/// The most bits an exact number may take: a result beyond it is an overflow.
const maxBits = 1 << 20;

/// The bits of `n`'s magnitude.
int bitsOf(BigInt n) => n.abs().bitLength;

/// A rational, `3r` or `1r/3r`: reduced, with a positive denominator.
final class Rat extends Value {
  final BigInt num, den;

  const Rat._(this.num, this.den);

  /// `num / den` reduced; null when `den` is zero.
  static Rat? make(BigInt num, BigInt den) {
    if (den == BigInt.zero) return null;
    var g = num.gcd(den);
    if (den.isNegative) g = -g;
    return Rat._(num ~/ g, den ~/ g);
  }

  /// The integer `n`.
  Rat.integer(BigInt n) : this._(n, BigInt.one);

  /// The rational a decimal literal such as `1.25e-3` writes; null when it is malformed or its
  /// exponent is beyond [maxBits].
  static Rat? decimal(String text) {
    var mantissa = text, exp = 0;
    final e = text.indexOf(RegExp('[eE]'));
    if (e >= 0) {
      mantissa = text.substring(0, e);
      final x = int.tryParse(text.substring(e + 1));
      if (x == null) return null;
      exp = x;
    }
    final dot = mantissa.indexOf('.');
    final whole = dot < 0 ? mantissa : mantissa.substring(0, dot);
    final frac = dot < 0 ? '' : mantissa.substring(dot + 1);
    final digits = BigInt.tryParse('$whole$frac');
    if (digits == null) return null;
    exp -= frac.length;
    // 10^e has more than 3e bits.
    if (exp.abs() * 3 > maxBits) return null;
    final scale = BigInt.from(10).pow(exp.abs());
    return exp >= 0 ? make(digits * scale, BigInt.one) : make(digits, scale);
  }

  Rat operator +(Rat b) => make(num * b.den + b.num * den, den * b.den)!;

  Rat operator -(Rat b) => this + -b;

  Rat operator *(Rat b) => make(num * b.num, den * b.den)!;

  /// The quotient; null when `b` is zero.
  Rat? div(Rat b) => make(num * b.den, den * b.num);

  Rat operator -() => Rat._(-num, den);

  /// The bits of the larger of numerator and denominator.
  int get bits => math.max(bitsOf(num), bitsOf(den));

  bool get isNegative => num.isNegative;

  int compareRat(Rat other) => (num * other.den).compareTo(other.num * den);
}

/// A number placed on the extended line, for comparing numbers of different kinds:
/// `-inf`, then the finite numbers, then `+inf`, then NaN, which is after `+inf` in a float's
/// total order.
final class Exact implements Comparable<Exact> {
  /// 0 for `-inf`, 1 for a finite number, 2 for `+inf`, 3 for NaN.
  final int rank;
  final Rat? finite;

  const Exact._(this.rank, this.finite);

  Exact.of(Rat r) : this._(1, r);

  /// The float `x` placed exactly.
  factory Exact.float(double x) {
    if (x.isNaN) return const Exact._(3, null);
    if (x.isInfinite) return Exact._(x > 0 ? 2 : 0, null);
    final bits = f64Bits(x);
    final exp = (bits >>> 52) & 0x7ff;
    final frac = bits & ((1 << 52) - 1);
    final (mantissa, e) = exp == 0 ? (frac, -1074) : (frac | (1 << 52), exp - 1075);
    var m = BigInt.from(mantissa);
    if (bits < 0) m = -m;
    final r = e >= 0 ? Rat.integer(m << e) : Rat.make(m, BigInt.one << -e)!;
    return Exact._(1, r);
  }

  @override
  int compareTo(Exact other) =>
      rank != other.rank ? rank - other.rank : (rank == 1 ? finite!.compareRat(other.finite!) : 0);

  @override
  bool operator ==(Object other) => other is Exact && compareTo(other) == 0;

  @override
  int get hashCode => Object.hash(rank, finite?.num, finite?.den);
}

final _bytes = ByteData(8);

/// The IEEE 754 bits of `x`, as a signed 64-bit integer.
int f64Bits(double x) {
  _bytes.setFloat64(0, x);
  return _bytes.getInt64(0);
}

/// The float whose IEEE 754 bits are `bits`.
double f64FromBits(int bits) {
  _bytes.setInt64(0, bits);
  return _bytes.getFloat64(0);
}

/// A float as the language writes it: the shortest digits that read back as `x`, with `.0` on
/// a whole number, and an exponent outside `1e-6 ≤ |x| < 1e21`: `0.1`, `100.0`, `1.0e300`.
String showF64(double x) {
  if (x.isNaN) return 'nan';
  if (x.isInfinite) return x > 0 ? 'inf' : '-inf';
  // The shortest digits, as `-1.25e-7` or `5e+0`.
  final sci = x.toStringAsExponential();
  final e = sci.indexOf('e');
  final exp = int.parse(sci.substring(e + 1));
  var mantissa = sci.substring(0, e);
  var sign = '';
  if (mantissa.startsWith('-')) {
    sign = '-';
    mantissa = mantissa.substring(1);
  }
  final digits = mantissa.replaceAll('.', '');
  final n = digits.length;
  final String body;
  if (exp >= -6 && exp < 21) {
    if (exp < 0) {
      body = '0.${'0' * (-exp - 1)}$digits';
    } else if (n <= exp + 1) {
      body = '$digits${'0' * (exp + 1 - n)}.0';
    } else {
      body = '${digits.substring(0, exp + 1)}.${digits.substring(exp + 1)}';
    }
  } else {
    final rest = digits.length > 1 ? digits.substring(1) : '0';
    body = '${digits[0]}.${rest}e$exp';
  }
  return '$sign$body';
}

/// The float equal to `r`, when one is.
double? exactF64(Rat r) {
  // A double is m * 2^k with |m| < 2^53, so its denominator is a power of two.
  final denBits = r.den.bitLength - 1;
  if (r.den != BigInt.one << denBits) return null;
  var x = r.num.toDouble();
  // Two exact scalings, the first staying normal, so the only rounding is the last one.
  var k = denBits;
  if (k > 1022) {
    x *= math.pow(2.0, -1022);
    k -= 1022;
  }
  x *= math.pow(2.0, -k);
  return Exact.float(x) == Exact.of(r) ? x : null;
}
