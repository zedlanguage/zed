/// The one-argument words on scalars (step L1.17): `show`, the casts, `abs`, and the string
/// words `len`, `lower`, `upper` and `trim`.
library;

import 'error.dart';
import 'term.dart';
import 'value.dart';

/// The word `p` applied to `x`. Throws [KernelTypeError] when `p` does not apply to `x`, and
/// [OverflowError] for a number beyond [maxBits].
Value word(Prim p, Value x) {
  const inexact = Atom('inexact'), invalid = Atom('invalid');
  switch ((p, x)) {
    case (Prim.show, Str()):
      return x;
    case (Prim.show, _):
      return Str(x is Float ? showF64(x.x) : '$x');
    case (Prim.castInt, Str(:final text)):
      final n = _readInt(text.text);
      return n == null ? invalid : sized(n);
    case (Prim.castRat, Str(:final text)):
      final r = _readRat(text.text);
      if (r == null) return invalid;
      if (r.bits > maxBits) throw const OverflowError();
      return r;
    case (Prim.castF64, Str(:final text)):
      final f = _readF64(text.text);
      if (f == null) return invalid;
      if (f.isInfinite && !text.text.endsWith('inf')) return inexact;
      return Float(f);
    case (Prim.castInt || Prim.castRat || Prim.castF64, _):
      if (x.numberKind == null) throw _typeErr(p, x);
      final r = x.exact.finite;
      if (r == null) return p == Prim.castF64 ? x : invalid;
      switch (p) {
        case Prim.castInt:
          return r.den == BigInt.one ? Value.integer(r.num) : inexact;
        case Prim.castRat:
          return r;
        default:
          final f = exactF64(r);
          return f == null ? inexact : Float(f);
      }
    case (Prim.abs, Int(:final value)):
      return value == _minInt ? Value.integer(-BigInt.from(value)) : Int(value.abs());
    case (Prim.abs, Big(:final value)):
      return Value.integer(value.abs());
    case (Prim.abs, Rat r):
      return r.isNegative ? -r : r;
    case (Prim.abs, Float(x: final f)):
      return Float(f.abs());
    case (Prim.len, Str(:final text)):
      return Int(text.text.runes.length);
    case (Prim.lower, Str(:final text)):
      return Str(text.text.toLowerCase());
    case (Prim.upper, Str(:final text)):
      return Str(text.text.toUpperCase());
    case (Prim.trim, Str(:final text)):
      return Str(_trim(text.text));
    default:
      throw _typeErr(p, x);
  }
}

const _minInt = -0x8000000000000000;

KernelTypeError _typeErr(Prim p, Value x) => KernelTypeError('$p applied to $x');

/// The integer `n`; throws [OverflowError] when it has more than [maxBits] bits.
Value sized(BigInt n) {
  if (bitsOf(n) > maxBits) throw const OverflowError();
  return Value.integer(n);
}

final _int = RegExp(r'^-?[0-9]+$');
final _decimal = RegExp(r'^-?[0-9]+\.[0-9]+$');
final _float = RegExp(r'^-?[0-9]+(\.[0-9]+)?(e-?[0-9]+)?$');

BigInt? _readInt(String s) => _int.hasMatch(s) ? BigInt.parse(s) : null;

Rat? _readRat(String s) {
  BigInt? part(String t) => _readInt(t.endsWith('r') ? t.substring(0, t.length - 1) : t);
  final slash = s.indexOf('/');
  if (slash >= 0) {
    final n = part(s.substring(0, slash)), d = part(s.substring(slash + 1));
    return n == null || d == null ? null : Rat.make(n, d);
  }
  final n = part(s);
  if (n != null) return Rat.integer(n);
  return _decimal.hasMatch(s) ? Rat.decimal(s) : null;
}

double? _readF64(String s) => switch (s) {
  'inf' => double.infinity,
  '-inf' => double.negativeInfinity,
  'nan' || '-nan' => double.nan,
  _ => _float.hasMatch(s) ? double.parse(s) : null,
};

/// `s` without leading and trailing characters of Unicode's White_Space property.
String _trim(String s) {
  bool space(int c) =>
      (c >= 0x09 && c <= 0x0D) ||
      c == 0x20 ||
      c == 0x85 ||
      c == 0xA0 ||
      c == 0x1680 ||
      (c >= 0x2000 && c <= 0x200A) ||
      c == 0x2028 ||
      c == 0x2029 ||
      c == 0x202F ||
      c == 0x205F ||
      c == 0x3000;
  var a = 0, b = s.length;
  while (a < b && space(s.codeUnitAt(a))) {
    a++;
  }
  while (b > a && space(s.codeUnitAt(b - 1))) {
    b--;
  }
  return s.substring(a, b);
}
