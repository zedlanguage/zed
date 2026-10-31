/// Helpers the reference scripts share: the Zed rules their outputs depend on.
///
/// - fmt(x): how Zed prints a value. Floats follow DESIGN.md line 320: the shortest digits
///   that round-trip, in fixed notation when the decimal exponent is in -6..<21 (at least one
///   digit on each side of the point), otherwise one digit, a point, the remaining digits ('0'
///   if none), 'e', and the exponent ('-' only when negative); special values print inf,
///   -inf, nan. Ints print in decimal; bools print true/false.
/// - fsum(xs): a float `+` fold or scan entry is the exact sum rounded once (DESIGN.md line
///   320). An exact zero is 0.0 (DESIGN.md says -0.0 when every element is -0.0), and both
///   inf and -inf, or a finite sum that rounds to an infinity, throw.
/// - tree(xs, op): every other float fold uses the canonical tree of line 320.
/// - natural order (sec:order) for the keys these programs use: ints ascending, strings by
///   code point (compareCodePoints; Dart's String.compareTo compares UTF-16 code units, which
///   puts U+E000..U+FFFF after the characters above U+FFFF), tuples lexicographically.
/// - readLines(path): stdin as Lines, the lines of the input with the final newline not
///   starting an extra empty line. "\r\n" and "\r" end a line too,
///   and a leading byte order mark is kept as U+FEFF.
///
/// Where the Zed rule is the same or unstated, the outputs follow these readings of text,
/// kept here so that every script makes them the same way:
/// - parseInt(s) / tryParseInt(s): surrounding whitespace, a sign, decimal digits of any
///   script, '_' between digits, at most 4300 digits; any size (BigInt).
/// - parseFloat(s) / tryParseFloat(s): the same reading of digits and a decimal float, and
///   also inf, infinity and nan in any case.
/// - lower(s): the full lowercase mapping (U+0130 becomes "i̇") and the final-sigma rule for
///   U+03A3.
/// - isDigit(c): a Numeric_Type of Decimal or Digit.
/// - floorDiv(a, b): the quotient rounded toward negative infinity.
/// The Unicode tables at the end are of Unicode 16.0.
library;

import 'dart:convert';
import 'dart:io';
import 'dart:math' as math;
import 'dart:typed_data';

String fmtFloat(double x) {
  if (x.isNaN) return 'nan';
  if (x.isInfinite) return x > 0 ? 'inf' : '-inf';
  if (x == 0) return x.isNegative ? '-0.0' : '0.0';
  final s = x.isNegative ? '-' : '';
  final (ds, e10) = _shortestDigits(x.abs());
  if (-6 <= e10 && e10 < 21) {
    if (e10 >= 0) {
      final ip = ds.substring(0, math.min(e10 + 1, ds.length)).padRight(e10 + 1, '0');
      final fp = ds.length > e10 + 1 ? ds.substring(e10 + 1) : '0';
      return '$s$ip.$fp';
    }
    return '${s}0.${'0' * (-e10 - 1)}$ds';
  }
  return '$s${ds[0]}.${ds.length > 1 ? ds.substring(1) : '0'}e$e10';
}

/// The shortest round-trip digits of positive finite [x], without leading or trailing
/// zeros, and the decimal exponent of the first one. Dart's double.toString prints the
/// shortest round-trip digits (the nearest where several are equally short), in forms such as "123.456", "100.0", "1.5e-7" and "1e+21".
(String, int) _shortestDigits(double x) {
  final text = x.toString();
  final eAt = text.indexOf('e');
  final mantissa = eAt < 0 ? text : text.substring(0, eAt);
  final exp = eAt < 0 ? 0 : int.parse(text.substring(eAt + 1));
  final point = mantissa.indexOf('.');
  final intLen = point < 0 ? mantissa.length : point;
  final all = mantissa.replaceAll('.', '');
  final lead = all.length - all.replaceFirst(RegExp('^0+'), '').length;
  final ds = all.substring(lead).replaceFirst(RegExp(r'0+$'), '');
  return (ds, intLen - 1 - lead + exp);
}

String fmt(Object v) => switch (v) {
  bool b => b ? 'true' : 'false',
  double x => fmtFloat(x),
  _ => '$v',
};

/// The exact sum of [xs] rounded once to the nearest double, ties to even.
double fsum(Iterable<double> xs) {
  var nan = false, posInf = false, negInf = false;
  final terms = <(int, int)>[]; // each finite nonzero x is mantissa * 2^exponent
  for (final x in xs) {
    if (x.isNaN) {
      nan = true;
    } else if (x.isInfinite) {
      if (x > 0) {
        posInf = true;
      } else {
        negInf = true;
      }
    } else if (x != 0) {
      terms.add(_decompose(x));
    }
  }
  if (posInf && negInf) throw ArgumentError('-inf + inf in fsum');
  if (nan) return double.nan;
  if (posInf) return double.infinity;
  if (negInf) return double.negativeInfinity;
  if (terms.isEmpty) return 0.0;
  final scale = terms.map((t) => t.$2).reduce(math.min);
  var sum = BigInt.zero;
  for (final (m, e) in terms) {
    sum += BigInt.from(m) << (e - scale);
  }
  final r = _round(sum, scale);
  if (r.isInfinite) throw ArgumentError('intermediate overflow in fsum');
  return r;
}

(int, int) _decompose(double x) {
  final bytes = ByteData(8)..setFloat64(0, x);
  final hi = bytes.getUint32(0), lo = bytes.getUint32(4);
  final biased = (hi >> 20) & 0x7ff;
  final fraction = ((hi & 0xfffff) << 32) | lo;
  final (m, e) = biased == 0 ? (fraction, -1074) : (fraction | (1 << 52), biased - 1075);
  return (hi >> 31 == 1 ? -m : m, e);
}

/// [sum] * 2^[scale] rounded to the nearest double, ties to even (0.0 for zero).
double _round(BigInt sum, int scale) {
  if (sum == BigInt.zero) return 0.0;
  final a = sum.abs();
  var q = math.max(scale + a.bitLength - 1 - 52, -1074); // exponent of the last kept bit
  var m = a << math.max(scale - q, 0);
  if (q > scale) {
    final shift = q - scale;
    m = a >> shift;
    final rem = a - (m << shift);
    final half = BigInt.one << (shift - 1);
    if (rem > half || rem == half && m.isOdd) m += BigInt.one;
  }
  var mi = m.toInt();
  if (mi == 1 << 53) {
    mi >>= 1;
    q += 1;
  }
  final int bits;
  if (mi >= 1 << 52) {
    final biased = q + 52 + 1023;
    if (biased >= 0x7ff) return sum.isNegative ? double.negativeInfinity : double.infinity;
    bits = (biased << 52) | (mi - (1 << 52));
  } else {
    bits = mi; // subnormal: q is -1074
  }
  final bytes = ByteData(8)
    ..setUint32(0, (bits >> 32) | (sum.isNegative ? 0x80000000 : 0))
    ..setUint32(4, bits & 0xffffffff);
  return bytes.getFloat64(0);
}

/// Canonical float tree (DESIGN.md line 320) over [xs] in level order.
T tree<T>(List<T> xs, T Function(T, T) op) {
  final n = xs.length;
  if (n == 0) throw ArgumentError('#empty');
  if (n == 1) return xs[0];
  if (n & (n - 1) == 0) {
    final h = n ~/ 2;
    return op(tree(xs.sublist(0, h), op), tree(xs.sublist(h), op));
  }
  final p = n & -n; // largest power of two dividing n
  return op(tree(xs.sublist(0, n - p), op), tree(xs.sublist(n - p), op));
}

/// Natural order of strings: by code point. At the first UTF-16 code unit where the strings
/// differ, moving the surrogates (U+D800..U+DFFF) above U+E000..U+FFFF makes code-unit order
/// agree with code-point order.
int compareCodePoints(String a, String b) {
  final n = math.min(a.length, b.length);
  for (var i = 0; i < n; i++) {
    final x = a.codeUnitAt(i), y = b.codeUnitAt(i);
    if (x != y) return _codePointRank(x) - _codePointRank(y);
  }
  return a.length - b.length;
}

int _codePointRank(int unit) => unit >= 0xE000
    ? unit - 0x800
    : unit >= 0xD800
    ? unit + 0x2000
    : unit;

List<String> sortedByCodePoint(Iterable<String> xs) => xs.toList()..sort(compareCodePoints);

List<String> readLines(String path) {
  final bytes = File(path).readAsBytesSync();
  // utf8.decode drops a leading byte order mark, which is kept here.
  final bom = bytes.length >= 3 && bytes[0] == 0xEF && bytes[1] == 0xBB && bytes[2] == 0xBF;
  var text = (bom ? '﻿' : '') + utf8.decode(bytes);
  text = text.replaceAll('\r\n', '\n').replaceAll('\r', '\n');
  if (text.isEmpty) return [];
  if (text.endsWith('\n')) text = text.substring(0, text.length - 1);
  return text.split('\n');
}

BigInt parseInt(String s) => tryParseInt(s) ?? (throw FormatException('invalid int', s));

BigInt? tryParseInt(String s) {
  final t = _asciiDigitsAndSpaces(s);
  if (t == null) return null;
  final m = RegExp(r'^[ \t\n\v\f\r]*([+-]?\d(?:_?\d)*)[ \t\n\v\f\r]*$').firstMatch(t);
  if (m == null) return null;
  final digits = m[1]!.replaceAll('_', '');
  if (digits.replaceFirst(RegExp('^[+-]'), '').length > 4300) return null;
  return BigInt.parse(digits);
}

double parseFloat(String s) => tryParseFloat(s) ?? (throw FormatException('invalid float', s));

double? tryParseFloat(String s) {
  var t = _asciiDigitsAndSpaces(s);
  if (t == null) return null;
  t = t.replaceFirst(RegExp(r'^[ \t\n\v\f\r]+'), '').replaceFirst(RegExp(r'[ \t\n\v\f\r]+$'), '');
  if (t.contains('_')) {
    // '_' only between two digits
    if (RegExp(r'(^|\D)_|_(\D|$)').hasMatch(t)) return null;
    t = t.replaceAll('_', '');
  }
  final m = RegExp(
    r'^([+-]?)(?:((?:\d+\.?\d*|\.\d+)(?:e[+-]?\d+)?)|(inf|infinity)|(nan))$',
    caseSensitive: false,
  ).firstMatch(t);
  if (m == null) return null;
  final negative = m[1] == '-';
  if (m[3] != null) return negative ? double.negativeInfinity : double.infinity;
  if (m[4] != null) return double.nan;
  return double.parse(t);
}

/// The first step of parseInt and parseFloat: a non-ASCII space becomes ' ', a decimal
/// digit of any script becomes its ASCII digit; any other non-ASCII character (or DEL)
/// makes the text unreadable (null).
String? _asciiDigitsAndSpaces(String s) {
  final out = StringBuffer();
  for (final c in s.runes) {
    if (c < 127) {
      out.writeCharCode(c);
    } else if (_inRanges(_spaces, c)) {
      out.write(' ');
    } else if (_decimalValue(c) case final d?) {
      out.writeCharCode(0x30 + d);
    } else {
      return null;
    }
  }
  return out.toString();
}

int? _decimalValue(int c) {
  final i = _lastAtMost(_decimalZeros, c, (z) => z);
  if (i < 0 || c - _decimalZeros[i] > 9) return null;
  return c - _decimalZeros[i];
}

bool isDigit(int c) => _inRanges(_digits, c);

String lower(String s) {
  final cs = s.runes.toList();
  final out = StringBuffer();
  for (var i = 0; i < cs.length; i++) {
    final c = cs[i];
    if (c == 0x3A3) {
      out.writeCharCode(_finalSigma(cs, i) ? 0x3C2 : 0x3C3);
    } else if (c == 0x130) {
      out.write('i̇');
    } else {
      out.writeCharCode(_lowerOf(c));
    }
  }
  return out.toString();
}

/// Capital sigma at [i] is final when a cased letter precedes it and none follows it, case-
/// ignorable characters between them skipped (Unicode's Final_Sigma context).
bool _finalSigma(List<int> cs, int i) {
  bool cased(int c) => _inRanges(_cased, c);
  bool ignorable(int c) => _inRanges(_caseIgnorable, c);
  var j = i - 1;
  while (j >= 0 && ignorable(cs[j])) {
    j--;
  }
  if (j < 0 || !cased(cs[j])) return false;
  var k = i + 1;
  while (k < cs.length && ignorable(cs[k])) {
    k++;
  }
  return k == cs.length || !cased(cs[k]);
}

int _lowerOf(int c) {
  final i = _lastAtMost(_lowerRuns, c, (r) => r.start);
  if (i < 0) return c;
  final r = _lowerRuns[i];
  return c <= r.end && (c - r.start) % r.stride == 0 ? c + r.delta : c;
}

BigInt floorDiv(BigInt a, BigInt b) {
  final q = a ~/ b;
  return a.remainder(b) != BigInt.zero && a.isNegative != b.isNegative ? q - BigInt.one : q;
}

BigInt maxBig(BigInt a, BigInt b) => a >= b ? a : b;

BigInt minBig(BigInt a, BigInt b) => a <= b ? a : b;

/// The index of the last element of sorted [xs] whose key is at most [c], or -1.
int _lastAtMost<T>(List<T> xs, int c, int Function(T) key) {
  var lo = 0, hi = xs.length;
  while (lo < hi) {
    final mid = (lo + hi) ~/ 2;
    if (key(xs[mid]) <= c) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return lo - 1;
}

bool _inRanges(List<(int, int)> ranges, int c) {
  final i = _lastAtMost(ranges, c, (r) => r.$1);
  return i >= 0 && c <= ranges[i].$2;
}

Iterable<String> _fields(String data) => data.split(RegExp(r'\s+')).where((f) => f.isNotEmpty);

int _hex(String s) => int.parse(s, radix: 16);

List<(int, int)> _parseRanges(String data) => [
  for (final f in _fields(data))
    switch (f.split('-')) {
      [final a] => (_hex(a), _hex(a)),
      [final a, final b] => (_hex(a), _hex(b)),
      _ => throw FormatException('bad range', f),
    },
];

typedef _Run = ({int start, int end, int stride, int delta});

final List<_Run> _lowerRuns = [
  for (final f in _fields(_lowerData))
    switch (RegExp(r'^([0-9a-f]+)(?:-([0-9a-f]+)/(\d+))?:(-?\d+)$').firstMatch(f)) {
      final m? => (
        start: _hex(m[1]!),
        end: _hex(m[2] ?? m[1]!),
        stride: int.parse(m[3] ?? '1'),
        delta: int.parse(m[4]!),
      ),
      null => throw FormatException('bad run', f),
    },
];
final _cased = _parseRanges(_casedData);
final _caseIgnorable = _parseRanges(_caseIgnorableData);
final _digits = _parseRanges(_digitData);
final _decimalZeros = [for (final f in _fields(_decimalData)) _hex(f)];
final _spaces = _parseRanges(_spaceData);

void main() {
  // self-test of the printing rule and the canonical tree
  const cases = [
    (1.0, '1.0'),
    (0.1, '0.1'),
    (-0.0, '-0.0'),
    (1e21, '1.0e21'),
    (1e20, '100000000000000000000.0'),
    (1.5e-7, '1.5e-7'),
    (1e-6, '0.000001'),
    (123.456, '123.456'),
    (2.5e-5, '0.000025'),
    (double.infinity, 'inf'),
    (double.nan, 'nan'),
  ];
  for (final (x, want) in cases) {
    final got = fmtFloat(x);
    if (got != want) throw StateError('fmtFloat($x) = $got, want $want');
  }
  final order = tree('abcdef'.split(''), (a, b) => '($a$b)');
  if (order != '(((ab)(cd))(ef))') throw StateError(order);
  print('zedrt self-test ok');
}

// Unicode 16.0 tables; whitespace-separated hexadecimal code
// points. _lowerData: start-end/stride:delta (or start:delta), each code point start,
// start + stride, ..., end lower-cases to itself + delta (the lowercase mapping without
// U+0130 and U+03A3, handled above). _casedData: cased characters that are not case-ignorable.
// _caseIgnorableData: case-ignorable characters. _digitData: a Numeric_Type of Decimal or
// Digit. _decimalData: the zero of each run of ten decimal digits (Numeric_Type Decimal).
// _spaceData: white space at or above U+007F (Bidi_Class WS, B or S, or category Zs).

const _lowerData = '''
41-5a/1:32 c0-d6/1:32 d8-de/1:32 100-12e/2:1 132-136/2:1 139-147/2:1 14a-176/2:1 178:-121
179-17d/2:1 181:210 182-184/2:1 186:206 187:1 189-18a/1:205 18b:1 18e:79 18f:202 190:203 191:1
193:205 194:207 196:211 197:209 198:1 19c:211 19d:213 19f:214 1a0-1a4/2:1 1a6:218 1a7:1 1a9:218
1ac:1 1ae:218 1af:1 1b1-1b2/1:217 1b3-1b5/2:1 1b7:219 1b8:1 1bc:1 1c4:2 1c5:1 1c7:2 1c8:1 1ca:2
1cb-1db/2:1 1de-1ee/2:1 1f1:2 1f2-1f4/2:1 1f6:-97 1f7:-56 1f8-21e/2:1 220:-130 222-232/2:1
23a:10795 23b:1 23d:-163 23e:10792 241:1 243:-195 244:69 245:71 246-24e/2:1 370-372/2:1 376:1
37f:116 386:38 388-38a/1:37 38c:64 38e-38f/1:63 391-3a1/1:32 3a4-3ab/1:32 3cf:8 3d8-3ee/2:1
3f4:-60 3f7:1 3f9:-7 3fa:1 3fd-3ff/1:-130 400-40f/1:80 410-42f/1:32 460-480/2:1 48a-4be/2:1
4c0:15 4c1-4cd/2:1 4d0-52e/2:1 531-556/1:48 10a0-10c5/1:7264 10c7:7264 10cd:7264
13a0-13ef/1:38864 13f0-13f5/1:8 1c89:1 1c90-1cba/1:-3008 1cbd-1cbf/1:-3008 1e00-1e94/2:1
1e9e:-7615 1ea0-1efe/2:1 1f08-1f0f/1:-8 1f18-1f1d/1:-8 1f28-1f2f/1:-8 1f38-1f3f/1:-8
1f48-1f4d/1:-8 1f59-1f5f/2:-8 1f68-1f6f/1:-8 1f88-1f8f/1:-8 1f98-1f9f/1:-8 1fa8-1faf/1:-8
1fb8-1fb9/1:-8 1fba-1fbb/1:-74 1fbc:-9 1fc8-1fcb/1:-86 1fcc:-9 1fd8-1fd9/1:-8 1fda-1fdb/1:-100
1fe8-1fe9/1:-8 1fea-1feb/1:-112 1fec:-7 1ff8-1ff9/1:-128 1ffa-1ffb/1:-126 1ffc:-9 2126:-7517
212a:-8383 212b:-8262 2132:28 2160-216f/1:16 2183:1 24b6-24cf/1:26 2c00-2c2f/1:48 2c60:1
2c62:-10743 2c63:-3814 2c64:-10727 2c67-2c6b/2:1 2c6d:-10780 2c6e:-10749 2c6f:-10783 2c70:-10782
2c72:1 2c75:1 2c7e-2c7f/1:-10815 2c80-2ce2/2:1 2ceb-2ced/2:1 2cf2:1 a640-a66c/2:1 a680-a69a/2:1
a722-a72e/2:1 a732-a76e/2:1 a779-a77b/2:1 a77d:-35332 a77e-a786/2:1 a78b:1 a78d:-42280
a790-a792/2:1 a796-a7a8/2:1 a7aa:-42308 a7ab:-42319 a7ac:-42315 a7ad:-42305 a7ae:-42308
a7b0:-42258 a7b1:-42282 a7b2:-42261 a7b3:928 a7b4-a7c2/2:1 a7c4:-48 a7c5:-42307 a7c6:-35384
a7c7-a7c9/2:1 a7cb:-42343 a7cc:1 a7d0:1 a7d6-a7da/2:1 a7dc:-42561 a7f5:1 ff21-ff3a/1:32
10400-10427/1:40 104b0-104d3/1:40 10570-1057a/1:39 1057c-1058a/1:39 1058c-10592/1:39
10594-10595/1:39 10c80-10cb2/1:64 10d50-10d65/1:32 118a0-118bf/1:32 16e40-16e5f/1:32
1e900-1e921/1:34''';

const _casedData = '''
41-5a 61-7a aa b5 ba c0-d6 d8-f6 f8-1ba 1bc-1bf 1c4-293 295-2af 370-373 376-377 37b-37d 37f 386
388-38a 38c 38e-3a1 3a3-3f5 3f7-481 48a-52f 531-556 560-588 10a0-10c5 10c7 10cd 10d0-10fa
10fd-10ff 13a0-13f5 13f8-13fd 1c80-1c8a 1c90-1cba 1cbd-1cbf 1d00-1d2b 1d6b-1d77 1d79-1d9a
1e00-1f15 1f18-1f1d 1f20-1f45 1f48-1f4d 1f50-1f57 1f59 1f5b 1f5d 1f5f-1f7d 1f80-1fb4 1fb6-1fbc
1fbe 1fc2-1fc4 1fc6-1fcc 1fd0-1fd3 1fd6-1fdb 1fe0-1fec 1ff2-1ff4 1ff6-1ffc 2102 2107 210a-2113
2115 2119-211d 2124 2126 2128 212a-212d 212f-2134 2139 213c-213f 2145-2149 214e 2160-217f
2183-2184 24b6-24e9 2c00-2c7b 2c7e-2ce4 2ceb-2cee 2cf2-2cf3 2d00-2d25 2d27 2d2d a640-a66d
a680-a69b a722-a76f a771-a787 a78b-a78e a790-a7cd a7d0-a7d1 a7d3 a7d5-a7dc a7f5-a7f6 a7fa
ab30-ab5a ab60-ab68 ab70-abbf fb00-fb06 fb13-fb17 ff21-ff3a ff41-ff5a 10400-1044f 104b0-104d3
104d8-104fb 10570-1057a 1057c-1058a 1058c-10592 10594-10595 10597-105a1 105a3-105b1 105b3-105b9
105bb-105bc 10c80-10cb2 10cc0-10cf2 10d50-10d65 10d70-10d85 118a0-118df 16e40-16e7f 1d400-1d454
1d456-1d49c 1d49e-1d49f 1d4a2 1d4a5-1d4a6 1d4a9-1d4ac 1d4ae-1d4b9 1d4bb 1d4bd-1d4c3 1d4c5-1d505
1d507-1d50a 1d50d-1d514 1d516-1d51c 1d51e-1d539 1d53b-1d53e 1d540-1d544 1d546 1d54a-1d550
1d552-1d6a5 1d6a8-1d6c0 1d6c2-1d6da 1d6dc-1d6fa 1d6fc-1d714 1d716-1d734 1d736-1d74e 1d750-1d76e
1d770-1d788 1d78a-1d7a8 1d7aa-1d7c2 1d7c4-1d7cb 1df00-1df09 1df0b-1df1e 1df25-1df2a 1e900-1e943
1f130-1f149 1f150-1f169 1f170-1f189''';

const _caseIgnorableData = '''
27 2e 3a 5e 60 a8 ad af b4 b7-b8 2b0-36f 374-375 37a 384-385 387 483-489 559 55f 591-5bd 5bf
5c1-5c2 5c4-5c5 5c7 5f4 600-605 610-61a 61c 640 64b-65f 670 6d6-6dd 6df-6e8 6ea-6ed 70f 711
730-74a 7a6-7b0 7eb-7f5 7fa 7fd 816-82d 859-85b 888 890-891 897-89f 8c9-902 93a 93c 941-948 94d
951-957 962-963 971 981 9bc 9c1-9c4 9cd 9e2-9e3 9fe a01-a02 a3c a41-a42 a47-a48 a4b-a4d a51
a70-a71 a75 a81-a82 abc ac1-ac5 ac7-ac8 acd ae2-ae3 afa-aff b01 b3c b3f b41-b44 b4d b55-b56
b62-b63 b82 bc0 bcd c00 c04 c3c c3e-c40 c46-c48 c4a-c4d c55-c56 c62-c63 c81 cbc cbf cc6 ccc-ccd
ce2-ce3 d00-d01 d3b-d3c d41-d44 d4d d62-d63 d81 dca dd2-dd4 dd6 e31 e34-e3a e46-e4e eb1 eb4-ebc
ec6 ec8-ece f18-f19 f35 f37 f39 f71-f7e f80-f84 f86-f87 f8d-f97 f99-fbc fc6 102d-1030 1032-1037
1039-103a 103d-103e 1058-1059 105e-1060 1071-1074 1082 1085-1086 108d 109d 10fc 135d-135f
1712-1714 1732-1733 1752-1753 1772-1773 17b4-17b5 17b7-17bd 17c6 17c9-17d3 17d7 17dd 180b-180f
1843 1885-1886 18a9 1920-1922 1927-1928 1932 1939-193b 1a17-1a18 1a1b 1a56 1a58-1a5e 1a60 1a62
1a65-1a6c 1a73-1a7c 1a7f 1aa7 1ab0-1ace 1b00-1b03 1b34 1b36-1b3a 1b3c 1b42 1b6b-1b73 1b80-1b81
1ba2-1ba5 1ba8-1ba9 1bab-1bad 1be6 1be8-1be9 1bed 1bef-1bf1 1c2c-1c33 1c36-1c37 1c78-1c7d
1cd0-1cd2 1cd4-1ce0 1ce2-1ce8 1ced 1cf4 1cf8-1cf9 1d2c-1d6a 1d78 1d9b-1dff 1fbd 1fbf-1fc1
1fcd-1fcf 1fdd-1fdf 1fed-1fef 1ffd-1ffe 200b-200f 2018-2019 2024 2027 202a-202e 2060-2064
2066-206f 2071 207f 2090-209c 20d0-20f0 2c7c-2c7d 2cef-2cf1 2d6f 2d7f 2de0-2dff 2e2f 3005
302a-302d 3031-3035 303b 3099-309e 30fc-30fe a015 a4f8-a4fd a60c a66f-a672 a674-a67d a67f
a69c-a69f a6f0-a6f1 a700-a721 a770 a788-a78a a7f2-a7f4 a7f8-a7f9 a802 a806 a80b a825-a826 a82c
a8c4-a8c5 a8e0-a8f1 a8ff a926-a92d a947-a951 a980-a982 a9b3 a9b6-a9b9 a9bc-a9bd a9cf a9e5-a9e6
aa29-aa2e aa31-aa32 aa35-aa36 aa43 aa4c aa70 aa7c aab0 aab2-aab4 aab7-aab8 aabe-aabf aac1 aadd
aaec-aaed aaf3-aaf4 aaf6 ab5b-ab5f ab69-ab6b abe5 abe8 abed fb1e fbb2-fbc2 fe00-fe0f fe13
fe20-fe2f fe52 fe55 feff ff07 ff0e ff1a ff3e ff40 ff70 ff9e-ff9f ffe3 fff9-fffb 101fd 102e0
10376-1037a 10780-10785 10787-107b0 107b2-107ba 10a01-10a03 10a05-10a06 10a0c-10a0f 10a38-10a3a
10a3f 10ae5-10ae6 10d24-10d27 10d4e 10d69-10d6d 10d6f 10eab-10eac 10efc-10eff 10f46-10f50
10f82-10f85 11001 11038-11046 11070 11073-11074 1107f-11081 110b3-110b6 110b9-110ba 110bd 110c2
110cd 11100-11102 11127-1112b 1112d-11134 11173 11180-11181 111b6-111be 111c9-111cc 111cf
1122f-11231 11234 11236-11237 1123e 11241 112df 112e3-112ea 11300-11301 1133b-1133c 11340
11366-1136c 11370-11374 113bb-113c0 113ce 113d0 113d2 113e1-113e2 11438-1143f 11442-11444 11446
1145e 114b3-114b8 114ba 114bf-114c0 114c2-114c3 115b2-115b5 115bc-115bd 115bf-115c0 115dc-115dd
11633-1163a 1163d 1163f-11640 116ab 116ad 116b0-116b5 116b7 1171d 1171f 11722-11725 11727-1172b
1182f-11837 11839-1183a 1193b-1193c 1193e 11943 119d4-119d7 119da-119db 119e0 11a01-11a0a
11a33-11a38 11a3b-11a3e 11a47 11a51-11a56 11a59-11a5b 11a8a-11a96 11a98-11a99 11c30-11c36
11c38-11c3d 11c3f 11c92-11ca7 11caa-11cb0 11cb2-11cb3 11cb5-11cb6 11d31-11d36 11d3a 11d3c-11d3d
11d3f-11d45 11d47 11d90-11d91 11d95 11d97 11ef3-11ef4 11f00-11f01 11f36-11f3a 11f40 11f42 11f5a
13430-13440 13447-13455 1611e-16129 1612d-1612f 16af0-16af4 16b30-16b36 16b40-16b43 16d40-16d42
16d6b-16d6c 16f4f 16f8f-16f9f 16fe0-16fe1 16fe3-16fe4 1aff0-1aff3 1aff5-1affb 1affd-1affe
1bc9d-1bc9e 1bca0-1bca3 1cf00-1cf2d 1cf30-1cf46 1d167-1d169 1d173-1d182 1d185-1d18b 1d1aa-1d1ad
1d242-1d244 1da00-1da36 1da3b-1da6c 1da75 1da84 1da9b-1da9f 1daa1-1daaf 1e000-1e006 1e008-1e018
1e01b-1e021 1e023-1e024 1e026-1e02a 1e030-1e06d 1e08f 1e130-1e13d 1e2ae 1e2ec-1e2ef 1e4eb-1e4ef
1e5ee-1e5ef 1e8d0-1e8d6 1e944-1e94b 1f3fb-1f3ff e0001 e0020-e007f e0100-e01ef''';

const _digitData = '''
30-39 b2-b3 b9 660-669 6f0-6f9 7c0-7c9 966-96f 9e6-9ef a66-a6f ae6-aef b66-b6f be6-bef c66-c6f
ce6-cef d66-d6f de6-def e50-e59 ed0-ed9 f20-f29 1040-1049 1090-1099 1369-1371 17e0-17e9
1810-1819 1946-194f 19d0-19da 1a80-1a89 1a90-1a99 1b50-1b59 1bb0-1bb9 1c40-1c49 1c50-1c59 2070
2074-2079 2080-2089 2460-2468 2474-247c 2488-2490 24ea 24f5-24fd 24ff 2776-277e 2780-2788
278a-2792 a620-a629 a8d0-a8d9 a900-a909 a9d0-a9d9 a9f0-a9f9 aa50-aa59 abf0-abf9 ff10-ff19
104a0-104a9 10a40-10a43 10d30-10d39 10d40-10d49 10e60-10e68 11052-1105a 11066-1106f 110f0-110f9
11136-1113f 111d0-111d9 112f0-112f9 11450-11459 114d0-114d9 11650-11659 116c0-116c9 116d0-116e3
11730-11739 118e0-118e9 11950-11959 11bf0-11bf9 11c50-11c59 11d50-11d59 11da0-11da9 11f50-11f59
16130-16139 16a60-16a69 16ac0-16ac9 16b50-16b59 16d70-16d79 1ccf0-1ccf9 1d7ce-1d7ff 1e140-1e149
1e2f0-1e2f9 1e4f0-1e4f9 1e5f1-1e5fa 1e950-1e959 1f100-1f10a 1fbf0-1fbf9''';

const _decimalData = '''
30 660 6f0 7c0 966 9e6 a66 ae6 b66 be6 c66 ce6 d66 de6 e50 ed0 f20 1040 1090 17e0 1810 1946 19d0
1a80 1a90 1b50 1bb0 1c40 1c50 a620 a8d0 a900 a9d0 a9f0 aa50 abf0 ff10 104a0 10d30 10d40 11066
110f0 11136 111d0 112f0 11450 114d0 11650 116c0 116d0 116da 11730 118e0 11950 11bf0 11c50 11d50
11da0 11f50 16130 16a60 16ac0 16b50 16d70 1ccf0 1d7ce 1d7d8 1d7e2 1d7ec 1d7f6 1e140 1e2f0 1e4f0
1e5f1 1e950 1fbf0''';

const _spaceData = '''
85 a0 1680 2000-200a 2028-2029 202f 205f 3000''';
