/// 21 stats. Zed rules used: f64(s) parses a decimal (#invalid -> 0.0 by the program's else);
/// a float `.sum` is the exact sum rounded once (fsum); `/`, `-`, `*` and `.sqrt` are IEEE;
/// floats print shortest round-trip (zedrt.fmt). Only mean and sd are printed. (The Python
/// original said cov was computed to check that it is a well-defined value the program could
/// have read; it only parsed the second column, unused, so neither is done here.)
library;

import 'dart:math' as math;

import 'zedrt.dart';

double num(String s) => tryParseFloat(s) ?? 0.0;

void main(List<String> args) {
  final xs = [for (final l in readLines(args[0])) num(l.split(' ')[0])];
  final n = xs.length.toDouble();
  // An empty input divides by zero, which the Python original raised on (Dart gives NaN).
  if (n == 0) throw UnsupportedError('float division by zero');
  final mx = fsum(xs) / n;
  final dx = [for (final x in xs) x - mx];
  final sd = math.sqrt(fsum([for (final d in dx) d * d]) / n);
  print('mean ${fmt(mx)}');
  print('sd ${fmt(sd)}');
}
