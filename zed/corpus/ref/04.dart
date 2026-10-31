/// 04 running variance. Zed rules used: a float `+` scan entry is the exact prefix sum rounded
/// once (fsum); `/`, `*`, `-` are IEEE binary64; floats print by the shortest round-trip rule
/// (zedrt.fmt); "${x}" is String(x); f64(s) reads the input text.
library;

import 'zedrt.dart';

void main(List<String> args) {
  final xs = [for (final l in readLines(args[0])) parseFloat(l)];
  for (final (i, x) in xs.indexed) {
    final n = fsum(List.filled(i + 1, 1.0));
    final s1 = fsum(xs.take(i + 1));
    final s2 = fsum([for (final v in xs.take(i + 1)) v * v]);
    final m = s1 / n;
    print('${fmt(x)} ${fmt(m)} ${fmt(s2 / n - m * m)}');
  }
}
