/// 02 histogram. Both columns are computed independently, as the two spellings are; rows for
/// lengths 1..=maxLen, a missing scatter key printing 0. A length counts code points.
library;

import 'dart:math' as math;

import 'zedrt.dart';

void main(List<String> args) {
  final words = [
    for (final w in readLines(args[0]).join(' ').split(' '))
      if (w.isNotEmpty) w.runes.length,
  ];
  final histA = <int, int>{};
  for (final n in words) {
    histA.update(n, (c) => c + 1, ifAbsent: () => 1);
  }
  final maxLen = words.fold(0, math.max);
  for (var n = 1; n <= maxLen; n++) {
    final histB = words.where((len) => len == n).length;
    print('$n ${histA[n] ?? 0} $histB');
  }
}
