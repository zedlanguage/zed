/// 17 sensor windows. Zed rules used: int() of a non-integer is #invalid, so `else -1` and
/// the where drop the line; the assumed window signature puts a reading in the window starting
/// at t div 10 * 10 (Euclidean div, t >= 0 here), windows in start order, absent when empty;
/// groups in sensor-name order; the output is the batch result, which the streaming plan
/// must equal.
library;

import 'zedrt.dart';

BigInt num(String s) => tryParseInt(s) ?? BigInt.from(-1);

void main(List<String> args) {
  final ten = BigInt.from(10);
  final wins = <BigInt, Map<String, List<BigInt>>>{};
  for (final l in readLines(args[0])) {
    final w = l.split(' ');
    final t = num(w[0]);
    final s = w.length > 1 ? w[1] : '';
    final v = num(w.length > 2 ? w[2] : '');
    if (t >= BigInt.zero && v >= BigInt.zero) {
      wins.putIfAbsent(floorDiv(t, ten) * ten, () => {}).putIfAbsent(s, () => []).add(v);
    }
  }
  for (final w in wins.keys.toList()..sort()) {
    final groups = wins[w]!;
    final parts = [
      for (final s in sortedByCodePoint(groups.keys))
        switch (groups[s]!) {
          final vs =>
            '$s n=${vs.length} sum=${vs.fold(BigInt.zero, (a, b) => a + b)} '
                'max=${vs.reduce(maxBig)}',
        },
    ];
    print('$w: ${parts.join('; ')}');
  }
}
