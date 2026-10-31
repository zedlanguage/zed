/// 29 late-arrival dedup, under the window rule this corpus assumes: readings are taken in
/// arrival order (the input's line order); the watermark is the largest event time seen so
/// far minus the lateness 5; a reading is dropped (late: #drop) when its window's end, start +
/// 10, is at or below the watermark at its arrival. Kept readings are deduplicated per window
/// and id, first arrival wins (group then first). Windows print in start order, ids in
/// code-point order.
library;

import 'zedrt.dart';

void main(List<String> args) {
  final (five, ten) = (BigInt.from(5), BigInt.from(10));
  final wins = <BigInt, Map<String, BigInt>>{};
  BigInt? top;
  for (final l in readLines(args[0])) {
    final [i, ts, vs] = l.split(' ');
    final (t, v) = (parseInt(ts), parseInt(vs));
    final start = floorDiv(t, ten) * ten;
    final wm = top == null ? null : top - five;
    top = top == null ? t : maxBig(top, t);
    if (wm != null && start + ten <= wm) continue;
    wins.putIfAbsent(start, () => {}).putIfAbsent(i, () => v);
  }
  for (final w in wins.keys.toList()..sort()) {
    final ids = wins[w]!;
    print('$w: ${sortedByCodePoint(ids.keys).map((i) => '$i=${ids[i]}').join(' ')}');
  }
}
