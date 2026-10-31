/// 18 windowed word frequency: window start t div 5 * 5, words case folded, empty pieces
/// (from double spaces) dropped, words in code-point order. A line whose first piece is not an
/// int is skipped; a window exists once it has a word.
library;

import 'zedrt.dart';

void main(List<String> args) {
  final five = BigInt.from(5);
  final wins = <BigInt, Map<String, int>>{};
  for (final l in readLines(args[0])) {
    final w = l.split(' ');
    final t = tryParseInt(w[0]);
    if (t == null) continue;
    for (final x in w.skip(1)) {
      if (x.isNotEmpty) {
        wins
            .putIfAbsent(floorDiv(t, five) * five, () => {})
            .update(lower(x), (n) => n + 1, ifAbsent: () => 1);
      }
    }
  }
  for (final w in wins.keys.toList()..sort()) {
    final c = wins[w]!;
    print('$w: ${sortedByCodePoint(c.keys).map((x) => '$x=${c[x]}').join(' ')}');
  }
}
