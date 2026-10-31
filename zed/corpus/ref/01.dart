/// 01 word count. Zed rules used: split(" ") keeps empty pieces (removed by the where); group
/// keys are the lower-cased words; a push of a String-keyed map into stdout is in the keys'
/// natural order, code-point order (sec:order).
library;

import 'zedrt.dart';

void main(List<String> args) {
  final words = readLines(args[0]).join(' ').split(' ').where((w) => w.isNotEmpty);
  final counts = <String, int>{};
  for (final w in words) {
    counts.update(lower(w), (n) => n + 1, ifAbsent: () => 1);
  }
  for (final w in sortedByCodePoint(counts.keys)) {
    print('$w ${counts[w]}');
  }
}
