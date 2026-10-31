/// 22 top-K: score descending, then name ascending (code-point order).
library;

import 'zedrt.dart';

void main(List<String> args) {
  final es = [
    for (final l in readLines(args[0]))
      switch (l.split(' ')) {
        final w => (w[0], parseInt(w[1])),
      },
  ];
  es.sort((x, y) => y.$2 != x.$2 ? y.$2.compareTo(x.$2) : compareCodePoints(x.$1, y.$1));
  for (final (i, (n, s)) in es.take(3).indexed) {
    print('${i + 1} $n $s');
  }
}
