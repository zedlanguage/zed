/// 03 edit distance, top-down memoized and bottom-up; a line with one word gives b = ""
/// (w[1] else ""); a line starting with a space gives a = "". Characters are code points.
library;

import 'dart:math' as math;

import 'zedrt.dart';

int topDown(List<int> a, List<int> b) {
  final memo = [for (var i = 0; i <= a.length; i++) List<int?>.filled(b.length + 1, null)];
  int go(int i, int j) {
    if (i == 0) return j;
    if (j == 0) return i;
    return memo[i][j] ??= [
      go(i - 1, j) + 1,
      go(i, j - 1) + 1,
      go(i - 1, j - 1) + (a[i - 1] == b[j - 1] ? 0 : 1),
    ].reduce(math.min);
  }

  return go(a.length, b.length);
}

int bottomUp(List<int> a, List<int> b) {
  final d = [for (var i = 0; i <= a.length; i++) List.filled(b.length + 1, 0)];
  for (var i = 0; i <= a.length; i++) {
    for (var j = 0; j <= b.length; j++) {
      d[i][j] = i == 0
          ? j
          : j == 0
          ? i
          : [
              d[i - 1][j] + 1,
              d[i][j - 1] + 1,
              d[i - 1][j - 1] + (a[i - 1] == b[j - 1] ? 0 : 1),
            ].reduce(math.min);
    }
  }
  return d[a.length][b.length];
}

void main(List<String> args) {
  for (final line in readLines(args[0])) {
    final w = line.split(' ');
    final a = w[0];
    final b = w.length > 1 ? w[1] : '';
    final (ca, cb) = (a.runes.toList(), b.runes.toList());
    print('$a $b ${topDown(ca, cb)} ${bottomUp(ca, cb)}');
  }
}
