/// 14 single-linkage clustering to k clusters, recomputing all pairs each step: the closest
/// pair of points in different clusters, ties broken by (distance², smaller label, larger
/// label) in natural tuple order; the larger label is renamed to the smaller. n - k merges
/// (none if k >= n).
library;

import 'dart:math' as math;

import 'zedrt.dart';

typedef Pair = (BigInt, int, int);

int compare(Pair x, Pair y) => switch (x.$1.compareTo(y.$1)) {
  0 => x.$2 != y.$2 ? x.$2 - y.$2 : x.$3 - y.$3,
  final c => c,
};

void main(List<String> args) {
  final lines = readLines(args[0]);
  final k = parseInt(lines[0]);
  final pts = [
    for (final l in lines.skip(1)) [for (final t in l.split(' ')) parseInt(t)],
  ];
  var label = List.generate(pts.length, (i) => i);
  final merges = maxBig(BigInt.zero, BigInt.from(pts.length) - k).toInt();
  for (var step = 0; step < merges; step++) {
    Pair? best;
    for (var i = 0; i < pts.length; i++) {
      for (var j = 0; j < pts.length; j++) {
        if (i < j && label[i] != label[j]) {
          final dx = pts[i][0] - pts[j][0], dy = pts[i][1] - pts[j][1];
          final Pair cand = (
            dx * dx + dy * dy,
            math.min(label[i], label[j]),
            math.max(label[i], label[j]),
          );
          if (best == null || compare(cand, best) < 0) best = cand;
        }
      }
    }
    if (best == null) throw StateError('min() of no pairs');
    final (_, a, b) = best;
    label = [for (final l in label) l == b ? a : l];
  }
  for (final c in label.toSet().toList()..sort()) {
    final members = [
      for (final (i, l) in label.indexed)
        if (l == c) i,
    ];
    print('$c: ${members.join(' ')}');
  }
}
