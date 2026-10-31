/// 26 heat stencil. Zed rule used: div is Euclidean; the divisor here is 4 (positive), where
/// Euclidean div equals floor division (zedrt.floorDiv).
library;

import 'zedrt.dart';

void main(List<String> args) {
  final ls = readLines(args[0]);
  final steps = parseInt(ls[0]).toInt();
  final u = [
    [for (final x in ls[1].split(' ')) parseInt(x)],
  ];
  final n = u[0].length;
  final (two, four) = (BigInt.two, BigInt.from(4));
  for (var t = 1; t <= steps; t++) {
    final p = u.last;
    u.add([
      for (var i = 0; i < n; i++)
        i == 0 || i == n - 1 ? p[i] : p[i] + floorDiv(p[i - 1] - two * p[i] + p[i + 1], four),
    ]);
  }
  for (final t in [0, 1, 2, steps]) {
    print('t=$t: ${u[t].join(' ')}');
  }
}
