/// 05 maximum prefix sum: max(0, max of prefix sums), the fold with state (sum, best) started
/// at (0, 0), and the total.
library;

import 'zedrt.dart';

void main(List<String> args) {
  final xs = [for (final l in readLines(args[0])) parseInt(l)];
  final pre = <BigInt>[];
  var s = BigInt.zero;
  for (final x in xs) {
    s += x;
    pre.add(s);
  }
  final direct = maxBig(BigInt.zero, pre.fold(BigInt.zero, maxBig));
  var (sum, best) = (BigInt.zero, BigInt.zero);
  for (final x in xs) {
    (sum, best) = (sum + x, maxBig(best, sum + x));
  }
  print('$direct $best $sum');
}
