/// 24 weighted pick: least i with cumul[i] > q, by bisect_right on the prefix sums (the
/// program's binary search must agree), or none when q >= total. bisectRight is Python's
/// bisect.bisect_right, step for step, so a negative weight gives the same answer too.
library;

import 'zedrt.dart';

int bisectRight(List<BigInt> a, BigInt x) {
  var (lo, hi) = (0, a.length);
  while (lo < hi) {
    final mid = (lo + hi) ~/ 2;
    if (x < a[mid]) {
      hi = mid;
    } else {
      lo = mid + 1;
    }
  }
  return lo;
}

void main(List<String> args) {
  final ls = readLines(args[0]);
  final w = [for (final x in ls[0].split(' ')) parseInt(x)];
  final cumul = <BigInt>[];
  for (final x in w) {
    cumul.add((cumul.isEmpty ? BigInt.zero : cumul.last) + x);
  }
  final total = cumul.isEmpty ? BigInt.zero : cumul.last;
  for (final l in ls.skip(1)) {
    final q = parseInt(l);
    print(q >= total ? '$q none' : '$q ${bisectRight(cumul, q)}');
  }
}
