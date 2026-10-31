/// 27 parent chains: root and depth per node, nodes in code-point order.
library;

import 'zedrt.dart';

void main(List<String> args) {
  final par = <String, String>{};
  for (final l in readLines(args[0])) {
    final [c, p] = l.split(' ');
    par.putIfAbsent(c, () => p); // group then first: the first line for a child wins
  }
  for (final v in sortedByCodePoint(par.keys)) {
    var (r, d) = (v, 0);
    while ((par[r] ?? '-') != '-') {
      (r, d) = (par[r]!, d + 1);
    }
    print('$v $r $d');
  }
}
