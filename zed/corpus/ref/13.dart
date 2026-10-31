/// 13 connectivity by a classic union-find (path halving, union by size): the reference the
/// library's certified path must agree with. Node count is max node id on an edge + 1; a
/// queried node outside that range is alone. A negative node id counts from the end, as a
/// Python list index does (-1 is node count - 1); below -node count it is an error.
library;

import 'zedrt.dart';

void main(List<String> args) {
  final edges = <(BigInt, BigInt)>[], qs = <(BigInt, BigInt)>[];
  for (final l in readLines(args[0])) {
    final w = l.split(' ');
    if (w[0] == '?') {
      qs.add((parseInt(w[1]), parseInt(w[2])));
    } else {
      edges.add((parseInt(w[0]), parseInt(w[1])));
    }
  }
  final nBig = edges.map((e) => maxBig(e.$1, e.$2)).fold(BigInt.from(-1), maxBig) + BigInt.one;
  final n = nBig.toInt();
  final parent = List.generate(n, (i) => i), size = List.filled(n, 1);

  int index(BigInt x) {
    final i = x.isNegative ? x + nBig : x;
    if (i.isNegative || i >= nBig) throw RangeError.range(x.toInt(), -n, n - 1, 'node');
    return i.toInt();
  }

  int find(int x) {
    while (parent[x] != x) {
      parent[x] = parent[parent[x]];
      x = parent[x];
    }
    return x;
  }

  for (final (a, b) in edges) {
    var (ra, rb) = (find(index(a)), find(index(b)));
    if (ra != rb) {
      if (size[ra] < size[rb]) (ra, rb) = (rb, ra);
      parent[rb] = ra;
      size[ra] += size[rb];
    }
  }
  (bool, BigInt) root(BigInt x) => x < nBig ? (false, BigInt.from(find(index(x)))) : (true, x);
  for (final (a, b) in qs) {
    print('$a $b ${root(a) == root(b) ? 'yes' : 'no'}');
  }
  print('components ${{for (var v = 0; v < n; v++) find(v)}.length}');
}
