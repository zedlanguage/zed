/// 23 join zoo. Keys in int order; a missing side prints '-'; amounts per id are summed (group
/// then sum). Output order: the four join blocks, then the difference lines, then the
/// range-split check.
library;

import 'zedrt.dart';

void main(List<String> args) {
  final o = <BigInt, BigInt>{}, p = <BigInt, BigInt>{};
  for (final l in readLines(args[0])) {
    final [s, i, n] = l.split(' ');
    final (key, amount) = (parseInt(i), parseInt(n));
    (s == 'O' ? o : p).update(key, (v) => v + amount, ifAbsent: () => amount);
  }
  String g(Map<BigInt, BigInt> d, BigInt k) => d[k]?.toString() ?? '-';
  List<BigInt> sorted(Iterable<BigInt> ks) => ks.toList()..sort();
  for (final k in sorted(o.keys)) {
    if (p.containsKey(k)) print('inner $k ${o[k]} ${p[k]}');
  }
  for (final k in sorted(o.keys)) {
    print('left $k ${o[k]} ${g(p, k)}');
  }
  for (final k in sorted(p.keys)) {
    print('right $k ${g(o, k)} ${p[k]}');
  }
  for (final k in sorted({...o.keys, ...p.keys})) {
    print('outer $k ${g(o, k)} ${g(p, k)}');
  }
  final onlyL = sorted(o.keys.where((k) => !p.containsKey(k)));
  final onlyR = sorted(p.keys.where((k) => !o.containsKey(k)));
  print('unpaid ${onlyL.join(' ')}');
  print('unordered ${onlyR.join(' ')}');
  print('symdiff ${sorted([...onlyL, ...onlyR]).join(' ')}');
  final ten = BigInt.from(10);
  final low = {
    for (final MapEntry(:key, :value) in o.entries)
      if (key < ten) key: value,
  };
  final high = {
    for (final MapEntry(:key, :value) in o.entries)
      if (key >= ten) key: value,
  };
  final rejoined = {...low, ...high};
  final equal = rejoined.length == o.length && rejoined.entries.every((e) => o[e.key] == e.value);
  print('rejoined ${equal ? 'equal' : 'different'}');
}
