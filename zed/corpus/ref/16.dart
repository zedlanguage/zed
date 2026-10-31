/// 16 game tick: per tick, each player's moves are summed first (the reducer's coalescing),
/// then applied once and clamped to 0..=10. Players start at 5 and are listed in name order;
/// one line per tick 0..=last.
library;

import 'zedrt.dart';

void main(List<String> args) {
  final evs = [
    for (final l in readLines(args[0]))
      switch (l.split(' ')) {
        [final t, final p, final dx] => (parseInt(t), p, parseInt(dx)),
        _ => throw FormatException('not "tick player dx"', l),
      },
  ];
  final moves = <(BigInt, String), BigInt>{};
  for (final (t, p, dx) in evs) {
    moves.update((t, p), (m) => m + dx, ifAbsent: () => dx);
  }
  final players = sortedByCodePoint({for (final (_, p, _) in evs) p});
  final last = evs.map((e) => e.$1).fold(BigInt.from(-1), maxBig);
  final ten = BigInt.from(10);
  var pos = {for (final p in players) p: BigInt.from(5)};
  for (var t = BigInt.zero; t <= last; t += BigInt.one) {
    pos = {
      for (final MapEntry(key: p, value: x) in pos.entries)
        p: minBig(ten, maxBig(BigInt.zero, x + (moves[(t, p)] ?? BigInt.zero))),
    };
    print('$t ${players.map((p) => '$p=${pos[p]}').join(' ')}');
  }
}
