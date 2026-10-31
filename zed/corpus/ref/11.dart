/// 11 CSV fields by a three-state quote machine, run serially (the reference for the scan of
/// transition tables). A comma separates when the state before it is not 1 (inside quotes);
/// fields are the text between separators.
library;

import 'zedrt.dart';

const quoteNext = [1, 2, 1]; // after '"', by state
const otherNext = [0, 1, 0]; // after any other character

void main(List<String> args) {
  for (final line in readLines(args[0])) {
    final cs = line.runes.toList();
    var st = 0;
    final before = <int>[];
    for (final c in cs) {
      before.add(st);
      st = (c == 0x22 ? quoteNext : otherNext)[st];
    }
    final seps = [
      for (final (i, c) in cs.indexed)
        if (c == 0x2C && before[i] != 1) i,
    ];
    final cuts = [-1, ...seps, cs.length];
    final fs = [
      for (var k = 0; k < cuts.length - 1; k++) String.fromCharCodes(cs, cuts[k] + 1, cuts[k + 1]),
    ];
    print('${fs.length} ${fs.map((f) => '[$f]').join(' ')}');
  }
}
