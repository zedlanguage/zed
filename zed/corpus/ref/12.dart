/// 12 CYK over the bracket grammar, transcribed from the program, checked against a direct
/// balanced-bracket test on every substring. Characters are code points.
library;

import 'zedrt.dart';

const open = 0x28, close = 0x29; // '(' and ')'

bool balanced(List<int> s) {
  var d = 0;
  for (final c in s) {
    d += c == open
        ? 1
        : c == close
        ? -1
        : 0;
    if (d < 0 || (c != open && c != close)) return false;
  }
  return d == 0 && s.isNotEmpty;
}

typedef Cell = (bool, bool, bool, bool);

/// The cell of a split into a left part x and a right part y.
Cell join(Cell x, Cell y) => (x.$3 && (y.$4 || y.$2) || x.$1 && y.$1, x.$1 && y.$4, false, false);

Cell or(Cell a, Cell b) => (a.$1 || b.$1, a.$2 || b.$2, a.$3 || b.$3, a.$4 || b.$4);

/// t[w][i] for the substring of width w starting at i.
List<List<Cell>> cyk(List<int> s) {
  final n = s.length;
  final t = <List<Cell>>[[]];
  for (var w = 1; w <= n; w++) {
    t.add([
      for (var i = 0; i <= n - w; i++)
        if (w == 1)
          (false, false, s[i] == open, s[i] == close)
        else
          [for (var k = 1; k < w; k++) join(t[k][i], t[w - k][i + k])]
              .fold((false, false, false, false), or),
    ]);
  }
  return t;
}

void main(List<String> args) {
  for (final line in readLines(args[0])) {
    final s = line.runes.toList();
    final t = cyk(s);
    final whole = s.isNotEmpty && t[s.length][0].$1;
    final count = t.expand((row) => row).where((v) => v.$1).length;
    var direct = 0;
    for (var w = 1; w <= s.length; w++) {
      for (var i = 0; i <= s.length - w; i++) {
        if (balanced(s.sublist(i, i + w))) direct++;
      }
    }
    if (whole != balanced(s) || count != direct) throw StateError('CYK disagrees: $line');
    print('${whole ? 'balanced' : 'unbalanced'} $count $line');
  }
}
