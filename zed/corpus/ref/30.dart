/// 30 client/server, run as one process. The struct grammars are phrase level: whitespace
/// between elements is skipped. A parse failure reports the farthest position any
/// alternative reached (the same assumption as 07). serialize writes the elements with no
/// whitespace. Positions are code-point offsets; item names are ASCII letters and
/// quantities ASCII digits.
library;

import 'dart:math' as math;

import 'zedrt.dart';

const prices = {'apple': 3, 'pear': 5, 'plum': 2};

typedef Request = ({String kind, String item, String? qty});

bool isLetter(int c) => (c >= 0x41 && c <= 0x5A) || (c >= 0x61 && c <= 0x7A);

bool isAsciiDigit(int c) => c >= 0x30 && c <= 0x39;

/// The request on line [s], or the farthest failure position.
Object parse(String line) {
  final s = line.runes.toList();
  int ws(int i) {
    while (i < s.length && (s[i] == 0x20 || s[i] == 0x09)) {
      i++;
    }
    return i;
  }

  /// After whitespace from [i]: the end and start of a nonempty run of [ok] characters, or
  /// null and the start.
  (int?, int) run(int i, bool Function(int) ok) {
    i = ws(i);
    var j = i;
    while (j < s.length && ok(s[j])) {
      j++;
    }
    return (j > i ? j : null, i);
  }

  String text(int i, int j) => String.fromCharCodes(s, i, j);
  var far = 0;
  for (final kind in const ['get', 'buy']) {
    final at0 = ws(0);
    if (at0 + 3 > s.length || text(at0, at0 + 3) != kind) {
      far = math.max(far, at0);
      continue;
    }
    final (itemEnd, itemAt) = run(at0 + 3, isLetter);
    if (itemEnd == null) {
      far = math.max(far, itemAt);
      continue;
    }
    var j = itemEnd;
    String? qty;
    if (kind == 'buy') {
      final (qtyEnd, qtyAt) = run(j, isAsciiDigit);
      if (qtyEnd == null) {
        far = math.max(far, qtyAt);
        continue;
      }
      qty = text(qtyAt, qtyEnd);
      j = qtyEnd;
    }
    j = ws(j);
    if (j != s.length) {
      far = math.max(far, j);
      continue;
    }
    return (kind: kind, item: text(itemAt, itemEnd), qty: qty);
  }
  return far;
}

void main(List<String> args) {
  for (final l in readLines(args[0])) {
    switch (parse(l)) {
      case final Request r:
        final (:kind, :item, :qty) = r;
        final q = kind == 'get' ? BigInt.one : parseInt(qty!);
        print(switch (prices[item]) {
          final p? => '$item=${BigInt.from(p) * q}',
          null => 'missing:$item',
        });
      case final int far:
        print('bad request at $far');
    }
  }
}
