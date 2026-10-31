/// 07 JSON parser. Implements the grammar of 07-json-parser/json.zed with the Zed rules this
/// output depends on:
/// - struct grammars skip whitespace (space, tab) between elements; token types (JsonStr,
///   JsonNum, JsonLit) are exact; nothing is skipped before the first element or after the
///   document's end, which must be the end of the line;
/// - union alternatives are tried in declared order (they are disjoint by their first
///   character, so the choice rule picks the only match);
/// - X* sep "," is zero or more X separated by ",", no trailing separator;
/// - serialize writes the matched text of every token and the literal scaffolding, with no
///   whitespace;
/// - the #syntaxError position is the farthest code-point offset at which the parse failed,
///   after skipping whitespace (an assumption; see LEDGER.md).
/// A JsonNum digit is any character with a Numeric_Type of Decimal or Digit (zedrt.isDigit);
/// a JsonStr character is an ASCII letter or digit, or a
/// space.
library;

import 'dart:math' as math;

import 'zedrt.dart';

/// A parse result: the offset after the match, and the serialized text.
typedef Parsed = (int, String);

class Parser {
  Parser(String line) : s = line.runes.toList();

  final List<int> s;
  var far = 0;

  /// Records a failure at [i]; every failing parse returns null after calling it.
  Null fail(int i) {
    far = math.max(far, i);
    return null;
  }

  int ws(int i) {
    while (i < s.length && (s[i] == 0x20 || s[i] == 0x09)) {
      i++;
    }
    return i;
  }

  bool startsWith(String t, int i) {
    final cs = t.codeUnits; // t is ASCII
    if (i + cs.length > s.length) return false;
    for (var k = 0; k < cs.length; k++) {
      if (s[i + k] != cs[k]) return false;
    }
    return true;
  }

  String text(int i, int j) => String.fromCharCodes(s, i, j);

  int? lit(int i, String t) => startsWith(t, i) ? i + t.length : fail(i);

  Parsed? json(int i) => obj(i) ?? arr(i) ?? str(i) ?? num(i) ?? kw(i) ?? fail(i);

  (int, List<String>)? sepList(int i, Parsed? Function(int) item, String close) {
    final out = <String>[];
    if (item(ws(i)) case (final j, final v)) {
      out.add(v);
      i = j;
      while (true) {
        final comma = lit(ws(i), ',');
        if (comma == null) break;
        final next = item(ws(comma));
        if (next == null) break;
        out.add(next.$2);
        i = next.$1;
      }
    }
    final end = lit(ws(i), close);
    return end == null ? null : (end, out);
  }

  Parsed? kv(int i) {
    if (str(i) case (final j, final k)) {
      if (lit(ws(j), ':') case final colon?) {
        if (json(ws(colon)) case (final end, final v)) return (end, '$k:$v');
      }
    }
    return null;
  }

  Parsed? obj(int i) => switch (lit(i, '{')) {
    final open? => switch (sepList(open, kv, '}')) {
      (final end, final es) => (end, '{${es.join(',')}}'),
      null => null,
    },
    null => null,
  };

  Parsed? arr(int i) => switch (lit(i, '[')) {
    final open? => switch (sepList(open, json, ']')) {
      (final end, final es) => (end, '[${es.join(',')}]'),
      null => null,
    },
    null => null,
  };

  Parsed? str(int i) {
    var j = lit(i, '"');
    if (j == null) return null;
    while (j! < s.length && (_isAsciiAlnum(s[j]) || s[j] == 0x20)) {
      j++;
    }
    j = lit(j, '"');
    return j == null ? null : (j, text(i, j));
  }

  Parsed? num(int i) {
    final j = startsWith('-', i) ? i + 1 : i;
    var k = j;
    while (k < s.length && isDigit(s[k])) {
      k++;
    }
    if (k == j) return fail(k);
    if (startsWith('.', k)) {
      var m = k + 1;
      while (m < s.length && isDigit(s[m])) {
        m++;
      }
      if (m > k + 1) {
        k = m;
      } else {
        far = math.max(far, k + 1);
      }
    }
    return (k, text(i, k));
  }

  Parsed? kw(int i) {
    for (final w in const ['true', 'false', 'null']) {
      if (startsWith(w, i)) return (i + w.length, w);
    }
    return fail(i);
  }
}

bool _isAsciiAlnum(int c) =>
    (c >= 0x30 && c <= 0x39) || (c >= 0x41 && c <= 0x5A) || (c >= 0x61 && c <= 0x7A);

void main(List<String> args) {
  for (final line in readLines(args[0])) {
    final p = Parser(line);
    switch (p.json(0)) {
      case (final end, final v) when end == p.s.length:
        print(v);
      case (final end, _):
        p.fail(end);
        print('error at ${p.far}');
      case null:
        print('error at ${p.far}');
    }
  }
}
