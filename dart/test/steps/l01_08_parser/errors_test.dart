/// A text that does not parse is reported at the furthest token any alternative reached, with
/// what the grammar expected there.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';
import 'package:zed/src/unicode.dart';

import '../../support/support.dart';

String report(String text) {
  try {
    parse(text, lex(text), 'Unit', top);
  } on ParseError catch (e) {
    final bytes = utf8.encode(text);
    final line = bytes.sublist(0, e.span.start).where((b) => b == 0x0a).length + 1;
    final at = utf8.decode(bytes.sublist(e.span.start, e.span.end));
    return '${quoted(text, '"')}\n  line $line, at ${quoted(at, '"')}: $e';
  }
  fail('$text parses');
}

void main() {
  test('errors', () {
    expectOutput(
      'l01_08_parser',
      'errors',
      [
        'total = price * ;',
        'discount = if member { 0.1 }; // `if` needs its `else`',
        'area(w, h) = w * h\nmain = area(2, 3);',
        'xs = [1, 2, 3;',
        'p = Point(x: 1 y: 2);',
        // `\` cannot follow a `|` union, so it is not expected here (`TypeUnion`)
        'type Bound = int | #unbounded\nlimit: Bound = 10;',
      ].map(report).join('\n'),
    );
  });
}
