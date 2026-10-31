/// Step L1.12: declarations, namely functions in equation and block form with their `test`
/// tables, `main`'s port header, the whole-value push `p <- e`, and `if`/`else`.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

/// The statements of the unit `text`, one s-expression per line, or its error: `error: …` with
/// each note and its byte, or `syntax` when it does not parse.
String sx(String text) {
  final tokens = lex(text);
  final Tree tree;
  try {
    tree = parse(text, tokens, 'Unit', top);
  } on ParseError {
    return 'syntax';
  }
  try {
    return unit(text, tokens, tree).join('\n');
  } on BuildError catch (e) {
    return 'error: $e${[for (final n in e.notes) '; ${n.text} at byte ${n.span.start}'].join()}';
  }
}

/// Checks each case's text against its s-expression, reporting every one that differs.
void check(List<(String, String)> cases) {
  final wrong = [
    for (final (text, want) in cases)
      if (sx(text) case final got when got != want) '$text\n  got  $got\n  want $want',
  ];
  expect(wrong, isEmpty, reason: wrong.join('\n'));
}
