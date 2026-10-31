/// The s-expression of an expression, or why it has none.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

/// The s-expression of the expression `text`, or its error: `error: …`, or `syntax` when it
/// does not parse.
String sx(String text) {
  final tokens = lex(text);
  final Tree tree;
  try {
    tree = parse(text, tokens, 'Expr', top);
  } on ParseError {
    return 'syntax';
  }
  try {
    return '${build(text, tokens, tree)}';
  } on BuildError catch (e) {
    return 'error: $e';
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
