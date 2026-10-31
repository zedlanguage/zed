/// The syntax tree of an expression, parsed at the top ring.
library;

import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

/// The syntax tree of the expression `text`, parsed at the top ring.
Expr ast(String text) {
  final tokens = lex(text);
  return build(text, tokens, parse(text, tokens, 'Expr', top));
}

/// The error building the expression `text`.
BuildError astError(String text) {
  try {
    throw StateError('$text builds: ${ast(text)}');
  } on BuildError catch (e) {
    return e;
  }
}
