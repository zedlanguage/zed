/// Step L1.13: the source formatter. What it writes parses to the same statements and formats
/// to itself, and keeps every comment.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/format.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

/// The tokens of the unit `text` and its statements; throws when it does not build.
(List<Token>, List<Stmt>) build(String text) {
  final tokens = lexFence(text);
  return (tokens, unit(text, tokens, parse(text, tokens, 'Unit', top)));
}

/// The comments of `text`, sorted.
List<String> commentTexts(String text, List<Token> tokens) {
  final bytes = utf8.encode(text);
  return [for (final c in comments(text, tokens)) utf8.decode(bytes.sublist(c.start, c.end))]
    ..sort();
}

/// `text` formatted, after checking that the result builds to the same statements (their
/// s-expressions, which hold no spans), keeps the same comments, and formats to itself.
String fmt(String text) {
  final (tokens, stmts) = build(text);
  final out = format(text, tokens, stmts);
  final (tokens2, stmts2) = build(out);
  expect(stmts2.join('\n'), stmts.join('\n'), reason: 'the statements changed in\n$out');
  expect(commentTexts(out, tokens2), commentTexts(text, tokens));
  expect(format(out, tokens2, stmts2), out, reason: 'not a fixed point');
  return out;
}
