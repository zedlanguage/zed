/// Parse trees printed as the bracketing cases of `tools/grammar/cases.txt` print them.
library;

import 'dart:convert';

import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

/// The s-expression of `tree`, parsed from `tokens` of `text`: a node is its tokens, with
/// each child bracketed in its place, and a node with one child spanning all of it is that
/// child; a node with no child is its tokens' texts.
String sx(String text, List<Token> tokens, Tree tree) {
  final bytes = utf8.encode(text);
  final words = [for (final t in tokens) utf8.decode(bytes.sublist(t.span.start, t.span.end)), ''];
  return _node(tree.root, words);
}

String _node(Node n, List<String> words) {
  if (n.kids.isEmpty) return words.sublist(n.start, n.end).join(' ');
  if (n.kids case [final k] when k.start == n.start && k.end == n.end) return _node(k, words);
  final parts = <String>[];
  var pos = n.start;
  for (final k in n.kids) {
    parts
      ..addAll(words.sublist(pos, k.start))
      ..add(_node(k, words));
    pos = k.end;
  }
  parts.addAll(words.sublist(pos, n.end));
  return '(${parts.join(' ')})';
}
