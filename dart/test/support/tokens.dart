/// Tokens as text, for expected output: a keyword in `«»`, an integer with its base, a string
/// as its parts.
library;

import 'dart:convert';

import 'package:zed/lex.dart';
import 'package:zed/src/unicode.dart';

/// `tokens` on one line.
String render(List<Token> tokens) => tokens.map((t) => _one(t.tok)).join(' ');

/// `tokens` of `text`, one rendered line per line of `text` that starts a token, each after its
/// line number; a token belongs to the line it starts on. Spans are byte offsets, and `tokens`
/// are in order.
String renderLines(String text, List<Token> tokens) {
  final out = <String>[];
  var (start, next) = (0, 0);
  for (final (k, line) in text.split('\n').indexed) {
    final end = start + utf8.encode(line).length + 1;
    final first = next;
    while (next < tokens.length && tokens[next].span.start < end) {
      next++;
    }
    if (next > first) out.add('${'${k + 1}'.padLeft(3)} | ${render(tokens.sublist(first, next))}');
    start = end;
  }
  return out.join('\n');
}

String _one(Tok tok) => switch (tok) {
  Name(:final text) => text,
  Wildcard() => '_',
  Keyword(:final word) => '«$word»',
  Op(:final op) => op,
  Atom(:final name) => '#$name',
  Annot(:final name) => '@$name',
  Int(:final radix, :final digits) => '$digits₍$radix₎',
  Float(:final text) => '${text}f',
  Rat(:final text) => '${text}r',
  Str(:final parts) =>
    'str[${parts.map((p) => switch (p) {
      TextPart(:final text) => quoted(text, '"'),
      Hole(:final tokens) => '\${${render(tokens)}}',
    }).join(' ')}]',
};
