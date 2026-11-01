/// Step L1.14: name resolution. A bare name resolves in its block scopes, innermost outward,
/// then in the unit's top level, then in the prelude; one test per rule of that order, and one
/// per error a resolution reports.
library;

import 'dart:convert';

import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';
import 'package:zed/resolve.dart';

/// The statements of the unit `text`.
List<Stmt> stmtsOf(String text) {
  final tokens = lexFence(text);
  return unit(text, tokens, parse(text, tokens, 'Unit', top));
}

/// The resolution of the unit `text`; throws [ResolveErrors].
Resolution run(String text) => resolve(stmtsOf(text));

/// The text of `span` in `text`.
String slice(String text, Span span) =>
    utf8.decode(utf8.encode(text).sublist(span.start, span.end));

final _word = RegExp(r'[\p{L}\p{N}_]', unicode: true);

/// What the `n`-th (from 0) occurrence of the name `name` in `text` resolves to: the text and
/// kind of each binder, or the prelude word.
List<String> at(String text, String name, int n) {
  final r = run(text);
  bool ok(int i) => i < 0 || i >= text.length || !_word.hasMatch(text[i]);
  final starts = [
    for (final m in name.allMatches(text))
      if (ok(m.start - 1) && ok(m.end)) utf8.encode(text.substring(0, m.start)).length,
  ];
  if (n >= starts.length) throw StateError('no occurrence $n of `$name`');
  final used = [
    for (final (key, value) in r.uses.entries)
      if (key.start == starts[n]) value,
  ];
  if (used.isEmpty) throw StateError('occurrence $n of `$name` is not a recorded use');
  return switch (used.first) {
    Prelude(:final word) => ['prelude $word'],
    Bound(:final binders) => [for (final b in binders) '${b.kind.name} ${slice(text, b.span)}'],
  };
}

/// The errors of the unit `text`, each `message [text]`, each note after it as `; note [text]`.
List<String> errors(String text) {
  try {
    run(text);
  } on ResolveErrors catch (e) {
    return [
      for (final x in e.errors)
        '${x.message} [${slice(text, x.span)}]'
            '${[for (final note in x.notes) '; ${note.text} [${slice(text, note.span)}]'].join()}',
    ];
  }
  throw StateError('$text resolves');
}
