/// Step L1.5: string literals, their escapes, `"""` indentation stripping, and `${…}` holes
/// split into parts, each hole lexed into its tokens.
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';
import 'package:zed/src/unicode.dart';

/// The parts of the one string in `text`.
List<Part> stringParts(String text) => switch (lex(text)) {
  [(tok: Str(:final parts), span: _)] => parts,
  final toks => fail('${quoted(text, '"')}: $toks'),
};

/// The parts of the one string in `text`, a hole shown as `${` its tokens `}`.
List<String> parts(String text) => [
  for (final p in stringParts(text))
    switch (p) {
      TextPart(:final text) => text,
      Hole(:final tokens) => '\${${tokens.map((t) => t.tok).join(' ')}}',
    },
];

/// The one text part of the string in `text`, or `""` for an empty string.
String text(String text) {
  final p = parts(text);
  expect(p.length, lessThanOrEqualTo(1), reason: '${quoted(text, '"')}: $p');
  return p.isEmpty ? '' : p.single;
}

/// The error lexing each of `cases`, each case quoted and its error's span and message
/// indented on the next line.
String malformed(List<String> cases) => [
  for (final c in cases)
    switch (() {
      try {
        lex(c);
      } on LexError catch (e) {
        return e;
      }
      fail('${quoted(c, '"')} lexed');
    }()) {
      final e => '${quoted(c, '"')}\n    [${e.span.start}..${e.span.end}] $e',
    },
].join('\n');
