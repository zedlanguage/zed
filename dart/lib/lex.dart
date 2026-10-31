/// The lexer (DESIGN.md sec:lexical, its lexical grammar; steps L1.2–L1.6): the loaded text
/// (`source.dart`) becomes tokens, each with its span, a byte range of that text.
///
/// Tokens are read by ordered choice, as the lexical grammar orders them. A character no rule
/// reads is an error at that character, and lexing stops there.
library;

import 'source.dart';
import 'src/lex/comment.dart';
import 'src/lex/name.dart';
import 'src/lex/number.dart';
import 'src/lex/punct.dart';
import 'src/lex/string.dart';
import 'src/lex/text.dart';
import 'src/unicode.dart';

export 'source.dart' show Span;
export 'src/lex/name.dart' show isSingleScript;
export 'src/lex/punct.dart' show keywords, operators;

/// A token's kind and the value it carries.
sealed class Tok {
  const Tok();
}

/// A name, with its trailing `'` when it has one (`x'`).
final class Name extends Tok {
  final String text;

  const Name(this.text);

  @override
  bool operator ==(Object other) => other is Name && other.text == text;

  @override
  int get hashCode => text.hashCode;

  @override
  String toString() => 'Name(${quoted(text, '"')})';
}

/// The discard wildcard `_`.
final class Wildcard extends Tok {
  const Wildcard();

  @override
  bool operator ==(Object other) => other is Wildcard;

  @override
  int get hashCode => 0;

  @override
  String toString() => 'Wildcard';
}

/// An integer: its base (2, 8, 10 or 16) and its digits, without `_`.
final class Int extends Tok {
  final int radix;
  final String digits;

  const Int(this.radix, this.digits);

  @override
  bool operator ==(Object other) => other is Int && other.radix == radix && other.digits == digits;

  @override
  int get hashCode => Object.hash(radix, digits);

  @override
  String toString() => 'Int { radix: $radix, digits: ${quoted(digits, '"')} }';
}

/// A float, as its decimal text without `_` (`1.5e-3`).
final class Float extends Tok {
  final String text;

  const Float(this.text);

  @override
  bool operator ==(Object other) => other is Float && other.text == text;

  @override
  int get hashCode => text.hashCode;

  @override
  String toString() => 'Float(${quoted(text, '"')})';
}

/// An exact rational, as its decimal text without `_` and the `r` (`0.1`).
final class Rat extends Tok {
  final String text;

  const Rat(this.text);

  @override
  bool operator ==(Object other) => other is Rat && other.text == text;

  @override
  int get hashCode => text.hashCode;

  @override
  String toString() => 'Rat(${quoted(text, '"')})';
}

/// A string: its text and its holes, in order, never two text parts in a row.
final class Str extends Tok {
  final List<Part> parts;

  const Str(this.parts);

  @override
  bool operator ==(Object other) => other is Str && _same(other.parts, parts);

  @override
  int get hashCode => Object.hashAll(parts);

  @override
  String toString() => 'Str($parts)';
}

/// An atom `#name`, without the `#`.
final class Atom extends Tok {
  final String name;

  const Atom(this.name);

  @override
  bool operator ==(Object other) => other is Atom && other.name == name;

  @override
  int get hashCode => name.hashCode;

  @override
  String toString() => 'Atom(${quoted(name, '"')})';
}

/// An annotation `@name`, without the `@`.
final class Annot extends Tok {
  final String name;

  const Annot(this.name);

  @override
  bool operator ==(Object other) => other is Annot && other.name == name;

  @override
  int get hashCode => name.hashCode;

  @override
  String toString() => 'Annot(${quoted(name, '"')})';
}

/// A keyword.
final class Keyword extends Tok {
  final String word;

  const Keyword(this.word);

  @override
  bool operator ==(Object other) => other is Keyword && other.word == word;

  @override
  int get hashCode => word.hashCode;

  @override
  String toString() => 'Keyword(${quoted(word, '"')})';
}

/// An operator or punctuation mark.
final class Op extends Tok {
  final String op;

  const Op(this.op);

  @override
  bool operator ==(Object other) => other is Op && other.op == op;

  @override
  int get hashCode => op.hashCode;

  @override
  String toString() => 'Op(${quoted(op, '"')})';
}

/// A doc comment: its text after `///` and one space, and its span, from the first `/` to the
/// end of the line.
typedef Doc = ({String text, Span span});

/// A part of a string literal.
sealed class Part {
  const Part();
}

/// Text, with its escapes decoded and, in a `"""` string, its indentation stripped.
final class TextPart extends Part {
  final String text;

  const TextPart(this.text);

  @override
  bool operator ==(Object other) => other is TextPart && other.text == text;

  @override
  int get hashCode => text.hashCode;

  @override
  String toString() => 'Text(${quoted(text, '"')})';
}

/// A `${…}` hole: the tokens between `${` and `}`, and the span from `$` to `}`.
final class Hole extends Part {
  final List<Token> tokens;
  final Span span;

  const Hole(this.tokens, this.span);

  @override
  bool operator ==(Object other) =>
      other is Hole && other.span == span && _same(other.tokens, tokens);

  @override
  int get hashCode => Object.hash(span, Object.hashAll(tokens));

  @override
  String toString() => 'Hole { tokens: $tokens, span: $span }';
}

/// A token and its span.
typedef Token = ({Tok tok, Span span});

bool _same<T>(List<T> a, List<T> b) {
  if (a.length != b.length) return false;
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

/// Why lexing stopped.
sealed class ErrorKind {
  const ErrorKind();
}

/// A character, the code point `char`, that starts no token.
final class Unexpected extends ErrorKind {
  final int char;

  const Unexpected(this.char);

  @override
  bool operator ==(Object other) => other is Unexpected && other.char == char;

  @override
  int get hashCode => char;
}

/// A name whose characters are not all of one script (UTS #39, "Highly Restrictive").
final class MixedScript extends ErrorKind {
  final String name;

  const MixedScript(this.name);

  @override
  bool operator ==(Object other) => other is MixedScript && other.name == name;

  @override
  int get hashCode => name.hashCode;
}

/// A malformed number, and what is wrong with it.
final class BadNumber extends ErrorKind {
  final String why;

  const BadNumber(this.why);

  @override
  bool operator ==(Object other) => other is BadNumber && other.why == why;

  @override
  int get hashCode => why.hashCode;
}

/// A malformed string, and what is wrong with it.
final class BadString extends ErrorKind {
  final String why;

  const BadString(this.why);

  @override
  bool operator ==(Object other) => other is BadString && other.why == why;

  @override
  int get hashCode => why.hashCode;
}

/// A block comment that is not closed.
final class BadComment extends ErrorKind {
  final String why;

  const BadComment(this.why);

  @override
  bool operator ==(Object other) => other is BadComment && other.why == why;

  @override
  int get hashCode => why.hashCode;
}

/// A lexical error and its span.
final class LexError implements Exception {
  final ErrorKind kind;
  final Span span;

  const LexError(this.kind, this.span);

  @override
  String toString() => switch (kind) {
    Unexpected(:final char) =>
      'no token starts with ${quoted(String.fromCharCode(char), "'")} '
          '(U+${char.toRadixString(16).toUpperCase().padLeft(4, '0')})',
    BadNumber(:final why) => 'malformed number: $why',
    BadString(:final why) => 'malformed string: $why',
    BadComment(:final why) => why,
    MixedScript(:final name) => 'the name ${quoted(name, '"')} mixes scripts: ${scriptsOf(name)}',
  };
}

/// The tokens of `text`, a loaded source text.
List<Token> lex(String text) {
  final t = Text(text);
  return lexFrom(t, 0, [], false, Holes(t));
}

/// The tokens of `text`, a fence of the documentation, where `…` outside strings and comments
/// marks elided code and is read as the name `…` (DESIGN.md sec:grammar, "Documentation
/// notation"). No program can write that name.
List<Token> lexFence(String text) {
  final t = Text(text);
  return lexFrom(t, 0, [], true, Holes(t));
}

/// The tokens of `text` and its doc comments: a comment that starts with exactly three `/`
/// (`////` is an ordinary comment). Doc comments inside a string's hole are not collected.
(List<Token>, List<Doc>) lexWithDocs(String text) {
  final t = Text(text);
  final docs = <Doc>[];
  final tokens = lexFrom(t, 0, docs, false, Holes(t));
  return (tokens, docs);
}

/// The comments of `text`, lexed as `tokens`, in order: those between tokens, since a comment
/// in a string's hole is part of the string's token. Since `text` lexed, every block comment
/// in it is closed.
List<Span> comments(String text, List<Token> tokens) {
  final t = Text(text);
  final out = <Span>[];
  var pos = 0;
  for (final next in [...tokens.map((t) => t.span), (start: t.length, end: t.length)]) {
    while (pos < next.start) {
      if (comment(t, pos) case final end?) {
        out.add((start: pos, end: end));
        pos = end;
      } else {
        pos += t.charLength(pos);
      }
    }
    pos = next.end;
  }
  return out;
}

/// The tokens of `text` from byte `pos` to its end, with spans in `text`, and its doc comments
/// added to `docs`; with `elisions`, `…` is a name. `holes` holds what is known of the holes of
/// the whole text this is part of.
List<Token> lexFrom(Text text, int pos, List<Doc> docs, bool elisions, Holes holes) {
  final out = <Token>[];
  for (var c = text.charAt(pos); c >= 0; c = text.charAt(pos)) {
    final start = pos;
    Tok? tok;
    if (c == 0x20 || c == 0x09 || c == 0x0d || c == 0x0a) {
      pos += 1;
    } else if (comment(text, pos) case final end?) {
      pos = end;
      if (text.startsWith('///', start) && !text.startsWith('////', start)) {
        final body = start + (text.startsWith('/// ', start) ? 4 : 3);
        docs.add((text: text.slice(body, pos), span: (start: start, end: pos)));
      }
    } else if (number(text, pos) case (final end, final t)?) {
      pos = end;
      tok = t;
    } else if (string(text, pos, holes) case (final end, final t)?) {
      pos = end;
      tok = t;
    } else if ((c == 0x23 || c == 0x40) && name(text, pos + 1) != null) {
      pos = name(text, pos + 1)!;
      final word = _checked(text, start + 1, pos);
      tok = c == 0x23 ? Atom(word) : Annot(word);
    } else if (name(text, pos) case final end?) {
      final word = text.slice(start, end);
      if (keyword(word.endsWith("'") ? word.substring(0, word.length - 1) : word) case final k?) {
        pos = start + k.length;
        tok = Keyword(k);
      } else {
        pos = end;
        tok = Name(_checked(text, start, end));
      }
    } else if (wildcard(text, pos) case final end?) {
      pos = end;
      tok = const Wildcard();
    } else if (elisions && c == 0x2026) {
      pos += text.charLength(pos);
      tok = const Name('…');
    } else if (operator(text, pos) case final op?) {
      pos += op.length;
      tok = Op(op);
    } else {
      throw LexError(Unexpected(c), (start: start, end: start + text.charLength(start)));
    }
    if (tok != null) out.add((tok: tok, span: (start: start, end: pos)));
  }
  return out;
}

/// The name from `start` to `end` of `text`, if its characters are of one script.
String _checked(Text text, int start, int end) {
  final word = text.slice(start, end);
  if (isSingleScript(word.endsWith("'") ? word.substring(0, word.length - 1) : word)) return word;
  throw LexError(MixedScript(word), (start: start, end: end));
}
