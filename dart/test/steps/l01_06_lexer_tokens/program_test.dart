/// Step L1.6: atoms, annotations, comments and doc comments, every operator, and the 36
/// keywords: the lexical grammar whole.
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/support.dart';
import '../../support/tokens.dart';

/// The `sec:tour_failure` example of EXAMPLES.md, copied.
const tourFailure = r'''// [d4] sec:tour_failure
parse : (String) -> Config | #syntaxError(pos: int)     // an assumed input, shown as a type — no ';' (sec:lexical)
conf = parse(text) else defaultConfig;
port = parse(text)?.server?.port else 8080;
msg  = match parse(text) { #syntaxError(pos:) -> "bad at ${pos}", c -> c.name };
results = files.map(f -> read(f)).map(b -> parse(b));   // File -> Config | #syntaxError(pos: int) | #ioError | #notFound: the atoms ride through
good = results.where(r -> r is Config);
bad  = results.where(r -> r is not Config);
amounts = files.map(f -> int(read(f)));                 // int | #invalid | #ioError | #notFound
sumKept   = amounts.where(a -> a is int) >< (+);
sumZeroed = amounts.map(a -> a else 0) >< (+);
''';

void main() {
  test('an example program', () {
    expectOutput(
      'l01_06_lexer_tokens',
      'example_program',
      renderLines(tourFailure, lex(tourFailure)),
    );
  });

  test('doc comments are collected and other comments dropped', () {
    const src =
        '/// The order total.\n///\n////  a ruled line, not a doc\n//   a plain comment\n'
        '/** a block comment */\n///   indented text keeps all but one space\ntotal = 1;';
    final (tokens, docs) = lexWithDocs(src);
    expect(render(tokens), 'total = 1₍10₎ ;');
    expect(docs.map((d) => d.text), [
      'The order total.',
      '',
      '  indented text keeps all but one space',
    ]);
    expect(src.substring(docs[0].span.start, docs[0].span.end), '/// The order total.');
  });

  test('block comments nest', () {
    expect(render(lex('a /* outer /* inner */ still out */ b /* /* */ */ c')), 'a b c');
    const src = 'x /* /* only the inner closes */ y';
    try {
      lex(src);
      fail('lexed');
    } on LexError catch (e) {
      expect((e.span.start, e.span.end), (2, src.length));
      expect('$e', 'the block comment is not closed (1 `*/` missing)');
    }
  });

  test('a comment delimiter in a string is text', () {
    expect(render(lex(r'url = "http://x/*y*/"; // c')), r'url = str["http://x/*y*/"] ;');
  });
}
