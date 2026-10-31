/// Where a name starts and ends, and what is the wildcard.
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

/// The tokens of `text`, a name as written and the wildcard as `(wildcard)`, or the error's
/// kind and byte offset.
Object toks(String text) {
  try {
    return [
      for (final t in lex(text))
        switch (t.tok) {
          Name(:final text) => text,
          Wildcard() => '(wildcard)',
          final other => '$other',
        },
    ];
  } on LexError catch (e) {
    return (e.kind, e.span.start);
  }
}

void main() {
  test('names as programs write them', () {
    expect(toks('invoiceTotal unit_price x1 X_2 lineItems\ttaxRate\n'), [
      'invoiceTotal',
      'unit_price',
      'x1',
      'X_2',
      'lineItems',
      'taxRate',
    ]);
  });

  test('a bare underscore is the wildcard and an underscore before a name character is a name', () {
    expect(toks('_ _unused __init__ _1 total_'), [
      '(wildcard)',
      '_unused',
      '__init__',
      '_1',
      'total_',
    ]);
  });

  test('a trailing prime is part of the name and only one is read', () {
    // The next generation of a loop's state (sec:generations).
    expect(toks("pos' count' x'y"), ["pos'", "count'", "x'", 'y']);
    expect(toks("x''"), (const Unexpected(0x27), 2));
    expect(toks("'x"), (const Unexpected(0x27), 0));
  });

  test('a name cannot start with a digit or a combining mark', () {
    // A digit starts a number, which must not run into a name (step L1.3).
    expect(toks('1st'), isA<(BadNumber, int)>().having((e) => e.$2, 'offset', 0));
    expect(toks('\u0301a'), (const Unexpected(0x301), 0));
  });

  test('spans are byte ranges of the text', () {
    final spans = [for (final t in lex("gr\u00f6\u00dfe  x'")) (t.span.start, t.span.end)];
    expect(spans, [(0, 7), (9, 11)]);
  });
}
