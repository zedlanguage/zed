/// Atoms with payloads: built and matched by position or by name.
library;

import 'package:test/test.dart';

import '../l01_16_elaboration/elab.dart';

void main() {
  test('a named payload is a struct, whatever the written order', () {
    const src =
        'e = #parseError(line: 3, col: 7);\nred = #red == #red;\nf = #parseError(col: 7, line: 3);\n'
        'same = e == f;\nother = e == #parseError(line: 3, col: 8);\n';
    expect(value(src, 'e'), '#parseError(col: 7, line: 3)');
    expect(value(src, 'same'), 'true');
    expect(value(src, 'other'), 'false');
    expect(value(src, 'red'), 'true', reason: '`==` compares atoms as data');
    expect(term(src, 'e'), '#parseError(line: 3, col: 7)');
  });

  test('a positional payload holds any value, atoms included', () {
    const src = 'sum = #add(1, (2, 3));\nwrapped = #some(#none);\nhole = #at(1 div 0);\n';
    expect(value(src, 'sum'), '#add(1, (2, 3))');
    // A payload holds an atom as data: it is not passed through as a failure.
    expect(value(src, 'wrapped'), '#some(#none)');
    expect(value(src, 'hole'), '#at(#divByZero)');
  });

  test('`else` matches a payload by name and binds its fields', () {
    const src =
        'parse(positional text) = if text == "" { #parseError(line: 1, col: 0) } else { 42 };\n'
        'line = parse("") else #parseError(line:) -> line;\n'
        'both = parse("") else #parseError(line:, col:) -> line * 100 + col;\n'
        'ok = parse("x") else #parseError(line:) -> line;\n'
        'miss = parse("") else #parseError(file:) -> 0;\n';
    expect(value(src, 'line'), '1');
    expect(value(src, 'both'), '100');
    expect(value(src, 'ok'), '42');
    expect(
      value(src, 'miss'),
      '#parseError(col: 0, line: 1)',
      reason: 'a field the payload lacks does not match',
    );
    expect(term(src, 'line'), r'match parse("") { #parseError(line: line@2) -> line@2, $1 -> $1 }');
  });

  test('nested atom patterns by position and by name', () {
    const src =
        'a = #some(#none) else #some(#none) -> 0;\n'
        'b = #some(#none) else #some(#other) -> 0;\n'
        'c = #wrap(inner: #none) else #wrap(inner: #none) -> 1;\n'
        'd = #wrap(inner: #none) else #wrap(#none) -> 1;\n';
    expect(value(src, 'a'), '0');
    expect(value(src, 'b'), '#some(#none)');
    expect(value(src, 'c'), '1');
    expect(
      value(src, 'd'),
      '#wrap(inner: #none)',
      reason: 'a pattern by position does not match a payload by name',
    );
  });

  test('payload errors', () {
    const cases = [
      (
        'x = #e(1, code: 2);',
        "an atom's payload is all by position or all by name [#e(1, code: 2)]",
      ),
      (
        'x = #e(code: 1, ...);',
        "`...` curries a function's named parameters; an atom has none [#e(code: 1, ...)]",
      ),
      (
        'x = #e(code: 1) else #e(code: #a, code: #b) -> 0;',
        'the pattern names `code` twice [#e(code: #a, code: #b)]',
      ),
    ];
    for (final (src, want) in cases) {
      expect(errors('$src\n'), [want], reason: src);
    }
  });
}
