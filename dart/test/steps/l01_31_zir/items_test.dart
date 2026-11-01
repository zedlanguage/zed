/// Types, values, patterns and edges, each read back from the text the kernel prints.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart';

void main() {
  test('types read back', () {
    for (final t in [
      '_',
      '(|)',
      'bool',
      'true',
      'int',
      'rat',
      'f64',
      'String',
      '#_',
      'tuple',
      'struct',
      'morphism',
      '3',
      '"GET"',
      '#none',
      '(#some (tuple int))',
      '(#some _)',
      '(| #none (#some (tuple int)))',
      '(| int String)',
      r'(\ int 0)',
      '(tuple int String)',
      '(-> int bool)',
      '(->? String int)',
      '(| (-> String String) (-> int int))',
    ]) {
      expect('${parseType(t)}', t);
    }
  });

  test('values read back', () {
    for (final v in [
      'true',
      '-42',
      '123456789012345678901234567890',
      '3r',
      '-3r/4r',
      '1.5',
      '-0.0',
      'inf',
      '-inf',
      'nan',
      '1.5e30',
      r'"tab\there \"quoted\" 😀"',
      '#empty',
      '#pair(1, "b")',
      '#err(code: 3, why: "x")',
      '()',
      '(1)',
      '(1, (2, 3))',
      '["eu" -> 2024 -> 3]',
      '{}',
      '{1 -> "a", 2 -> "b"}',
      '{"x", "y"}',
      '{1 -> {2 -> 3}}',
    ]) {
      expect('${parseValue(v)}', v);
    }
  });

  test('string escapes', () {
    // The kernel prints a printable character as itself; the reader takes the escapes too.
    expect(parseValue(r'"\u{1f600}\n\0"'), Str('😀\n\x00'));
    expect(
      () => parseValue(r'"a\qb"'),
      throwsA(
        isA<ZirError>().having((e) => e.message, 'message', r'column 2: `\q` is not an escape'),
      ),
    );
  });

  test('named payload fields sort', () {
    // A struct payload's fields are sorted, whatever order the text gives them in.
    expect(parseValue('#err(why: "x", code: 3)'), parseValue('#err(code: 3, why: "x")'));
    expect(
      () => parseValue('#err(code: 3, code: 4)'),
      throwsA(
        isA<ZirError>().having(
          (e) => e.message,
          'message',
          'column 23: atom `#err` names a field twice',
        ),
      ),
    );
  });

  test('floats keep their bits', () {
    final v = parseValue('-0.0');
    expect(v, Float(-0.0));
    expect(v, isNot(Float(0.0)));
  });

  test('patterns read back', () {
    for (final p in [
      '_',
      'n',
      '#_',
      '#none',
      '#some(n)',
      '#err(code: c, why: _)',
      '(a, b)',
      '(a,)',
      '()',
      '=3',
      '="GET"',
      '=#none',
      '=(1, 2)',
      '(is (| int String))',
      '#some((a, #pair(=1, b)))',
    ]) {
      expect(pattern(parsePattern(p)), p);
    }
    // A literal atom is not an atom pattern: `=#none` matches the value, `#none` the shape.
    expect(parsePattern('=#none'), isA<LitP>());
    expect(parsePattern('#none'), isA<AtomP>());
  });

  test('edges read back', () {
    for (final e in [
      'state out',
      'int',
      'int in [0..=9]',
      'int in [..=-1, 1..]',
      'int class 1 mod 3',
      'int class 5',
      'int set {1, 5, 9}',
      'int in [0..] class 0 mod 2 set {0, 2}',
      'rat facet units "m/s"',
      'String hint name "title" facet locale "en"',
    ]) {
      expect(edge(parseEdge(e)), e);
    }
  });

  test('a family literal that repeats a key is an error, not a crash', () {
    expect(
      () => parseValue('{1 -> 2, 1 -> 3}'),
      throwsA(
        isA<ZirError>().having(
          (e) => e.message,
          'message',
          'column 17: the family has a key twice',
        ),
      ),
    );
  });

  test('a rational with a third part is not a number', () {
    expect(
      () => parseValue('1r/2r/3r'),
      throwsA(
        isA<ZirError>().having(
          (e) => e.message,
          'message',
          'column 9: expected a value, found `1r/2r/3r`',
        ),
      ),
    );
  });
}
