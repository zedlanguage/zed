/// Step L1.9: postfix chains become syntax trees (`ast.dart`): calls with positional, named
/// and curried arguments, `.`, `?.`, indexing, and the `5.double` rule of the lexer.
///
/// The call rules: positional arguments first, then named ones, then an optional `...`; `x:`
/// supplies the variable `x`; no argument is named twice.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

import 'ast.dart';

String at(String text, Span s) => utf8.decode(utf8.encode(text).sublist(s.start, s.end));

void main() {
  test('positional, then named, then curry', () {
    const cases = [
      ('clamp(5, 0, 8)', '(call clamp 5 0 8)'),
      ('greet("Al", punct: "?")', '(call greet (str "Al") (punct: (str "?")))'),
      ('join(b, on: #orderId, kind: #left)', '(call join b (on: #orderId) (kind: #left))'),
      ('Point(x:, y:)', '(call Point (x: x) (y: y))'),
      ('Point(x: 0.0, ...)', '(call Point (x: 0.0) ...)'),
      ('greet("Ann", ...)', '(call greet (str "Ann") ...)'),
      ('Vec3(z: 1.0, x: 0.0, y: 0.0,)', '(call Vec3 (z: 1.0) (x: 0.0) (y: 0.0))'),
      ('now()', '(call now)'),
    ];
    for (final (text, want) in cases) {
      expect('${ast(text)}', want, reason: text);
    }
  });

  test('a shorthand argument is the name at its own place', () {
    const text = 'Point(x:, y: 2.0)';
    final e = ast(text) as Call;
    expect(at(text, e.named[0].$2.span), 'x');
  });

  test('misordered arguments do not parse', () {
    // DESIGN.md: `greet(name: "Al")` and `greet(punct: "?", "Al")` are errors; the first is a
    // type error (L1.16), the second a syntax error, as is `...` anywhere but last.
    for (final text in [
      'greet(punct: "?", "Al")',
      'f(..., x: 1)',
      'f(x: 1, ..., y: 2)',
      'f(...)',
    ]) {
      expect(() => parse(text, lex(text), 'Expr', top), throwsA(isA<ParseError>()), reason: text);
    }
  });

  test('an argument named twice is an error at the second', () {
    const text = 'Rect(w: 3, h: 4, w: 5)';
    final err = astError(text);
    expect(at(text, err.span), 'w');
    expect(err.span.start, 17);
    expect(err.message, 'the argument `w` is named twice');
    expect(err.notes, hasLength(1));
    expect(err.notes[0].text, 'the first argument named `w`');
    expect(err.notes[0].span.start, 5);
  });

  test('a form of a later layer names that layer', () {
    const cases = [
      ('data::len', 'this form (Suffix) is built from layer L3'),
      ('rows*.price', 'this form (Suffix) is built from layer L6'),
      ('sort(desc score)', 'this form (PosArg) is built from layer L5'),
    ];
    for (final (text, want) in cases) {
      expect(astError(text).message, want, reason: text);
    }
  });
}
