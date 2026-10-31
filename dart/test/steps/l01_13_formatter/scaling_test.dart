/// The formatter at the rule of low complexity (DESIGN.md Part G): of order n log n in the
/// length of the text, with the depth of its nesting bounded by memory alone.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/format.dart';

import '../../support/scaling.dart';

/// `f(c) = if c { if c { … { a = 1; a } … } else { 0 } } else { 0 };`, nested `depth` deep.
String nested(int depth) {
  var b = '{ a = 1; a }';
  for (var i = 0; i < depth; i++) {
    b = '{ if c $b else { 0 } }';
  }
  return 'f(c) = if c $b else { 0 };\n';
}

/// `n` statements, each with four comments on their own lines before it and one after it.
String commented(int n) =>
    [for (var i = 0; i < n; i++) '// a\n// b\n// c\n// d\na$i = $i; // a$i\n'].join();

void main() {
  test('nested one-statement blocks', () {
    // A block of one statement on several lines is rendered once, not once to try one line and
    // again on its own lines, which costs `2^d` renders for `d` such blocks nested.
    check(
      'nested one-statement blocks, by depth',
      200,
      (d) => formatSource(utf8.encode(nested(d))),
    );
    expect(
      formatSource(utf8.encode(nested(1))),
      'f(c) = if c {\n  if c {\n    a = 1;\n    a\n  } else { 0 }\n} else { 0 };\n',
    );
  });

  test('many comments', () {
    // Each statement's comments are found in an ordered map, not by a scan over every comment.
    check(
      'statements with comments, by count',
      500,
      (n) => formatSource(utf8.encode(commented(n))),
    );
    expect(formatSource(utf8.encode(commented(2))), commented(2));
  });

  test('a long else-if chain and deep lambdas', () {
    check('else-if chain, by length', 200, (n) {
      final text = 'f(x) = ${'if x { 1 } else ' * n}{ 0 };\n';
      expect(formatSource(utf8.encode(text)), text);
    });
    check('nested lambdas, by depth', 200, (n) {
      final text = 'f() = ${'x -> ' * n}x;\n';
      expect(formatSource(utf8.encode(text)), text);
    });
  });
}
