/// Parsing is of order n log n in the number of tokens, and in the depth of the text's
/// nesting, which is bounded by memory alone (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

import '../../support/scaling.dart';

void main() {
  test('many statements', () {
    const one = 'x = 1 + 2 * f(a, b)[0] else #none;\n';
    final texts = {
      for (final n in [100, 800]) n: one * n,
    };
    final tokens = {for (final MapEntry(:key, :value) in texts.entries) key: lex(value)};
    check('parse', 100, (n) => parse(texts[n]!, tokens[n]!, 'Unit', top));
  });

  test('deep nesting', () {
    String text(int d) => 'x = ${'(' * d}1${')' * d} + ${'f([1 + ' * d}2${'])' * d};';
    final texts = {
      for (final d in [500, 4000]) d: text(d),
    };
    final tokens = {for (final MapEntry(:key, :value) in texts.entries) key: lex(value)};
    check('parse', 500, (d) => parse(texts[d]!, tokens[d]!, 'Unit', top));
  });

  test('a nested string hole', () {
    String text(int d) => 'x = ${r'"${' * d}1${'}"' * d};';
    final texts = {
      for (final d in [100, 800]) d: text(d),
    };
    final tokens = {for (final MapEntry(:key, :value) in texts.entries) key: lex(value)};
    check('parse', 100, (d) => parse(texts[d]!, tokens[d]!, 'Unit', top));
  });
}
