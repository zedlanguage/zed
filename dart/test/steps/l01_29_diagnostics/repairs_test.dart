/// A repair is offered only when the checker accepts the repaired application, so applying
/// the offered repair makes the program check.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/run.dart';

import 'diagnostics.dart';

/// The program `src` with the text `at` wrapped in `word(…)`.
String wrapped(String src, String at, String word) {
  expect(at.allMatches(src), hasLength(1), reason: at);
  return src.replaceFirst(at, '$word($at)');
}

void main() {
  test('the offered repair applied makes the program check', () {
    const cases = [
      (
        'main(stdin: Lines) -> (stdout: Lines) {\n'
            '  n = int(stdin[1]) else 0;\n'
            '  stdout <- "count: " ++ n * 2;\n'
            '}\n',
        'n * 2',
        'String',
      ),
      (
        'price(positional cents: int) = cents * 100;\n'
            'main(stdin: Lines) -> (stdout: Lines) {\n'
            '  stdout <- String(price(2.5));\n'
            '}\n',
        '2.5',
        '',
      ),
    ];
    for (final (src, at, word) in cases) {
      final out = rejected(src);
      if (word.isEmpty) {
        expect(out, isNot(contains('repair:')));
        continue;
      }
      expect(out, contains('repair: wrap this in `$word(…)`; the checker accepts that'));
      final fixed = wrapped(src, at, word);
      load(utf8.encode(fixed));
    }
  });

  test('a conversion that can fail is not offered where its failure is not taken', () {
    // `int("12")` is `int | #invalid`, and `discount` takes no `#invalid`.
    const src =
        'discount(price: int, tier) = if tier == #gold { price * 8 } else { price * 10 };\n'
        'main(stdin: Lines) -> (stdout: Lines) {\n'
        '  p = discount(price: "12", tier: #gold);\n'
        '  stdout <- String(p);\n'
        '}\n';
    expect(rejected(src), isNot(contains('repair:')));
    expect(() => load(utf8.encode(wrapped(src, '"12"', 'int'))), throwsA(isA<RunError>()));
  });
}
