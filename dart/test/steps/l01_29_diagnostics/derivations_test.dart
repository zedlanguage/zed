/// What a derivation contains: the chain from the rejected term back to the declarations its
/// types come from.
library;

import 'package:test/test.dart';

import 'diagnostics.dart';

void main() {
  test('a report line that concatenates a number shows the chain back to the input port', () {
    final out = rejected('''main(stdin: Lines) -> (stdout: Lines) {
  n = int(stdin[1]) else 0;
  total = n * 2;
  stdout <- "total: " ++ total;
}
''');
    expect(out, r'''4:13: `++` does not take ("total: ", int)
  [1]  4:13: this expression is "total: "
       4 |   stdout <- "total: " ++ total;
         |             ^^^^^^^^^
  [2]  4:26: `total` is int | _ here
       4 |   stdout <- "total: " ++ total;
         |                          ^^^^^
  [3]  3:11: `total` is defined as this expression, int | _
       3 |   total = n * 2;
         |           ^^^^^
  [4]  3:11: this `*` gives int | _
  [5]  3:11: `n` is 0 | _ here
       3 |   total = n * 2;
         |           ^
  [6]  2:7: `n` is defined as this expression, 0 | _
       2 |   n = int(stdin[1]) else 0;
         |       ^^^^^^^^^^^^^^^^^^^^
  [7]  2:7: this `else` gives 0 | _
  [8]  2:7: this call of `int` gives _
       2 |   n = int(stdin[1]) else 0;
         |       ^^^^^^^^^^^^^
  [9]  2:11: this expression gives _
       2 |   n = int(stdin[1]) else 0;
         |           ^^^^^^^^
  [10] 2:11: `stdin` is _ here
       2 |   n = int(stdin[1]) else 0;
         |           ^^^^^
  [11] 1:6: `stdin` is declared `Lines`, whose values the checker does not track: it takes `stdin` as unknown, _
       1 | main(stdin: Lines) -> (stdout: Lines) {
         |      ^^^^^^^^^^^^
  [12] 2:26: this literal, 0, is 0
       2 |   n = int(stdin[1]) else 0;
         |                          ^
  [13] 3:15: this literal, 2, is 2
       3 |   total = n * 2;
         |               ^
  [14] 4:13: `++` takes (String, String) -> String
       4 |   stdout <- "total: " ++ total;
         |             ^^^^^^^^^^^^^^^^^^
  [15] 4:26: repair: wrap this in `String(…)`; the checker accepts that
       4 |   stdout <- "total: " ++ total;
         |                          ^^^^^''');
  });

  test('a call of a declared function shows the declaration and its signature', () {
    final out = rejected(
      'discount(price: int, tier) = if tier == #gold { price * 8 } else { price * 10 };\n'
      'main(stdin: Lines) -> (stdout: Lines) {\n'
      '  p = discount(price: "12", tier: #gold);\n'
      '  stdout <- String(p);\n'
      '}\n',
    );
    expect(steps(out), [
      'this expression is "12"',
      'this expression is #gold',
      '`discount` takes (price: int, tier: T) -> int',
      '`discount` is declared here, `(price: int, tier: T) -> int`',
    ]);
  });

  test('a test that narrows a parameter is a step with the parameter it narrowed', () {
    final out = rejected(
      'label(positional v) = if v is int { "n" ++ v } else { "s" };\n'
      'main(stdin: Lines) -> (stdout: Lines) {\n'
      '  stdout <- label(3);\n'
      '}\n',
    );
    final s = steps(out);
    final narrowed = s.indexOf('`v` is narrowed to int where this test decides');
    expect(narrowed, isNot(-1), reason: out);
    expect(s[narrowed - 1], '`v` is int here');
    expect(s[narrowed + 1], '`v` has no declared type; its uses give it T', reason: out);
  });

  test('a rebinding points at the first binding', () {
    final out = rejected(
      'main(stdin: Lines) -> (stdout: Lines) {\n'
      '  rate = 3;\n'
      '  rate = 4;\n'
      '  stdout <- "x";\n'
      '}\n',
    );
    expect(
      out,
      '3:3: `rate` is already bound in this scope\n'
      '  [1] 2:3: the first binding of `rate`\n'
      '      2 |   rate = 3;\n'
      '        |   ^^^^^^^^^',
    );
  });

  test('an error in a function is at the use that leaves its parameter no carrier', () {
    final out = rejected(
      'badge(positional x) = "#" ++ x * 2;\n'
      'main(stdin: Lines) -> (stdout: Lines) {\n'
      '  stdout <- badge(3);\n'
      '}\n',
    );
    expect(out.split('\n').first, '1:23: `++` does not take ("#", int | f64 | rat)');
    final s = steps(out);
    for (final step in [
      'this `*` gives int | f64 | rat',
      '`x` is int | f64 | rat here',
      'the literal 2 takes int | f64 | rat',
      '`++` takes (String, String) -> String',
    ]) {
      expect(s, contains(step), reason: out);
    }
  });

  test('an error over several parameters is one error with the use that joined them', () {
    // The search this replaces tried 25 combinations of carriers and showed 12.
    final out = rejected(
      'area(positional w, positional h) = "#" ++ w * h;\n'
      'main(stdin: Lines) -> (stdout: Lines) {\n'
      '  stdout <- area(2, 3);\n'
      '}\n',
    );
    expect(out.split('\n').first, '1:36: `++` does not take ("#", int | f64 | rat)');
    final s = steps(out);
    for (final step in [
      '`w` is int | f64 | rat here',
      '`h` is int | f64 | rat here',
      '`*` gives these values one carrier',
      '`*` takes int | f64 | rat',
    ]) {
      expect(s, contains(step), reason: out);
    }
    expect(s.any((t) => t.startsWith('with ')), isFalse, reason: out);
  });

  test('a function whose search succeeded shows its signature, not the abandoned runs', () {
    final out = rejected(
      'twice(positional x) = x * 2;\n'
      'main(stdin: Lines) -> (stdout: Lines) {\n'
      '  stdout <- "a" ++ twice(3);\n'
      '}\n',
    );
    expect(steps(out), [
      'this expression is "a"',
      'this call of `twice` gives int',
      '`twice` is declared here, `(int) -> int`',
      '`++` takes (String, String) -> String',
      'repair: wrap this in `String(…)`; the checker accepts that',
    ]);
  });

  test('a long chain is shown whole back to its first binding', () {
    final src = StringBuffer('main(stdin: Lines) -> (stdout: Lines) {\n  a0 = 1;\n');
    for (var i = 1; i < 25; i++) {
      src.write('  a$i = a${i - 1} + 1;\n');
    }
    src.write('  stdout <- "x" ++ a24;\n}\n');
    final out = rejected('$src');
    final s = steps(out);
    expect(out, isNot(contains('goes back further')));
    for (var i = 1; i < 25; i++) {
      final t = '`a$i` is int here';
      expect(s.where((x) => x == t), hasLength(1), reason: '$t: $out');
    }
    expect(s, contains('`a0` is 1 here'), reason: out);
    expect(s, contains('`a0` is defined as this expression, 1'), reason: out);
  });

  test('a value read twice is derived once', () {
    // Each `a{i}` reads `a{i-1}` twice; without a visited set the derivation doubles at each
    // binding.
    final src = StringBuffer('main(stdin: Lines) -> (stdout: Lines) {\n  a0 = 1;\n');
    for (var i = 1; i < 40; i++) {
      src.write('  a$i = a${i - 1} + a${i - 1};\n');
    }
    src.write('  stdout <- "x" ++ a39;\n}\n');
    final out = rejected('$src');
    final s = steps(out);
    expect(s, contains('`a0` is defined as this expression, 1'), reason: out);
    for (var i = 1; i < 40; i++) {
      final t = '`a$i` is defined as this expression, int';
      expect(s.where((x) => x == t), hasLength(1), reason: '$t: $out');
    }
  });

  test("a body reading a top-level value shows that value's whole chain", () {
    final out = rejected(
      'base = 4;\n'
      'rate = base * 3;\n'
      'tag(positional x) = "rate " ++ rate;\n'
      'main(stdin: Lines) -> (stdout: Lines) {\n'
      '  stdout <- tag(1);\n'
      '}\n',
    );
    expect(steps(out), [
      'this expression is "rate "',
      '`rate` is int here',
      '`rate` is defined as this expression, int',
      'this `*` gives int',
      '`base` is 4 here',
      '`base` is defined as this expression, 4',
      'this expression is 4',
      'this literal, 3, is 3',
      '`++` takes (String, String) -> String',
      'repair: wrap this in `String(…)`; the checker accepts that',
    ]);
  });
}
