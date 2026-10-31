/// Rows of `test { }` tables: a function's, and `main`'s, each a wave.
library;

import 'package:test/test.dart';

import 'runner.dart';

void main() {
  test('a wrong row reports the result', () {
    expect(checks('square(positional x) = x * x test { 3 -> 9, 4 -> 15 }\n'), [
      '1:37: ok',
      '1:45: `4 -> 15` of `square`: the result is 16',
    ]);
  });

  test('a row of several arguments, and a failure value', () {
    const src =
        'area(w, h) = w * h test { (2, 3) -> 6, (2, 3) -> 7 }\n'
        'parse(positional s) = int(s) test { "12" -> 12, "1.5" -> #invalid }\n';
    expect(checks(src), [
      '1:27: ok',
      '1:40: `(2, 3) -> 7` of `area`: the result is 6',
      '2:37: ok',
      '2:49: ok',
    ]);
  });

  test('a row that stops the evaluator fails', () {
    final got = checks('first(positional s) = s[1] test { "ab" -> "a" }\n');
    expect(got, hasLength(1));
    expect(got[0], startsWith('1:35: `"ab" -> "a"` of `first`: '));
    expect(got[0], isNot(endsWith(': ok')));
  });

  test('a main row compares the bytes each port writes', () {
    const src =
        'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- upper(stdin[1]);\n}\n'
        r'test { "abc\n" -> "ABC\n", "abc" -> "ABC" }'
        '\n';
    expect(checks(src), [
      '4:8: ok',
      r'4:28: `"abc" -> "ABC"` of `main`: port `stdout` writes "ABC\n"',
    ]);
  });

  test('a port not pushed writes nothing', () {
    const src =
        'main(stdin: Lines) -> (stdout: Lines, stderr: Lines) {\n  stdout <- stdin[1];\n}\n'
        r'test { "a" -> ("a\n", ""), "a" -> ("a\n", "warning\n") }'
        '\n';
    expect(checks(src), [
      '4:8: ok',
      r'4:28: `"a" -> ("a\n", "warning\n")` of `main`: port `stderr` writes ""',
    ]);
  });

  test('a Files port is given as a function of the path', () {
    const src =
        'main(fs: Files) -> (stdout: Lines) {\n  stdout <- fs["a.txt"] ++ fs["b.txt"];\n}\n'
        r'test { (p -> if p == "a.txt" { "1" } else { "2" }) -> "12\n" }'
        '\n';
    expect(checks(src), ['4:8: ok']);
  });

  test('a row of the wrong shape says what a port takes', () {
    const src =
        'main(stdin: Lines) -> (stdout: Lines, stderr: Lines) {\n'
        '  stdout <- "x";\n  stderr <- "y";\n}\n'
        r'test { 3 -> ("x\n", "y\n"), "" -> "x\n", "" -> ("x\n", 2) }'
        '\n';
    expect(checks(src), [
      r'5:8: `3 -> ("x\n", "y\n")` of `main`: the `Lines` port `stdin` is given as a String, '
          'not 3',
      r'5:29: `"" -> "x\n"` of `main`: the expected value is a String for each of the 2 output '
          r'ports, not "x\n"',
      r'5:42: `"" -> ("x\n", 2)` of `main`: the expected value of port `stderr` is a String, '
          'not 2',
    ]);
  });

  test('a wave that aborts fails its row', () {
    const src =
        'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- int(stdin[1]);\n}\n'
        r'test { "7" -> "7\n" }'
        '\n';
    expect(checks(src), [
      r'4:8: `"7" -> "7\n"` of `main`: port `stdout` takes strings; 7 was pushed',
    ]);
  });

  test('a main whose ports are not L1 reports once and runs no row', () {
    const src =
        'main(n: int) -> (stdout: Lines) {\n  stdout <- "x";\n}\n'
        r'test { 1 -> "x\n" }'
        '\n';
    expect(checks(src), ['1:1: port `n` of `main` is `Lines` or `Files` at layer L1']);
  });
}
