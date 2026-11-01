/// How a diagnostic is laid out: the message, then each step numbered and padded to one
/// width, its source line with a gutter of one width and the covered text underlined, the
/// source shown once for consecutive steps on one place.
library;

import 'package:test/test.dart';
import 'package:zed/run.dart';

import 'diagnostics.dart';

void main() {
  test('steps are numbered to one width and places shown once when repeated', () {
    const src9 = '  x = a + b;';
    const src12 = '  y = x ++ "!";';
    final d = Diagnostic(12, 7, '`++` does not take (int, "!")', [
      Step(12, 7, '`x` is int here', src12, 1),
      for (var i = 0; i < 9; i++) Step(9, 7, 'fact $i', src9, 5),
    ]);
    expect('$d', '''12:7: `++` does not take (int, "!")
  [1]  12:7: `x` is int here
       12 |   y = x ++ "!";
          |       ^
  [2]  9:7: fact 0
        9 |   x = a + b;
          |       ^^^^^
  [3]  9:7: fact 1
  [4]  9:7: fact 2
  [5]  9:7: fact 3
  [6]  9:7: fact 4
  [7]  9:7: fact 5
  [8]  9:7: fact 6
  [9]  9:7: fact 7
  [10] 9:7: fact 8''');
  });

  test('a diagnostic without steps is one line', () {
    expect('${Diagnostic(3, 1, '`Point` is not defined')}', '3:1: `Point` is not defined');
  });

  test('the underline covers a multibyte span by characters', () {
    final out = rejected(
      'main(stdin: Lines) -> (stdout: Lines) {\n'
      '  größe = 3;\n'
      '  größe = 4;\n'
      '  stdout <- "x";\n'
      '}\n',
    );
    expect(
      out,
      '3:3: `größe` is already bound in this scope\n'
      '  [1] 2:3: the first binding of `größe`\n'
      '      2 |   größe = 3;\n'
      '        |   ^^^^^^^^^^',
    );
  });
}
