/// The errors elaboration reports, one case each.
library;

import 'package:test/test.dart';

import 'elab.dart';

void main() {
  test('recursion is layer L6', () {
    expect(
      one('countdown(positional n) = if n == 0 { 0 } else { countdown(n - 1) };\n'),
      startsWith('`countdown` is defined in terms of itself: recursion arrives at layer L6'),
    );
    expect(
      one('a = b + 1;\nb = a + 1;\n'),
      startsWith('`a`, `b` are defined in terms of each other'),
    );
    expect(
      one('total = { x = y; y = x; x };\n'),
      contains('are defined in terms of each other: recursion arrives at layer L6'),
    );
  });

  test('call rules', () {
    const greet = 'greet(positional name, punct = "!") = name ++ punct;\n';
    const cases = [
      ('x = greet(name: "Al");', '`name` of `greet` is positional: pass it by position ["Al"]'),
      ('x = greet(punct: "?");', 'missing argument `name` of `greet` [greet(punct: "?")]'),
      ('x = greet("Al", "?");', '`punct` of `greet` is named: pass it as `punct: …` ["?"]'),
      ('x = greet("Al", tone: 1);', '`greet` has no parameter `tone` [1]'),
      (
        'x = greet("Al", punct: "?", ...);',
        '`...` leaves no named parameter out [greet("Al", punct: "?", ...)]',
      ),
      (
        'x = greet(punct: "?", ...);',
        '`...` curries named parameters only; the positional `name` is left out '
            '[greet(punct: "?", ...)]',
      ),
      ('x = "Al".greet("?");', '`punct` of `greet` is named: pass it as `punct: …` ["?"]'),
    ];
    for (final (call, want) in cases) {
      expect(one('$greet$call\n'), want, reason: call);
    }
  });

  test('errors are listed in text order, those of one span by message', () {
    // `b` is elaborated before `a`, which reads it; the checker's error comes first, at the
    // span that holds the others.
    expect(errors('a = b + (1 is Lines);\nb = (2 is Files);\n'), [
      '`+` does not take (bool, bool) [b + (1 is Lines)]',
      '`Lines` is the type of a port, and no value has it [Lines]',
      '`Files` is the type of a port, and no value has it [Files]',
    ]);
    expect(errors('f(a, b) = a;\ny = f();\n'), [
      'missing argument `a` of `f` [f()]',
      'missing argument `b` of `f` [f()]',
    ]);
  });

  test('too many arguments', () {
    expect(
      one('pair(positional a, positional b) = (a, b);\nx = 1.pair(2, 3);\n'),
      'too many arguments: `pair` takes 2 [3]',
    );
  });

  test('defaults that read each other', () {
    expect(
      one('f(a = b, b = a) = a;\ny = f();\n'),
      'the defaults of `a`, `b` read each other [f()]',
    );
  });

  test('named arguments through a value need its parameter names', () {
    // A lambda with no expected type takes its arguments by position.
    expect(
      one('inc = x -> x + 1;\ny = inc(x: 1);\n'),
      '`x` of `(_) -> _` is positional: pass it by position [1]',
    );
    // A prelude word, and a value of unknown type, give no parameter names.
    const want =
        'named arguments and `...` need the parameter names of the function called, '
        'which a prelude word and a value of unknown type do not give';
    expect(one('y = len(s: "ab");\n'), '$want [len(s: "ab")]');
    expect(one('g(f) = f(x: 1);\n'), '$want [f(x: 1)]');
  });

  test('forms of later steps and layers', () {
    const cases = [
      (
        'p = 1;\nx = p.size;',
        '`size` is not a function in scope, and fields arrive at L2 [p.size]',
      ),
      ('p = 1;\nx = p.map(1);', '`map` is a prelude word of layer L3 [p.map]'),
      (
        'f = (x = 1) -> x;',
        "a lambda's parameter has a default only where an expected function type leaves it "
            'out [1]',
      ),
      (
        'f(x: int) = 1;\nf(x: String) = 2;\ny = f(x: 1);',
        '`f` names 2 overloads; choosing among them arrives at L2 [f]',
      ),
    ];
    for (final (src, want) in cases) {
      expect(one('$src\n'), want, reason: src);
    }
  });

  test('test tables', () {
    expect(
      one('area(w, h) = w * h test { 2 -> 6 }\n'),
      'a test key of `area` is the tuple of its 2 arguments [2]',
    );
    expect(
      one('outer = { sq(positional x) = x * x test { 2 -> 4 } sq(3) };\n'),
      startsWith("`sq` has a test table, which belongs to a function at the unit's top level"),
    );
  });
}
