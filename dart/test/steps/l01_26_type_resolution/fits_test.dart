/// A function argument fits the function type its slot expects: by its parameters' names,
/// in any order; a lambda by its own names; a parameter the type leaves out only with a
/// default.
library;

import 'package:test/test.dart';
import 'package:zed/check.dart';

import '../l01_16_elaboration/elab.dart';
import 'support.dart';

const apply = 'apply(f: (a: int, b: int) -> int) = f(a: 1, b: 2);\n';

List<Fit> fits(String text) => [...info(text).fits.values];

void main() {
  test('a function with the same names in order needs no fit', () {
    const p = '${apply}sub(a, b) = a - b;\ny = apply(f: sub);\n';
    expect(fits(p), isEmpty);
    expect(value(p, 'y'), '-1');
  });

  test('a function with the names reordered gets an adapter', () {
    const p = '${apply}sub(b, a) = a - b;\ny = apply(f: sub);\n';
    expect(fits(p), [
      const FitAdapter([1, 0]),
    ]);
    expect(value(p, 'y'), '-1');
  });

  test('a lambda takes its parameters by name', () {
    const p = '${apply}y = apply(f: (b, a) -> a - b);\n';
    expect(fits(p), [
      const FitLambda([1, 0], []),
    ]);
    expect(value(p, 'y'), '-1');
  });

  test('a lambda parameter the type leaves out takes its default', () {
    const p = 'apply(f: (a: int) -> int) = f(a: 3);\ny = apply(f: (a, k = 10) -> a * k);\n';
    expect(value(p, 'y'), '30');
  });

  test('a lambda parameter with another name is an error', () {
    expect(typeErrors('${apply}y = apply(f: (a, s) -> a - s);\n'), [
      "the lambda's parameter `s` is not a parameter of `(a: int, b: int) -> int`: "
          'rename it `b` [s]',
    ]);
  });

  test('named parameters do not fit a positional type', () {
    expect(
      typeErrors(
        'apply(f: (int, int) -> int) = f(1, 2);\nsub(a, b) = a - b;\ny = apply(f: sub);\n',
      ),
      [
        'the parameters of `sub` (a, b) do not fit `(int, int) -> int`: declare them as it '
            'passes them, with `positional` where it passes by position, or pass a lambda, '
            '(a, b) -> sub(a: a, b: b) [sub]',
      ],
    );
  });

  test("a lambda's result must fit", () {
    expect(typeErrors('apply(f: (int) -> String) = f(1);\ny = apply(f: n -> n + 1);\n'), [
      'the lambda returns int, and `(int) -> String` returns String [n + 1]',
    ]);
  });
}
