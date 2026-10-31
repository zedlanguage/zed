/// Step L1.22: `e is T` elaborates to a match whose first arm is the type and whose second is
/// `_`, and `is not` swaps the answers; a type naming a port, or bounding functions, is
/// rejected.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../l01_16_elaboration/elab.dart';

void main() {
  test('is is a match on the type', () {
    expect(
      term('f(x) = x is int | (int, String);', 'f'),
      contains('(is (| int (tuple int String))) -> true, _ -> false'),
    );
    expect(term('f(x) = x is not #none;', 'f'), contains('(is #none) -> false, _ -> true'));
  });

  test('function types are curried one level per parameter', () {
    // Only a test that cannot run shows the type, so the shape is read from the kernel:
    // `(a: int, b: int) -> int` is `int -> int -> int`.
    final curried = Type.exact(Type.integer, Type.exact(Type.integer, Type.integer));
    expect('$curried', '(-> int (-> int int))');
    expect(errors('f(x) = x is ((a: int, b: int) -> int);'), [
      '`is` cannot test a value against a function type at run time [((a: int, b: int) -> int)]',
    ]);
  });

  test('port types and function bounds are rejected', () {
    expect(errors('f(x) = x is Lines;'), [
      '`Lines` is the type of a port, and no value has it [Lines]',
    ]);
    expect(errors('f(x) = x is (int, String ->? int);'), [
      '`is` cannot test a value against a function type at run time [(int, String ->? int)]',
    ]);
  });
}
