/// Loose atoms, the failure channel: `else` defaults them, the pattern form handles the one it
/// names, and they flow through the operators unchanged.
library;

import 'package:test/test.dart';

import '../l01_16_elaboration/elab.dart';
import '../l01_26_type_resolution/support.dart';

/// A lookup's result: a value, a missing row, or a stored NULL.
const lookup = 'positional x: int | #notFound | #none';

void main() {
  test('else defaults every loose atom', () {
    const t = 'f($lookup) = x else 0;\n';
    expect(sig(t, 'f'), '(int | #none | #notFound) -> int');
    const run = '${t}a = f(#none);\nb = f(#notFound);\nc = f(4);\n';
    expect(value(run, 'a'), '0');
    expect(value(run, 'b'), '0');
    expect(value(run, 'c'), '4');
  });

  test('the pattern form handles the atom it names and keeps the rest', () {
    const t = 'f($lookup) = x else #notFound -> -1;\n';
    expect(sig(t, 'f'), '(int | #none | #notFound) -> int | #none');
    const run = '${t}a = f(#none);\nb = f(#notFound);\nc = f(4);\n';
    expect(value(run, 'a'), '#none');
    expect(value(run, 'b'), '-1');
    expect(value(run, 'c'), '4');
    // Two patterns in turn handle both, and the result is the plain number.
    const both = 'f($lookup) = (x else #notFound -> -1) else #none -> 0;\n';
    expect(sig(both, 'f'), '(int | #none | #notFound) -> int');
    // A pattern naming an atom the value cannot hold handles nothing.
    const other = 'f($lookup) = x else #empty -> 0;\n';
    expect(sig(other, 'f'), '(int | #none | #notFound) -> int | #none | #notFound');
  });

  test('the three absences stay three facts', () {
    // Through an operator each absence flows unchanged, and two at once merge into `#errs`.
    expect(
      sig('f(positional x: int | #notFound, positional y: int | #none) = x + y;\n', 'f'),
      '(int | #notFound, int | #none) -> int | #errs(_) | #none | #notFound',
    );
    const run =
        'f(positional x: int | #notFound, positional y: int | #none) = x + y;\n'
        'a = f(#notFound, 1);\nb = f(1, #none);\nc = f(#notFound, #none);\n';
    expect(value(run, 'a'), '#notFound');
    expect(value(run, 'b'), '#none');
    expect(value(run, 'c'), '#errs({#none, #notFound})');
  });

  test('a loose atom flows through safe navigation', () {
    const t = 'f(positional x: int | #notFound) = x?.abs;\n';
    expect(sig(t, 'f'), '(int | #notFound) -> int | #notFound');
    expect(typeErrors(t), isEmpty);
    const run = '${t}a = f(#notFound);\nb = f(-3);\n';
    expect(value(run, 'a'), '#notFound');
    expect(value(run, 'b'), '3');
  });

  test('a declared function does not take an atom its type omits', () {
    expect(
      typeErrors(
        'g(positional n: int) = n + 1;\n'
        'f(positional x: int | #notFound) = g(x);\n',
      ),
      ['`g` does not take (#notFound) [g(x)]'],
    );
  });
}
