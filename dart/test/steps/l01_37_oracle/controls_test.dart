/// Negative controls: an engine that changes a value, drops a wave's writes or fails is
/// caught, and the mismatch names the binding or wave and both outcomes.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/native.dart' as native;
import 'package:zed/run.dart' show RunError, Through;

import '../../support/oracle.dart';

const lambdas = 'inc = x -> x + 1;\ntwice(positional f) = x -> f(f(x));\nfive = twice(inc)(3);\n';

const greeting =
    'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- "Hello, " ++ (stdin[1] else "") ++ "!";\n}\n';

final Through _fused = native.through(true);

Value offByOne(Term t, Evaluator ev) => switch (_fused(t, ev)) {
  Int(:final value) => Int(value + 1),
  final v => v,
};

Value silent(Term t, Evaluator ev) => const Tuple([]);

Value failing(Term t, Evaluator ev) => throw const RunError('out of memory');

void main() {
  test('a changed integer is caught with both values', () {
    final r = unit(lambdas, [('off by one', offByOne)]);
    expect(r.mismatches, [
      'binding `five`: the interpreter gives the value 5, and off by one gives the value 6',
    ]);
    expect(unit(lambdas, [('native', _fused)]).mismatches, isEmpty);
  });

  test('dropped writes are caught in the wave', () {
    final (r, want) = program(greeting, 'Ada\n'.codeUnits, [('silent', silent)]);
    expect(want, r'port `stdout` writes "Hello, Ada!\n"');
    expect(r.mismatches, [
      r'the wave: the interpreter gives port `stdout` writes "Hello, Ada!\n", and silent '
          'gives no writes',
    ]);
  });

  test('a failing engine is caught everywhere', () {
    final r = unit(lambdas, [('failing', failing)]);
    expect((r.compared, r.mismatches.length), (2, 1));
    final (w, _) = program(greeting, 'Ada\n'.codeUnits, [('failing', failing)]);
    expect(w.mismatches, [
      r'the wave: the interpreter gives port `stdout` writes "Hello, Ada!\n", and failing '
          'gives the error `out of memory`',
    ]);
  });
}
