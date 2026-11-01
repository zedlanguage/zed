/// The oracle against the size of what it compares (the rule of low complexity, DESIGN.md
/// Part G): a unit of many bindings, a wave of many lines, and a report of many mismatches
/// each take time near linear in their number. Each input is built, and each unit compiled,
/// before it is timed.
library;

import 'package:test/test.dart';
import 'package:zed/elab.dart' show Unit;
import 'package:zed/kernel.dart';
import 'package:zed/query.dart' show Db;
import 'package:zed/run.dart' show direct;

import '../../support/oracle.dart';
import '../../support/scaling.dart' as scaling;

/// `x0 = 0; x1 = 1; …`: `n` first-order bindings, compiled.
Unit numbers(int n) => Db().front([for (var i = 0; i < n; i++) 'x$i = $i;\n'].join()).$2;

const echo = 'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin[1] else "";\n}\n';

/// `n` lines of input.
List<int> lines(int n) => [for (var i = 0; i < n; i++) ...'line $i\n'.codeUnits];

/// A report of `n` mismatches.
Report mismatched(int n) => Report()..mismatches.addAll([for (var i = 0; i < n; i++) 'm$i']);

/// The interpreter with every integer one more.
Value offByOne(Term t, Evaluator ev) => switch (direct(t, ev)) {
  Int(:final value) => Int(value + 1),
  final v => v,
};

/// Times [run] on the inputs of [make] at `n` and `8n`, built first. Both sizes are run three
/// times before timing: with fewer, the first timing at `n` is up to twice the later ones, and
/// a quadratic runtime can pass on it.
void scales<T>(String what, int n, T Function(int) make, void Function(T) run) {
  final inputs = {n: make(n), scaling.factor * n: make(scaling.factor * n)};
  for (var i = 0; i < 3; i++) {
    run(inputs[n] as T);
    run(inputs[scaling.factor * n] as T);
  }
  scaling.check(what, n, (m) => run(inputs[m] as T));
}

void main() {
  test('the inputs are compared as they should be', () {
    expect(bindings(numbers(3), natives).compared, 6);
    expect(bindings(numbers(3), [('off by one', offByOne)]).mismatches, [
      'binding `x0`: the interpreter gives the value 0, and off by one gives the value 1',
      'binding `x1`: the interpreter gives the value 1, and off by one gives the value 2',
      'binding `x2`: the interpreter gives the value 2, and off by one gives the value 3',
    ]);
    final (r, want) = program(echo, lines(2), natives);
    expect(r.mismatches, isEmpty);
    expect(want, r'port `stdout` writes "line 0\n"');
    expect((Report()..add('at', mismatched(2))).mismatches, ['at: m0', 'at: m1']);
  });

  test('a unit of many bindings scales', () {
    scales('a unit of n bindings, each run natively', 250, numbers, (Unit u) {
      expect(bindings(u, natives).mismatches, isEmpty);
    });
  });

  test('a unit of many bindings scales in the interpreter', () {
    scales('a unit of n bindings, each mismatched', 1000, numbers, (Unit u) {
      expect(bindings(u, [('off by one', offByOne)]).mismatches, isNotEmpty);
    });
  });

  test('a wave of many lines scales', () {
    scales('a wave of n lines', 2000, lines, (List<int> input) {
      expect(program(echo, input, natives).$1.mismatches, isEmpty);
    });
  });

  test('a report of many mismatches scales', () {
    scales('a report of n mismatches, added', 10000, mismatched, (Report r) {
      expect((Report()..add('at', r)).mismatches, isNotEmpty);
    });
  });
}
