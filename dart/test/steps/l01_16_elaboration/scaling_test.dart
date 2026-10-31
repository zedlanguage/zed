/// Elaboration at the rule of low complexity (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/elab.dart';
import 'package:zed/resolve.dart';

import '../../support/scaling.dart' as scaling;
import 'elab.dart';

/// `n` bindings, each written before the one it reads.
String chain(int n) =>
    [for (var i = 0; i < n - 1; i++) 'v$i = v${i + 1} + 1;\n', 'v${n - 1} = 0;\n'].join();

/// Blocks nested `n` deep, each binding a name that reads the top-level `c`.
String nested(int n) => [
  'c = 1;\nmain = ',
  for (var i = 0; i < n; i++) '{\ny$i = c;\n',
  'c\n',
  '}\n' * n,
  ';\n',
].join();

/// A function with `n` named parameters whose defaults each read the one after, and a call
/// that fills them all.
String defaults(int n) => [
  'f(positional x, ',
  for (var i = 0; i < n - 1; i++) 'd$i = d${i + 1}, ',
  'd${n - 1} = x) = x;\ny = f(1);\n',
].join();

/// `f0(x = 1) = x;`, then each `fi` defaulting to two calls of the one before, and a call of
/// the last.
String calling(int k) => [
  'f0(x = 1) = x;\n',
  for (var i = 1; i <= k; i++) 'f$i(x = f${i - 1}() + f${i - 1}()) = x;\n',
  'main = f$k();\n',
].join();

/// The elaboration of `text`, timed alone: the statements and resolution of each size are
/// built once, by the run that warms the code.
Unit timed(Map<int, (List<Stmt>, Resolution)> built, int n, String Function(int) text) {
  final (stmts, res) = built[n] ??= () {
    final s = stmtsOf(text(n));
    return (s, resolve(s));
  }();
  return elaborate(stmts, res);
}

void main() {
  final chains = <int, (List<Stmt>, Resolution)>{};
  final nests = <int, (List<Stmt>, Resolution)>{};
  final calls = <int, (List<Stmt>, Resolution)>{};

  test('many statements in reverse dependency order scale', () {
    // The next statement to elaborate was looked for among all of them, each time.
    scaling.check('n bindings written in reverse order', 4000, (n) {
      expect(timed(chains, n, chain).defs.first.name, 'v${n - 1}');
    });
    expect([for (final d in elab(chain(3)).defs) d.name], ['v2', 'v1', 'v0']);
  });

  test('deeply nested blocks scale', () {
    // Each scope read every use inside each of its statements, nested ones included.
    scaling.check('blocks nested n deep', 300, (n) => timed(nests, n, nested));
    expect(value(nested(3), 'main'), '1');
  });

  test('a call filling many chained defaults scales', () {
    scaling.check('a call filling n chained defaults', 500, (n) {
      expect(timed(calls, n, defaults).defs.last.name, 'y');
    });
    expect(term(defaults(2), 'y'), '{ x = 1; d1 = x; d0 = d1; f(x, d0, d1) }');
  });

  test('defaults calling functions with defaults scale', () {
    // Each call leaving a parameter out elaborated its default again, and the default's own
    // calls theirs, so the work doubled with each function. The sizes are small so that such
    // growth fails the test in seconds rather than never finishing.
    final built = <int, (List<Stmt>, Resolution)>{};
    scaling.check('a chain of n defaults calling defaults', 2, (k) => timed(built, k, calling));
    expect(value(calling(3), 'main'), '8');
  });

  test('a long cycle is reported once, in order along it', () {
    final cycle = chain(4).replaceFirst('v3 = 0', 'v3 = v0');
    expect(
      one(cycle),
      '`v0`, `v1`, `v2`, `v3` are defined in terms of each other: '
      'recursion arrives at layer L6 [v0 = v1 + 1;]',
    );
  });
}
