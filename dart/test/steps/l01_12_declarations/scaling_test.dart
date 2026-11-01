/// Building units and writing their text are of order n log n in the length of the text, and
/// the depth of nested functions and `else if` chains is bounded by memory alone.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

import '../../support/scaling.dart';

List<Stmt> _unit(String text) {
  final tokens = lex(text);
  return unit(text, tokens, parse(text, tokens, 'Unit', top));
}

void main() {
  test('many functions and a long test table', () {
    check('build', 200, (n) {
      final stmts = _unit('${'f(x) = x test { 1 -> 1 }\n' * n}g(x) = x test { ${'1 -> 1, ' * n}}');
      expect((stmts.length, (stmts.last as FunctionDef).tests.length), (n + 1, n));
    });
  });

  test('nested functions', () {
    check('build', 200, (n) {
      Stmt s = _unit('${'f(x) { ' * n}x${' }' * n}').single;
      var depth = 0;
      while (true) {
        if (s case FunctionDef(body: Block(stmts: [final inner, ...]))) {
          (s, depth) = (inner, depth + 1);
        } else {
          break;
        }
      }
      expect((depth, '$s'), (n, '(return x)'));
    });
  });

  test('the text of nested functions and of a long sum', () {
    final built = <int, (Stmt, Stmt)>{};
    check('write', 125, (n) {
      final (def, sum) = built[n] ??= (
        _unit('${'f(x) { ' * n}x${' }' * n}').single,
        _unit('y = ${[for (var i = 0; i < 4 * n; i++) 'a$i'].join(' + ')};').single,
      );
      expect('$def'.length, 20 * n + 10);
      expect('$sum', startsWith('(= (y) ${'(+ ' * (4 * n - 1)}a0 a1)'));
    });
  });

  test('the text of functions nested deeper than the call stack', () {
    const n = 100000;
    final text = '${_unit('${'f(x) { ' * n}x${' }' * n}').single}';
    expect(text, startsWith('(def f (x) (block ' * 1000));
    expect(text, endsWith('(block (return x)))${'))' * (n - 1)}'));
  });

  test('a long else if chain', () {
    check('build', 200, (n) {
      final f = _unit('f(x) = ${'if x { 1 } else ' * n}{ 0 };').single as FunctionDef;
      var e = f.body;
      var length = 0;
      while (true) {
        if (e case If(:final otherwise)) {
          (e, length) = (otherwise, length + 1);
        } else {
          break;
        }
      }
      expect(length, n);
    });
  });
}
