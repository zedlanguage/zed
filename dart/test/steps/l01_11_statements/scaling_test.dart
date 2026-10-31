/// Building blocks is of order n log n in the length of the text, and the depth of their
/// nesting is bounded by memory alone.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';

import '../../support/scaling.dart';
import '../l01_09_postfix_chains/ast.dart';

void main() {
  test('a long block', () {
    check('build', 200, (n) {
      final e = ast('x -> { ${'a, _ = x; ' * n}x }');
      final stmts = ((e as Lambda).body as Block).stmts;
      expect((stmts.whereType<Bind>().length, '${stmts.last}'), (n, '(return x)'));
    });
  });

  test('nested blocks', () {
    check('build', 200, (n) {
      var e = ast('${'x -> { y = 1; ' * n}x${' }' * n}');
      var depth = 0;
      while (true) {
        if (e case Lambda(body: Block(stmts: [Bind(), Return(values: [final v])]))) {
          (e, depth) = (v, depth + 1);
        } else {
          break;
        }
      }
      expect((depth, '$e'), (n, 'x'));
    });
  });
}
