/// Building a syntax tree is of order n log n in the length of the text, and its depth is
/// bounded by memory alone.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';

import '../../support/scaling.dart';
import 'ast.dart';

void main() {
  test('a long chain', () {
    check('build', 200, (n) {
      final e = ast('x${'.f(a, b: c)[i]?.g' * n}');
      expect(e, isA<Member>());
    });
  });

  test('deep nesting', () {
    check('build', 500, (n) {
      var e = ast('${'f((-' * n}1${'))' * n}');
      var depth = 0;
      while (true) {
        if (e case Call(positional: [Unary(e: final inner)])) {
          (e, depth) = (inner, depth + 1);
        } else {
          break;
        }
      }
      expect((depth, '$e'), (n, '1'));
    });
  });

  test('nested string holes', () {
    check('build', 100, (n) {
      expect(ast('${r'"${' * n}1${'}"' * n}'), isA<StrLit>());
    });
  });
}
