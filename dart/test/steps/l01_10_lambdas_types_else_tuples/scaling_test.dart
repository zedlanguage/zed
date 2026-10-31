/// Building lambdas, `else` chains, type tests and tuples is of order n log n in the length of
/// the text, and the depth of their nesting is bounded by memory alone.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';

import '../../support/scaling.dart';
import '../l01_09_postfix_chains/ast.dart';

void main() {
  test('a long else chain', () {
    check('build', 200, (n) {
      var e = ast('e${' else #a(f: #b, g:) -> d' * n}');
      var length = 0;
      while (true) {
        if (e case Else(:final of, pattern: AtomPattern(fields: [_, (_, null)]))) {
          (e, length) = (of, length + 1);
        } else {
          break;
        }
      }
      expect(length, n);
    });
  });

  test('nested lambdas', () {
    check('build', 500, (n) {
      var e = ast('${'(x, y: int = 0) -> ' * n}x');
      var depth = 0;
      while (true) {
        if (e case Lambda(params: [_, Param(type: TypeName())], :final body)) {
          (e, depth) = (body, depth + 1);
        } else {
          break;
        }
      }
      expect((depth, '$e'), (n, 'x'));
    });
  });

  test('a long arrow type', () {
    check('build', 200, (n) {
      final e = ast('f is (${'int -> ' * n}int)');
      var t = (e as Is).type;
      var depth = 0;
      while (true) {
        if (t case ArrowType(params: [TypeParam(type: TypeName())], :final result)) {
          (t, depth) = (result, depth + 1);
        } else {
          break;
        }
      }
      expect(depth, n);
    });
  });

  test('a long union and nested tuple types', () {
    check('build', 200, (n) {
      final e = ast('x is ${'int | ' * n}${'(#a, ' * n}int${')' * n}');
      final union = (e as Is).type as UnionType;
      var t = union.items.last;
      var depth = 0;
      while (true) {
        if (t case TupleType(items: [AtomType(), final inner])) {
          (t, depth) = (inner, depth + 1);
        } else {
          break;
        }
      }
      expect((union.items.length, depth), (n + 1, n));
    });
  });

  test('nested tuples', () {
    check('build', 500, (n) {
      var e = ast('${'(1, ' * n}2${')' * n}');
      var depth = 0;
      while (true) {
        if (e case Tuple(items: [IntLit(), final inner])) {
          (e, depth) = (inner, depth + 1);
        } else {
          break;
        }
      }
      expect(depth, n);
    });
  });
}
