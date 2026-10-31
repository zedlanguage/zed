/// Every expression in the documentation's fences builds, or names the later layer of a form
/// inside it.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

import '../../support/fences.dart' as fences;

void main() {
  test('every expression in the fences builds or names its layer', () {
    var (built, later) = (0, 0);
    final wrong = <String>[];
    for (final f in fences.all()) {
      final tokens = lexFence(f.text);
      // Each tree, with the trees of the `${…}` holes in its tokens.
      final trees = [(tokens, parse(f.text, tokens, f.notation ? 'DocFence' : 'Unit', top))];
      while (trees.isNotEmpty) {
        final (tokens, tree) = trees.removeLast();
        final holes = [
          for (final t in tokens)
            if (t.tok case Str(:final parts))
              for (final p in parts)
                if (p case Hole(:final tokens)) tokens,
        ];
        for (final (k, h) in tree.holes.indexed) {
          trees.add((holes[k], h));
        }
        for (final node in tree.root.all) {
          if (node.name != 'Expr') continue;
          try {
            expr(f.text, tokens, tree, node);
            built++;
          } on BuildError catch (e) {
            if (e.message.contains(' is built from ')) {
              later++;
            } else {
              wrong.add('${f.at}: $e');
            }
          }
        }
      }
    }
    expect(wrong, isEmpty, reason: wrong.join('\n'));
    // 1512 and 309 at step L1.10, holes included; later steps build more.
    expect(built >= 1512 && built + later == 1821, isTrue, reason: 'built $built, later $later');
  });
}
