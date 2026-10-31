/// Every block in expression position in the documentation's fences builds, or names the later
/// layer of a form inside it. A block in a declaration's body is built with the declaration,
/// from step L1.12.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

import '../../support/fences.dart' as fences;

void main() {
  test('every block in expression position builds or names its layer', () {
    var (built, later) = (0, 0);
    final wrong = <String>[];
    for (final f in fences.all()) {
      final tokens = lexFence(f.text);
      final tree = parse(f.text, tokens, f.notation ? 'DocFence' : 'Unit', top);
      for (final p in tree.root.all) {
        if (!const {'Primary', 'Lambda', 'ElseTail'}.contains(p.name)) continue;
        for (final n in p.kids) {
          if (n.name != 'Block') continue;
          try {
            expr(f.text, tokens, tree, n);
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
    expect((built, later), (1, 0));
  });
}
