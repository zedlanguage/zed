/// Every postfix chain in the documentation's fences builds, or names the later layer of a
/// form inside it.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

import '../../support/fences.dart' as fences;

void main() {
  test('every chain in the fences builds or names its layer', () {
    var (built, later) = (0, 0);
    final wrong = <String>[];
    for (final f in fences.all()) {
      final tokens = lexFence(f.text);
      final tree = parse(f.text, tokens, f.notation ? 'DocFence' : 'Unit', top);
      for (final node in tree.root.all) {
        if (node.name != 'Postfix' || node.kids.length < 2) continue;
        try {
          final e = expr(f.text, tokens, tree, node);
          built++;
          final span = (start: tokens[node.start].span.start, end: tokens[node.end - 1].span.end);
          if (e.span != span) wrong.add('${f.at}: span of $e');
        } on BuildError catch (e) {
          if (e.message.contains(' is built from ')) {
            later++;
          } else {
            wrong.add('${f.at}: $e');
          }
        }
      }
    }
    expect(wrong, isEmpty, reason: wrong.join('\n'));
    // 512 and 170 at step L1.9; later steps build more.
    expect(built >= 512 && built + later == 682, isTrue, reason: 'built $built, later $later');
  });
}
