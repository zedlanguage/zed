/// Every unit in the documentation's fences builds, or names the later layer of a form in it.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

import '../../support/fences.dart' as fences;

void main() {
  test('every unit builds or names its layer', () {
    var (built, later) = (0, 0);
    final wrong = <String>[];
    for (final f in fences.all().where((f) => !f.notation)) {
      final tokens = lexFence(f.text);
      try {
        unit(f.text, tokens, parse(f.text, tokens, 'Unit', top));
        built++;
      } on BuildError catch (e) {
        if (e.message.contains(' is built from layer L')) {
          later++;
        } else {
          wrong.add('${f.at}: $e');
        }
      }
    }
    expect(wrong, isEmpty, reason: wrong.join('\n'));
    // 23 and 113 at step L1.12; later steps build more.
    expect(built >= 23 && built + later == 136, isTrue, reason: 'built $built, later $later');
  });
}
