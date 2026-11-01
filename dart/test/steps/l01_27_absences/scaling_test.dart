/// The checker on a chain of loose atoms, at the rule of low complexity (DESIGN.md Part G).
/// `e else d` and each operator strip the loose atoms of their operands; the strip
/// complemented every loose atom so far, so a chain of n failures took O(n²) (COMPLEXITY.md
/// F21). Each run checks the chain twice: the emptiness results were kept from one unit to
/// the next, and the second check compared each of its types in full with an equal kept one,
/// which also took O(n²) (COMPLEXITY.md F32).
library;

import 'package:test/test.dart';

import '../../support/scaling.dart' as scaling;
import '../l01_26_type_resolution/support.dart';

/// `x = #e0 + #e1 + … + #e(n-1);`
String chain(int n) => 'x = ${[for (var i = 0; i < n; i++) '#e$i'].join(' + ')};\n';

void main() {
  test('a chain of many failure atoms scales', () {
    scaling.check('a chain of n failure atoms, checked twice', 1000, (n) {
      final text = chain(n);
      for (var i = 0; i < 2; i++) {
        expect(info(text).errors, isEmpty);
      }
    });
  });
}
