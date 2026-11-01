/// The checker at the rule of low complexity (DESIGN.md Part G), continued: else patterns and
/// signatures of many type variables.
library;

import 'package:test/test.dart';

import '../../support/scaling.dart' as scaling;
import 'support.dart';

/// A function of `n` untyped parameters that returns them all, so that its signature has `n`
/// type variables.
String tuple(int n) {
  final xs = [for (var i = 0; i < n; i++) 'x$i'];
  return 'f(${[for (final x in xs) 'positional $x'].join(', ')}) = (${xs.join(', ')});\n';
}

void main() {
  test('many else patterns scale', () {
    // Each `else` with a pattern read every binder of the unit to find its own.
    scaling.check('n bindings each with an else pattern', 1000, (n) {
      final text = StringBuffer();
      for (var i = 0; i < n; i++) {
        text.write('v$i = #e(code: $i) else #e(code:) -> code;\n');
      }
      expect(info('$text').errors, isEmpty);
    });
  });

  test('a signature of many type variables scales', () {
    // Naming the variables looked for each among those named before (COMPLEXITY.md F28).
    expect(sig(tuple(2), 'f'), '(T, U) -> (T, U)');
    scaling.check('a signature of n type variables', 1000, (n) {
      expect(info(tuple(n)).errors, isEmpty);
    });
  });
}
