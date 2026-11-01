/// The checker at the rule of low complexity (DESIGN.md Part G). A signature search tried
/// each carrier for each untyped parameter, up to a budget, and began each run from a copy of
/// everything found so far. An untyped parameter is now a class of a union-find forest, and
/// each body is checked once.
library;

import 'package:test/test.dart';

import '../../support/scaling.dart' as scaling;
import 'support.dart';

/// A function of `n` untyped parameters, all added together.
String sum(int n) {
  final xs = [for (var i = 0; i < n; i++) 'x$i'];
  return 'f(${[for (final x in xs) 'positional $x'].join(', ')}) = ${xs.join(' + ')};\n';
}

/// `n` functions, each calling the one before with its untyped parameter.
String chain(int n) {
  final src = StringBuffer('g0(positional x) = -x;\n');
  for (var i = 1; i < n; i++) {
    src.write('g$i(positional x) = g${i - 1}(x) * x;\n');
  }
  return '$src';
}

void main() {
  test('searching the signatures of many functions scales', () {
    // Twenty constants for each function, each adopting its literal with no search, so that
    // what the unit has found is large beside the searches.
    scaling.check('the signatures of n functions beside 20n constants', 25, (n) {
      final text = StringBuffer();
      for (var j = 0; j < 20 * n; j++) {
        text.write('k$j = 0.5 + $j;\n');
      }
      for (var i = 0; i < n; i++) {
        text.write('f$i(x) = x / ${i + 1};\n');
      }
      final found = info('$text');
      expect(found.errors, isEmpty);
      expect(found.sigs, hasLength(n));
      expect(found.adopt, hasLength(21 * n));
    });
  });

  test('a function of many untyped parameters scales', () {
    // The search tried the product of the carriers of the parameters, 3^n, until its budget
    // of 256 combinations gave `_`. The parameters now merge into one class, once each.
    // The body is a chain of `n` additions, nested `n` deep.
    expect(sig(sum(3), 'f'), '(T, T, T) -> T for T in int | f64 | rat');
    final wide = sig(sum(40), 'f');
    expect(wide, endsWith(') -> T for T in int | f64 | rat'));
    scaling.check('a function of n untyped parameters', 400, (n) {
      expect(info(sum(n)).errors, isEmpty);
    });
  });

  test('a chain of functions with untyped parameters scales', () {
    // Each takes the bound of the one it calls, by its signature, with no search.
    expect(sig(chain(3), 'g2'), '(T) -> T for T in int | f64 | rat');
    scaling.check('a chain of n functions', 400, (n) {
      final found = info(chain(n));
      expect(found.errors, isEmpty);
      expect(found.sigs, hasLength(n));
    });
  });
}
