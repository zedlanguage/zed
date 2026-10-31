/// The canonicalizer at the rule of low complexity (DESIGN.md Part G). The rules rename one
/// binder per step, and each step walks the whole term to find the binder and its scope, so a
/// term of `n` binders takes `O(n^2)` steps at least; the facet rule swaps one pair of facets
/// per step, `O(F^2)` steps of `O(F)` each. The one-pass normal form must be near linear.
library;

import 'package:test/test.dart';
import 'package:zed/canon.dart';
import 'package:zed/kernel.dart';

import '../../support/scaling.dart' as scaling;
import 'harness.dart';

/// `let x0 = 0 in let x1 = x0 + 1 in … x{n-1}`.
Term chain(int n) {
  var body = var_('x${n - 1}');
  for (var i = n - 1; i >= 0; i--) {
    body = let_('x$i', i == 0 ? lit(0) : prim(Prim.add, [var_('x${i - 1}'), lit(1)]), body);
  }
  return body;
}

void main() {
  test('canonicalizing many binders scales', () {
    scaling.check('canonicalizing a chain of n binders', 250, (n) {
      expect(canonicalize(def('f', chain(n))).body, isA<Let>());
    });
  });

  test('sorting many facets scales', () {
    scaling.check('canonicalizing n facets in reverse order', 250, (n) {
      final d = def('f', lit(0));
      for (var i = n - 1; i >= 0; i--) {
        d.facets.add(Facet('units', Int(i ~/ 2), hint: i % 3 == 0));
      }
      final c = canonicalize(d);
      for (var i = 0; i + 1 < c.facets.length; i++) {
        expect(c.facets[i].compareTo(c.facets[i + 1]), lessThan(0));
      }
      expect(c.facets.every((f) => !f.hint), isTrue);
    });
  });
}
