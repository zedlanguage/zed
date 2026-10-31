/// Types at the rule of low complexity (DESIGN.md Part G). A union or intersection of `n` types
/// was built one type at a time, and each tuple type joined to a decision diagram of the ones
/// before it, so `n` tuple types of one length took `O(n²)`; they are now joined in pairs.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/scaling.dart' as scaling;
import '../l01_16_elaboration/elab.dart';

/// `n` distinct pairs of one length.
List<Type> pairs(int n) => [
  for (var i = 0; i < n; i++) Type.tuple([Type.atom('a$i'), Type.integer]),
];

/// A test of `x` against the union of `n` such pairs.
String union(int n) => 'f(x) = x is ${[for (var i = 0; i < n; i++) '(#a$i, int)'].join(' | ')};\n';

void main() {
  test('a union of many tuple types scales', () {
    final texts = <int, String>{};
    scaling.check('is against a union of n pairs', 250, (n) {
      expect(term(texts[n] ??= union(n), 'f'), contains('(is (| '));
    });
    final built = <int, List<Type>>{};
    scaling.check('the union of n pairs', 250, (n) {
      expect(Type.unionAll(built[n] ??= pairs(n)).isEmpty, isFalse);
    });
    scaling.check('the intersection of n complements of pairs', 250, (n) {
      expect(Type.meetAll([for (final p in built[n] ??= pairs(n)) ~p]).isEmpty, isFalse);
    });
  });

  test('the union taken one type at a time does not scale', () {
    // The negative control: the order the test above guards against is caught.
    final built = <int, List<Type>>{};
    expect(
      () => scaling.check('the union of n pairs, one at a time', 200, (n) {
        (built[n] ??= pairs(n)).fold(Type.empty, (a, b) => a | b);
      }),
      throwsStateError,
    );
  });
}
