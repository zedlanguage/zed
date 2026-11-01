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

/// A string of 1000 characters ending in `i`, as a type.
Type long(int i) => Type.lit(Str('${'s' * 1000}$i'))!;

/// The tuple `(… ((long(b), long(b)), long(b + 1)) …, long(b + d - 1))`, nested `d` deep.
Type chain(int d, int b) {
  var t = long(b);
  for (var i = 0; i < d; i++) {
    t = Type.tuple([t, long(b + i)]);
  }
  return t;
}

void main() {
  test('the text of a deeply nested type scales', () {
    // Each type's text was made from copies of the texts of the types inside it. Each run
    // makes new types, whose texts are not yet made.
    var b = 0;
    scaling.check('the text of a tuple nested n deep', 75, (d) {
      expect('${chain(d, b += 1000000)}'.length, greaterThan(1000 * d));
    });
    expect('${chain(2, 0)}', startsWith('(tuple (tuple "sss'));
  });

  test('the text of a type holding the complement of an atom payload is made', () {
    // The complement is a type made when the text is, and must be the same one each time.
    expect(
      '${Type.top - Type.atomWith('a', Type.tuple([Type.integer]))}',
      r'(| bool int rat f64 String (\ #_ (#a (tuple int))) tuple struct morphism)',
    );
  });

  test('the text of a type nested deeper than the call stack is made', () {
    var t = Type.lit(Int(0))!;
    for (var i = 1; i < 100000; i++) {
      t = Type.tuple([t, Type.lit(Int(i))!]);
    }
    expect('$t', allOf(startsWith('(tuple ' * 1000), endsWith(' 99998) 99999)')));
  });

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
