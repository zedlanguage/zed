/// The checker at the rule of low complexity (DESIGN.md Part G), continued: needs replayed
/// through calls, and atom payloads.
library;

import 'dart:collection';

import 'package:test/test.dart';
import 'package:zed/check.dart' show Shape, Ty;
import 'package:zed/kernel.dart' show Type;

import '../../support/scaling.dart' as scaling;
import 'support.dart';

/// `n` functions, each calling the one before twice with its untyped parameter, the first
/// taking a component of it; with `all`, each calls every one before it instead.
String fan(int n, bool all) {
  final src = StringBuffer('g0(positional t) = t[0];\n');
  for (var i = 1; i < n; i++) {
    final calls = all ? [for (var j = 0; j < i; j++) 'g$j(t)'] : ['g${i - 1}(t)', 'g${i - 1}(t)'];
    src.write('g$i(positional t) = ${calls.join(' + ')};\n');
  }
  return '$src';
}

/// The texts of [fan] at `n` and `factor * n`, built before the timing.
Map<int, String> fans(int n, bool all) => {
  for (final m in [n, scaling.factor * n]) m: fan(m, all),
};

/// `n` atoms, each with a payload of one field: of `n` names, or of one name with `n` shapes.
List<Ty> payloads(int n, bool oneName) => [
  for (var i = 0; i < n; i++)
    () {
      final name = oneName ? 'e' : 'e$i';
      return Ty.of(Type.atomWith(name, Type.top)).withPayloads({
        name: [
          Shape([], SplayTreeMap.of({'f$i': Ty.empty})),
        ],
      });
    }(),
];

void main() {
  test('needs replayed through a fan of calls scale', () {
    // Each of the two calls met the needs of the one before anew, so they doubled at each
    // function; a use met twice now gives what it gave the first time.
    expect(sig(fan(3, false), 'g2'), '(T) -> U for U in int | f64 | rat');
    final texts = fans(250, false);
    scaling.check('needs replayed through n functions, each calling the one before twice', 250, (
      n,
    ) {
      expect(info(texts[n]!).errors, isEmpty);
    });
  });

  test('the union of many atoms with payloads scales', () {
    final sides = {
      for (final n in [256, scaling.factor * 256]) n: (payloads(n, false), payloads(n, true)),
    };
    scaling.check('the union of n atoms with payloads', 256, (n) {
      final (names, shapes) = sides[n]!;
      var u = Ty.unionAll(names);
      expect(u.payloads.length, n);
      expect(u.payloads.values.every((v) => v != null), isTrue);
      u = Ty.unionAll(shapes);
      expect(u.payloads['e']?.length, n);
    });
  });
}
