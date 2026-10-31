/// The printer at the rule of low complexity (DESIGN.md Part G).
library;

import 'dart:math' as math;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/scaling.dart' as scaling;

/// Shape `k` nested `d` deep: lambdas, calls in argument position, calls in head position.
Term shape(int k, int d) {
  Term t = Var(const ['x', 'x', 'f'][k]);
  for (var i = 0; i < d; i++) {
    t = switch (k) {
      0 => Lam(const ['y'], t),
      1 => App(const Var('g'), [t, const Var('z')]),
      _ => App(t, const [Var('a')]),
    };
  }
  return t;
}

const shapes = ['lambdas', 'calls in argument position', 'calls in head position'];

/// What a run returns, read so that the run is not optimized away.
var sink = 0;

void main() {
  test('the printer scales with depth', () {
    for (final (k, what) in shapes.indexed) {
      // Each size's term is built once, so only the printer is timed.
      final terms = <int, Term>{};
      scaling.check('one line, nested $what, by depth', k == 2 ? 16000 : 500, (d) {
        sink += '${terms[d] ??= shape(k, d)}'.length;
      });
      // Broken, calls nested in argument position put depth `i` at indentation `2i`, so their
      // text is quadratic in the depth: they are measured by the text's length, the depth
      // growing as its square root.
      final (n, depth) = k == 1 ? (250000, (int m) => math.sqrt(m).floor()) : (500, (int m) => m);
      scaling.check('width 80, nested $what, by text', n, (m) {
        sink += pretty(terms[depth(m)] ??= shape(k, depth(m)), 80).length;
      });
    }
  });

  test('nested shapes break as before', () {
    final [lam, arg, head] = [
      for (final k in [0, 1, 2]) shape(k, 3),
    ];
    expect('$lam', 'y -> y -> y -> x');
    expect('$arg', 'g(g(g(x, z), z), z)');
    expect('$head', '((f(a))(a))(a)');
    expect(pretty(arg, 12), 'g(\n  g(\n    g(x, z),\n    z\n  ),\n  z\n)');
    expect(pretty(head, 8), '((f(a))(a))(\n  a\n)');
    expect(pretty(lam, 10), 'y -> y -> y -> x');
  });
}
