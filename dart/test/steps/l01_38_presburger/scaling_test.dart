/// The Omega test at the rule of low complexity (DESIGN.md Part G). An inexact elimination has
/// two shadows that both recurse, so the order and the checks before them decide whether the
/// work doubles with each variable: the dark shadow is solved first, since a point of it
/// settles the problem, and an empty problem is first tried by the real shadows alone. Each
/// family below doubles without one of the two: `chain(v, 3)` without the order, `rising`
/// without the real shadows. Each formula is built before it is timed.
library;

import 'package:test/test.dart';
import 'package:zed/presburger.dart';

import '../../support/scaling.dart' as scaling;

Lin x(int i) => Lin.atom(Sym('x$i'));

Lin k(int c) => Lin.constant(BigInt.from(c));

BigInt big(int c) => BigInt.from(c);

/// `3·x[i+1] >= 2·x[i] + 1` and `2·x[i] + k >= 3·x[i+1]` for `i < v`: no elimination is exact,
/// the chain has a point when `k >= 1`, and none when `k == 0`.
Formula chain(int v, int c) => Formula.and([
  for (var i = 0; i < v; i++) ...[
    Con.ge(x(i + 1).times(big(3)), x(i).times(big(2)).plus(k(1))),
    Con.ge(x(i).times(big(2)).plus(k(c)), x(i + 1).times(big(3))),
  ],
]);

/// `3·x[i] + 1 <= 2·x[i+1] <= 3·x[i] + 5` for `i < v`, `x[0] >= 0` and `x[v] <= 0`: empty, since
/// each `x[i+1]` is above `x[i]`, but no single step shows it.
Formula rising(int v) => Formula.and([
  Con.ge(x(0), Lin.zero),
  Con.ge(Lin.zero, x(v)),
  for (var i = 0; i < v; i++) ...[
    Con.ge(x(i + 1).times(big(2)), x(i).times(big(3)).plus(k(1))),
    Con.ge(x(i).times(big(3)).plus(k(5)), x(i + 1).times(big(2))),
  ],
]);

/// Times `satisfiable` on the formulas of [make] at `n` and `8n` variables, built first and each
/// run three times before timing.
void scales(String what, int n, Formula Function(int) make) {
  final inputs = {n: make(n), scaling.factor * n: make(scaling.factor * n)};
  for (var i = 0; i < 3; i++) {
    for (final f in inputs.values) {
      satisfiable(f);
    }
  }
  scaling.check(what, n, (m) => satisfiable(inputs[m]!));
}

void main() {
  test('chains of inexact eliminations are answered', () {
    for (var v = 1; v <= 15; v++) {
      final m = satisfiable(chain(v, 3)) ?? (throw StateError('the chain of $v has a point'));
      expect(chain(v, 3).holds(m), isTrue, reason: '$m');
      expect(satisfiable(chain(v, 0)), isNull, reason: 'the chain of $v is empty');
      expect(satisfiable(rising(v)), isNull, reason: 'the rising chain of $v is empty');
    }
  });

  test('a chain of inexact eliminations with a point scales', () {
    scales('the chain with a point', 32, (v) => chain(v, 3));
  });

  test('an empty chain scales', () {
    scales('the empty chain', 256, (v) => chain(v, 0));
  });

  test('a rising chain scales', () {
    scales('the rising chain', 128, rising);
  });
}
