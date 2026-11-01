/// Common subexpressions: a node whose canonical form has the address of one already in its
/// region is not added again.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' as zir;
import 'package:zed/zir.dart' hide print;

import '../l01_32_canonical_zir/zir.dart' show sameGraph;
import 'lowering.dart';

void main() {
  test('a repeated product is one node', () {
    // `x * 2 + x * 2`: one product, one sum.
    final g = graph('f(positional x) = x * 2 + x * 2\ntest { 3 -> 12 }\n', 'f');
    expect(count(g, 'prim'), 2);
  });

  test('let names do not separate equal nodes', () {
    // `a = x + 1; b = x + 1; a * b`: the two sums differ only in the name hint.
    final body = let_(
      'a',
      prim(Prim.add, [var_('x'), lit(1)]),
      let_('b', prim(Prim.add, [var_('x'), lit(1)]), prim(Prim.mul, [var_('a'), var_('b')])),
    );
    final t = App(lam(['x'], body), [lit(6)]);
    final g = lower(t);
    // The call of a literal lambda is lowered in place, with `x` the constant 6.
    expect((count(g, 'prim'), count(g, 'lambda'), g.nodes.length), (2, 0, 2));
    // The sum keeps the first name as a hint, and the graph prints and reads back.
    final text = zir.print(g);
    expect(text, contains('hint name "a"'));
    expect(text, isNot(contains('hint name "b"')));
    expect(sameGraph(parse(text), g), isTrue);
    expect(roundTrip(t), '49');
  });

  test('equal lambdas are one node', () {
    Term inc() => lam(['n'], prim(Prim.add, [var_('n'), lit(1)]));
    expect(count(lower(prim(Prim.tuple, [inc(), inc()])), 'lambda'), 1);
    // Different bodies stay apart.
    final dec = lam(['n'], prim(Prim.sub, [var_('n'), lit(1)]));
    expect(count(lower(prim(Prim.tuple, [inc(), dec])), 'lambda'), 2);
  });

  test('nodes in different regions stay apart', () {
    // `x + 1` inside each arm is a node of that arm's region, not of the root.
    final t = App(
      lam(
        ['x'],
        If(
          prim(Prim.lt, [var_('x'), lit(0)]),
          prim(Prim.add, [var_('x'), lit(1)]),
          prim(Prim.add, [var_('x'), lit(1)]),
        ),
      ),
      [
        prim(Prim.neg, [lit(5)]),
      ],
    );
    expect(count(lower(t), 'prim'), 4);
    expect(roundTrip(t), evaluate(t));
  });
}
