/// Each kernel form the L1 surface does not yet write, lowered and raised back: families,
/// reindexing, discards, folds, both fixpoints, generation loops and nested patterns, on the
/// small programs of step M0.9.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' show lower;

import '../../support/kernel.dart' hide count;
import 'lowering.dart';

/// Checks that `t` keeps its value through ZIR and that its graph has `n` nodes of `op`.
void keeps(Term t, String op, int n) {
  expect(roundTrip(t), evaluate(t));
  expect(count(lower(t), op), n, reason: '$op nodes');
}

Value floats() => Family.of([
  for (final (k, x) in [(0, 0.1), (1, 0.2), (2, 0.3)]) (Int(k), Float(x)),
]);

void main() {
  test('word count reindexes then folds', () {
    final doc = linesOf([
      ['the', 'cat', 'sat'],
      ['the', 'end'],
    ]);
    final kf = lam(['p', 'w'], path([var_('w'), key(var_('p'), 0), key(var_('p'), 1)]));
    final ones = reindex(lit(doc), kf, lam(['p', 'w'], lit(1)));
    final perLine = foldAt(ones, 3, const PrimFn(Prim.add));
    final t = foldAt(perLine, 2, const PrimFn(Prim.add));
    keeps(t, 'reindex', 1);
    keeps(t, 'fold', 2);
  });

  test('a float fold keeps its identity and its tree', () {
    final plus = lam(['a', 'b'], add(var_('a'), var_('b')));
    keeps(fold(lit(floats()), plus), 'fold', 1);
    final exact = fold(lit(floats()), const PrimFn(Prim.add), lit(Float(0.0)));
    expect(roundTrip(exact), '0.6');
    // An empty family folds to the identity, which the graph keeps as the fold's third input.
    final empty = fold(lit(const Family.empty()), const PrimFn(Prim.add), lit(7));
    expect(roundTrip(empty), '7');
  });

  test('a family reads a computed rate as a capture', () {
    final bands = lit(
      Family.set([
        for (final b in [100, 250, 1000]) Int(b),
      ]),
    );
    final t = let_(
      'rate',
      add(lit(2), lit(3)),
      fam(
        bands,
        'b',
        prim(Prim.sub, [
          prim(Prim.intDiv, [var_('b'), var_('rate')]),
          var_('rate'),
        ]),
      ),
    );
    keeps(t, 'fam', 1);
    final node = lower(t).nodes.firstWhere((n) => n.op.name == 'fam');
    // The domain, then the rate, read twice but captured once; the region takes the key, then
    // the rate.
    expect(node.inputs.length, 2);
    expect(node.regions[0].args.length, 2);
  });

  test('discard keeps categories and stocked items', () {
    final stock = Family.fromLeaves([
      for (final (c, i, n) in [('fruit', 'apple', 3), ('fruit', 'fig', 0), ('veg', 'kale', 0)])
        ([s(c), s(i)], Int(n)),
    ]);
    final sel = lam(
      ['p', 'v'],
      If(
        prim(Prim.eq, [
          prim(Prim.pathLen, [var_('p')]),
          lit(1),
        ]),
        lit(true),
        prim(Prim.gt, [var_('v'), lit(0)]),
      ),
    );
    keeps(discard(lit(stock), sel), 'discard', 1);
  });

  test('reachability is a lattice fixpoint', () {
    final edges = Family.set([
      for (final (a, b) in [('lhr', 'jfk'), ('jfk', 'sfo'), ('cdg', 'lhr'), ('syd', 'akl')])
        Tuple([s(a), s(b)]),
    ]);
    final fromReached = discard(
      lit(edges),
      lam(['p', 'e'], found(get(var_('r'), nth(var_('e'), 0)))),
    );
    final targets = groupBy(fromReached, (e) => nth(e, 1));
    final t = fixLattice(
      lit(Family.set([s('cdg')])),
      lam(['r'], fam(targets, 'k', var_('k'))),
      const PrimFn(Prim.union),
    );
    keeps(t, 'fix', 1);
  });

  test('fibonacci is a definedness fixpoint', () {
    final domain = lit(Family.set([for (var i = 0; i <= 20; i++) Int(i)]));
    final t = fixDefined(domain, (self, i) {
      Term at(int d) => get(self, prim(Prim.sub, [i, lit(d)]));
      return If(prim(Prim.lt, [i, lit(2)]), i, add(at(1), at(2)));
    });
    keeps(t, 'fix', 1);
  });

  test('an org chart matches inside a fixpoint', () {
    final managers = lit(Family.of([(s('bo'), s('ann')), (s('cy'), s('bo'))]));
    final domain = lit(Family.set([s('ann'), s('bo'), s('cy')]));
    final t = fixDefined(
      domain,
      (self, i) => Match(add(get(self, get(managers, i)), lit(1)), [
        (const AtomP('notFound'), lit(0)),
        (const BindP('d'), var_('d')),
      ]),
    );
    keeps(t, 'match', 1);
  });

  test('a running balance is a generation loop', () {
    final ledger = Family.of([
      for (final (t, x) in [(0, 500), (1, -200), (2, -450)]) (Int(t), Int(x)),
    ]);
    final step = lam(
      ['f'],
      prim(Prim.tuple, [
        add(nth(var_('f'), 0), lit(1)),
        add(nth(var_('f'), 1), get(lit(ledger), nth(var_('f'), 0))),
      ]),
    );
    for (final pos in GuardPos.values) {
      final guard = lam(
        ['f'],
        If(
          prim(Prim.lt, [nth(var_('f'), 1), lit(0)]),
          lit(const Atom('overdrawn')),
          prim(Prim.lt, [nth(var_('f'), 0), lit(3)]),
        ),
      );
      final t = Gen(prim(Prim.tuple, [lit(0), lit(0)]), step, guard, pos);
      keeps(t, 'gen', 1);
    }
  });

  test('nested patterns bind in preorder', () {
    final arms = [
      (
        const TupleP([BindP('n'), LitP(Int(0))]),
        prim(Prim.concat, [var_('n'), lit(': out of stock')]),
      ),
      (
        const AtomP('parseError', [BindP('pos'), BindP('msg')]),
        prim(Prim.concat, [
          var_('msg'),
          prim(Prim.show, [var_('pos')]),
        ]),
      ),
      (const WildP(), lit('ok')),
    ];
    for (final r in [
      Tuple([s('fig'), const Int(0)]),
      Atom('parseError', [const Int(17), s('expected , at ')]),
      const Int(3),
    ]) {
      keeps(Match(lit(r), arms), 'match', 1);
    }
  });

  test('a primitive passed as a value stays the primitive', () {
    // A fold of `+` itself sums exactly, and of a lambda that adds rounds at each step; the
    // graph keeps the two apart, as a `prim` node with no inputs and as a `lambda`.
    final exact = let_('plus', const PrimFn(Prim.add), fold(lit(floats()), var_('plus')));
    final tree = fold(lit(floats()), lam(['a', 'b'], add(var_('a'), var_('b'))));
    expect(roundTrip(exact), '0.6');
    expect(roundTrip(tree), '0.6000000000000001');
    keeps(exact, 'lambda', 0);
    keeps(tree, 'lambda', 1);
    expect(lower(exact).nodes.any((n) => n.inputs.isEmpty && n.op.name == 'prim'), isTrue);
  });
}
