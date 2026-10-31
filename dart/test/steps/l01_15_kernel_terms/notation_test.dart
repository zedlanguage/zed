/// Step L1.15: the kernel terms whole. One term per generator and per Tier 0 form, each written
/// as sec:kernel writes it.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/kernel.dart';

void main() {
  test('an invoice total is a fold over a family', () {
    Term line(String f) => get(var_('line'), lit(f));
    final total = fold(
      fam(var_('lines'), 'line', mul(line('qty'), line('price'))),
      const PrimFn(Prim.add),
      lit(0),
    );
    expect(
      '$total',
      'fold(fam(lines, line -> (get(line, "qty") * get(line, "price"))), (+), '
          'identity: 0, depth: 1, ev: {})',
    );
  });

  test('grouping orders by customer is a reindex with its witness', () {
    final byCustomer = Reindex(
      var_('orders'),
      lam(['k', 'v'], path([get(var_('v'), lit('customer')), var_('k')])),
      lam(['k', 'v'], var_('v')),
      const Residue(),
    );
    expect(
      '$byCustomer',
      'reindex(orders, (k, v) -> path(get(v, "customer"), k), (k, v) -> v, witness: residue)',
    );
    final catalog = Reindex(var_('orders'), var_('swap'), var_('id'), const Catalog('tuple.swap'));
    expect('$catalog', endsWith('witness: catalog("tuple.swap"))'));
  });

  test('a filter is a discard', () {
    final open = discard(
      var_('tickets'),
      lam(['t'], eq(get(var_('t'), lit('state')), atom('open'))),
    );
    expect('$open', 'discard(tickets, t -> (get(t, "state") == #open))');
  });

  test('fibonacci by definedness names this and its key', () {
    final fib = Fix(
      var_('upTo'),
      if_(
        lt(var_('n'), lit(2)),
        var_('n'),
        add(app(var_('fib'), [sub(var_('n'), lit(1))]), app(var_('fib'), [sub(var_('n'), lit(2))])),
      ),
      'fib',
      'n',
      const Definedness(),
      const {},
    );
    expect(
      '$fib',
      'fix(upTo, (fib, n) -> if (n < 2) { n } else { (fib((n - 1)) + fib((n - 2))) }, '
          'definedness, ev: {})',
    );
  });

  test('reachability is a lattice fix with its join and evidence', () {
    final reach = Fix(var_('start'), var_('next'), 'this', 'k', const Lattice(PrimFn(Prim.union)), {
      'monotone': Grade.proved,
      'ascendingChains': Grade.axiom,
    });
    // The record is written in property-name order, whatever order it was built in, and in
    // braces padded as a block's are.
    expect(
      '$reach',
      'fix(start, next, join: union, ev: { ascendingChains: axiom, monotone: proved })',
    );
  });

  test('a countdown is a gen with its guard position', () {
    final countdown = Gen(
      lit(10),
      lam(['n'], sub(var_('n'), lit(1))),
      lam(['n'], prim(Prim.gt, [var_('n'), lit(0)])),
      GuardPos.before,
    );
    expect('$countdown', 'gen(10, n -> (n - 1), n -> (n > 0), guard: before)');
  });

  test('a report reads stdin and pushes to stdout', () {
    final echo = let_('text', const Read('stdin'), Push('stdout', var_('text')));
    expect('$echo', '{ text = port.read(stdin); port.push(stdout, text) }');
  });

  test('a shipping rule is a match over atoms', () {
    final cost = Match(var_('zone'), [
      (const AtomP('local'), lit(5)),
      (const AtomP('abroad', [BindP('km')]), mul(var_('km'), lit(2))),
      (const LitP(Int(0)), lit(0)),
      (const TupleP([WildP(), BindP('x')]), var_('x')),
      (const TupleP([WildP()]), lit(1)),
    ]);
    expect(
      '$cost',
      'match zone { #local -> 5, #abroad(km) -> (km * 2), 0 -> 0, (_, x) -> x, (_,) -> 1 }',
    );
  });

  test('tuples, primitives and applied lambdas print unambiguously', () {
    expect('${prim(Prim.tuple, [lit(1), lit('a')])}', '(1, "a")');
    expect('${prim(Prim.tuple, [lit(1)])}', '(1,)');
    expect('${prim(Prim.neg, [var_('x')])}', 'neg(x)');
    expect('${count(var_('orders'))}', 'count(orders)');
    expect('${const PrimFn(Prim.max)}', 'max');
    // A lambda applied in place is parenthesized, so its body does not swallow the call.
    expect('${app(lam(['x'], add(var_('x'), lit(1))), [lit(2)])}', '(x -> (x + 1))(2)');
    // Nested operators keep every parenthesis: no precedence is needed to read them.
    expect('${sub(var_('a'), sub(var_('b'), var_('c')))}', '(a - (b - c))');
  });
}
