/// Step M0.9: the kernel reference evaluator.
///
/// Each test builds the kernel term that a small real program elaborates to and checks what
/// it computes: one or more tests per generator, the failure rules, ports, and the limits.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/kernel.dart';

const plus = PrimFn(Prim.add);

Value orders() {
  // order id -> (customer, region, amount)
  const rows = [
    (101, 'ann', 'north', 0.1),
    (102, 'bob', 'south', 2.5),
    (103, 'ann', 'north', 0.2),
    (104, 'cy', 'north', 0.3),
  ];
  return Family.of([
    for (final (id, c, r, a) in rows) (Int(id), Tuple([s(c), s(r), Float(a)])),
  ]);
}

Value stock() {
  const leaves = [
    ('fruit', 'apple', 3),
    ('fruit', 'fig', 0),
    ('veg', 'kale', 0),
    ('dairy', 'milk', 12),
  ];
  return Family.fromLeaves([
    for (final (c, i, n) in leaves) ([s(c), s(i)], Int(n)),
  ]);
}

Value edges() {
  // A flight network as a set of (from, to) pairs.
  const pairs = [('lhr', 'jfk'), ('jfk', 'sfo'), ('sfo', 'nrt'), ('cdg', 'lhr'), ('syd', 'akl')];
  return Family.set([
    for (final (a, b) in pairs) Tuple([s(a), s(b)]),
  ]);
}

Term definedness(Term domain, Term body) =>
    Fix(domain, body, 'this', 'i', const Definedness(), const {});

Term sheet(List<(String, Term)> cells) => definedness(
  lit(Family.set([for (final (c, _) in cells) s(c)])),
  Match(var_('i'), [for (final (c, t) in cells) (LitP(s(c)), t)]),
);

Term cell(String name) => get(var_('this'), lit(s(name)));

Value ledger() => Family.of([
  for (final (t, x) in const [(0, 500), (1, -200), (2, -450), (3, 100)]) (Int(t), Int(x)),
]);

/// A running balance: frame `(t, balance)`, one transaction per generation.
Term balanceLoop(Term guard, GuardPos pos) {
  final step = lam(
    ['f'],
    prim(Prim.tuple, [
      add(nth(var_('f'), 0), lit(1)),
      add(nth(var_('f'), 1), get(lit(ledger()), nth(var_('f'), 0))),
    ]),
  );
  return Gen(prim(Prim.tuple, [lit(0), lit(0)]), step, guard, pos);
}

Term push(String port, Term v) => Push(port, v);

void main() {
  test('word count groups then folds', () {
    final doc = linesOf([
      ['the', 'cat', 'sat'],
      ['on', 'the', 'mat'],
      ['the', 'end'],
    ]);
    // reindex each word to `word -> line -> position`, count 1 per occurrence, sum per word.
    final kf = lam(['p', 'w'], path([var_('w'), key(var_('p'), 0), key(var_('p'), 1)]));
    final ones = reindex(lit(doc), kf, lam(['p', 'w'], lit(1)));
    final perLine = foldAt(ones, 3, plus);
    final counts = foldAt(perLine, 2, plus);
    expect(
      eval(counts).toString(),
      '{"cat" -> 1, "end" -> 1, "mat" -> 1, "on" -> 1, "sat" -> 1, "the" -> 3}',
    );
  });

  test('revenue by region is the exact sum', () {
    final amounts = reindex(
      lit(orders()),
      lam(['p', 'o'], path([nth(var_('o'), 1), key(var_('p'), 0)])),
      lam(['p', 'o'], nth(var_('o'), 2)),
    );
    final revenue = foldAt(amounts, 2, plus, lit(0.0));
    // 0.1 + 0.2 + 0.3 is exactly 0.6 rounded once; left to right it would be 0.6000000000000001.
    expect(eval(revenue).toString(), '{"north" -> 0.6, "south" -> 2.5}');
  });

  test('a float fold of another operator uses the canonical tree', () {
    final xs = Family.of([
      for (final (k, x) in const [(0, 0.1), (1, 0.2), (2, 0.3)]) (Int(k), Float(x)),
    ]);
    // A function whose body is `a + b` is not the primitive `+`, so it folds on the tree
    // ((x0 + x1) + x2), rounding at each node.
    final sum = lam(['a', 'b'], add(var_('a'), var_('b')));
    expect(eval(fold(lit(xs), sum)), Float(0.1 + 0.2 + 0.3));
    expect(eval(fold(lit(xs), plus)), Float(0.6));
  });

  test('rekeying orders by customer collides on a repeat customer', () {
    final byCustomer = reindex(
      lit(orders()),
      lam(['p', 'o'], nth(var_('o'), 0)),
      lam(['p', 'o'], var_('o')),
    );
    expect(evalError(byCustomer), CollisionError([s('ann')]));
    // Grouping keeps the order id beneath the customer, so the keypaths stay distinct.
    final grouped = eval(groupBy(lit(orders()), (o) => nth(o, 0)));
    final ann = grouped.asFamily![s('ann')]!.asFamily!;
    expect(ann.keys.toList(), [const Int(101), const Int(103)]);
  });

  test('map is a reindex that keeps keys', () {
    // map(f) = reindex((k, v) -> k, f): a 10% price rise in cents.
    final prices = Family.of([(s('tea'), const Int(250)), (s('cake'), const Int(400))]);
    final kf = lam(['p', 'v'], var_('p'));
    final vf = lam(
      ['p', 'v'],
      prim(Prim.intDiv, [
        prim(Prim.mul, [var_('v'), lit(11)]),
        lit(10),
      ]),
    );
    expect(eval(reindex(lit(prices), kf, vf)).toString(), '{"cake" -> 440, "tea" -> 275}');
  });

  test('discard drops out-of-stock items and their emptied category', () {
    // Keep every category entry; keep an item when its count is above zero.
    final sel = lam(
      ['p', 'v'],
      if_(
        prim(Prim.eq, [
          prim(Prim.pathLen, [var_('p')]),
          lit(1),
        ]),
        lit(true),
        prim(Prim.gt, [var_('v'), lit(0)]),
      ),
    );
    // `veg` held only kale, so its level emptied and its key is gone.
    expect(
      eval(discard(lit(stock()), sel)).toString(),
      '{"dairy" -> {"milk" -> 12}, "fruit" -> {"apple" -> 3}}',
    );
  });

  test('a boundary verdict keeps the key as a set leaf', () {
    // The set of categories: stop at depth 1, keeping each key as itself.
    final sel = lam(['p', 'v'], lit(const Atom('boundary')));
    expect(eval(discard(lit(stock()), sel)), Family.set([s('dairy'), s('fruit'), s('veg')]));
    final bad = lam(['p', 'v'], lit(3));
    expect(
      evalError(discard(lit(stock()), bad)),
      const KernelTypeError('a discard selector returned 3'),
    );
  });

  test('fold collapses the innermost level', () {
    // store -> day -> takings: the fold gives each store's total, a second fold the chain's.
    const leaves = [
      ('east', 1, 120),
      ('east', 2, 80),
      ('west', 1, 95),
      ('west', 2, 0),
      ('west', 3, 40),
    ];
    final takings = Family.fromLeaves([
      for (final (st, d, n) in leaves) ([s(st), Int(d)], Int(n)),
    ]);
    final perStore = foldAt(lit(takings), 2, plus);
    expect(eval(perStore).toString(), '{"east" -> 200, "west" -> 135}');
    expect(eval(fold(perStore, plus)), const Int(335));
    final bestDay = fold(
      lit(eval(foldAt(lit(stock()), 2, const PrimFn(Prim.max)))),
      const PrimFn(Prim.max),
    );
    expect(eval(bestDay), const Int(12));
  });

  test('folding leaves at mixed depths is an error', () {
    final ragged = Family.fromLeaves([
      ([s('a')], const Int(1)),
      ([s('b'), s('c')], const Int(2)),
    ]);
    expect(evalError(foldAt(lit(ragged), 2, plus)), const MixedDepthError());
  });

  test('an empty level folds to the identity or #empty', () {
    final none = lit(const Family.empty());
    expect(eval(fold(none, plus, lit(0))), const Int(0));
    expect(eval(fold(none, const PrimFn(Prim.max))), const Atom('empty'));
  });

  test('an empty family folds by the depth its type gives', () {
    // Sales by store and day with no sales yet: the per-store totals are an empty table, not
    // `#empty`, which is what folding one empty level gives.
    final none = lit(const Family.empty());
    expect(eval(foldAt(none, 2, plus)), const Family.empty());
    // A one-level table folded as two levels has a leaf at the wrong depth.
    final flat = lit(Family.of([(s('east'), const Int(3))]));
    expect(evalError(foldAt(flat, 2, plus)), const MixedDepthError());
  });

  test('fam builds a table over a domain', () {
    // VAT at 20% for each price band, and a band with no entries drops its key.
    final bands = lit(Family.set([const Int(100), const Int(250), const Int(1000)]));
    final vat = fam(bands, 'b', prim(Prim.intDiv, [var_('b'), lit(5)]));
    expect(eval(vat).toString(), '{100 -> 20, 250 -> 50, 1000 -> 200}');
    expect(eval(fam(bands, 'b', lit(const Family.empty()))), const Family.empty());
  });

  test('reachability is a lattice fixpoint', () {
    // step(r) = the set of `to` over edges whose `from` is in r; the join is set union.
    final fromReached = discard(
      lit(edges()),
      lam(['p', 'e'], found(get(var_('r'), nth(var_('e'), 0)))),
    );
    final targets = groupBy(fromReached, (e) => nth(e, 1));
    final step = lam(['r'], fam(targets, 'k', var_('k')));
    final reach = Fix(
      lit(Family.set([s('cdg')])),
      step,
      'this',
      'k',
      const Lattice(PrimFn(Prim.union)),
      const {},
    );
    expect(
      eval(reach),
      Family.set([
        for (final x in ['cdg', 'jfk', 'lhr', 'nrt', 'sfo']) s(x),
      ]),
    );
  });

  test('fibonacci by general recursion', () {
    final domain = lit(Family.set([for (var i = 0; i <= 40; i++) Int(i)]));
    Term at(int d) => get(var_('this'), prim(Prim.sub, [var_('i'), lit(d)]));
    final body = if_(prim(Prim.lt, [var_('i'), lit(2)]), var_('i'), add(at(1), at(2)));
    final fib = eval(definedness(domain, body)).asFamily!;
    expect(fib[const Int(10)], const Int(55));
    expect(fib[const Int(40)], const Int(102334155));
  });

  test('a spreadsheet evaluates in dependency order', () {
    final book = sheet([
      ('total', add(cell('net'), cell('tax'))),
      ('tax', prim(Prim.intDiv, [cell('net'), lit(5)])),
      ('net', prim(Prim.mul, [cell('units'), cell('price')])),
      ('units', lit(12)),
      ('price', lit(250)),
      ('rate', get(var_('this'), lit(s('missing')))),
    ]);
    // A read outside the domain is `#notFound`, an ordinary value.
    expect(
      eval(book).toString(),
      '{"net" -> 3000, "price" -> 250, "rate" -> #notFound, "tax" -> 600, "total" -> 3600, '
      '"units" -> 12}',
    );
  });

  test('a circular reference stalls and names its cells', () {
    final book = sheet([
      ('a', add(cell('b'), lit(1))),
      ('b', add(cell('c'), lit(1))),
      ('c', add(cell('a'), lit(1))),
      ('d', lit(7)),
    ]);
    expect(evalError(book), StalledError([s('a'), s('b'), s('c')]));
  });

  test('a running balance is a generation loop', () {
    final more = lam(
      ['f'],
      prim(Prim.lt, [
        nth(var_('f'), 0),
        prim(Prim.count, [lit(ledger())]),
      ]),
    );
    expect(
      eval(balanceLoop(more, GuardPos.before)).toString(),
      '{0 -> (0, 0), 1 -> (1, 500), 2 -> (2, 300), 3 -> (3, -150), 4 -> (4, -50)}',
    );
  });

  test('a guard atom ends the loop with that value', () {
    // Stop at an overdraft: the end-position guard reads the frame it just committed.
    final guard = lam([
      'f',
    ], if_(prim(Prim.lt, [nth(var_('f'), 1), lit(0)]), lit(const Atom('overdrawn')), lit(true)));
    expect(
      eval(balanceLoop(guard, GuardPos.after)).toString(),
      '{0 -> (0, 0), 1 -> (1, 500), 2 -> (2, 300), 3 -> (3, -150), 4 -> #overdrawn}',
    );
    // Tested before each step, a guard that ends the loop commits nothing more.
    final atStart = eval(balanceLoop(lam(['f'], lit(false)), GuardPos.before));
    expect(atStart.toString(), '{0 -> (0, 0)}');
  });

  test('a loop that never stops runs out of fuel', () {
    final forever = balanceLoop(lam(['f'], lit(true)), GuardPos.before);
    // The ledger runs out at t = 4, after which a lookup is `#notFound` and propagates, so the
    // loop goes on with an atom balance until the fuel is spent.
    expect(evalError(forever, Evaluator(World(), fuel: 1000)), const OutOfFuelError());
  });

  test('self-application is cut off', () {
    final w = lam(['x'], app(var_('x'), [var_('x')]));
    expect(evalError(app(w, [w])), const TooDeepError());
  });

  test('failure atoms propagate through primitives', () {
    // A missing price makes the line total `#notFound`, never a crash.
    final prices = lit(Family.of([(s('tea'), const Int(250))]));
    Term line(String item) => prim(Prim.mul, [get(prices, lit(s(item))), lit(3)]);
    expect(eval(line('tea')), const Int(750));
    expect(eval(line('scone')), const Atom('notFound'));
    // Two failures merge into the set of them, whichever side each is on (step L1.18).
    final both = add(lit(const Atom('a')), lit(const Atom('b')));
    expect(eval(both).toString(), '#errs({#a, #b})');
    final swapped = add(lit(const Atom('b')), lit(const Atom('a')));
    expect(eval(swapped), eval(both));
    // `match` sees the atom and can supply a default.
    final priced = Match(line('scone'), [
      (const AtomP('notFound'), lit(0)),
      (const BindP('x'), var_('x')),
    ]);
    expect(eval(priced), const Int(0));
  });

  test('integer division is euclidean', () {
    Value div(int a, int b) => eval(prim(Prim.intDiv, [lit(a), lit(b)]));
    Value rem(int a, int b) => eval(prim(Prim.mod, [lit(a), lit(b)]));
    expect((div(7, 2), rem(7, 2)), (const Int(3), const Int(1)));
    expect((div(-7, 2), rem(-7, 2)), (const Int(-4), const Int(1)));
    expect((div(7, -2), rem(7, -2)), (const Int(-3), const Int(1)));
    expect(div(1, 0), const Atom('divByZero'));
    expect(rem(1, 0), const Atom('divByZero'));
    // `int` is unbounded (step L1.17): past 64 bits an integer widens.
    expect(eval(add(lit(0x7fffffffffffffff), lit(1))).toString(), '9223372036854775808');
  });

  test('floats compare as IEEE', () {
    // The language's `==` follows IEEE 754 (step L1.17); the values stay distinct keys.
    expect(eval(prim(Prim.eq, [lit(0.0), lit(-0.0)])), const Bool(true));
    expect(Float(0.0), isNot(Float(-0.0)));
    final nan = prim(Prim.div, [lit(0.0), lit(0.0)]);
    expect(eval(prim(Prim.eq, [nan, nan])), const Bool(false));
    expect(evalError(prim(Prim.lt, [lit(1), lit(2.0)])), isA<KernelTypeError>());
  });

  test('pushes to an output port return acknowledgments', () {
    const greeting = Read('stdin');
    final prog = let_(
      'a',
      push('stdout', prim(Prim.concat, [lit('hello, '), greeting])),
      let_('b', push('stdout', lit('bye')), prim(Prim.tuple, [var_('a'), var_('b')])),
    );
    final ev = Evaluator(World().input('stdin', s('ada')).output('stdout', 1));
    // The second push finds the port full.
    expect(ev.run(prog).toString(), '(#ok, #full)');
    expect(ev.world.log('stdout'), [s('hello, ada')]);
  });

  test('a port inside a pure region is rejected', () {
    final leak = fold(lit(ledger()), lam(['a', 'b'], push('stdout', var_('a'))));
    final ev = Evaluator(World().output('stdout'));
    expect(evalError(leak, ev), const KernelTypeError('port `stdout` used inside a pure region'));
    expect(ev.world.log('stdout'), isEmpty);
    expect(evalError(const Read('nope')), const UnknownPortError('nope'));
    expect(evalError(push('nope', lit(1))), const UnknownPortError('nope'));
  });

  test('ill-typed terms are reported', () {
    for (final (t, msg) in [
      (var_('x'), 'unbound variable `x`'),
      (app(lit(3), []), '3 is not a function'),
      (app(lam(['x'], var_('x')), []), 'a function of 1 parameters called with 0 arguments'),
      (if_(lit(1), lit(2), lit(3)), '`if` on 1'),
      (lam(['x'], var_('x')), "the program's result is a function"),
      (Match(lit(5), [(const LitP(Int(4)), lit(0))]), 'no arm matches 5'),
      (prim(Prim.neg, [lit(1), lit(2)]), 'Neg takes 1 arguments, given 2'),
      (prim(Prim.not, [lit(1)]), 'Not applied to 1'),
    ]) {
      expect(evalError(t), KernelTypeError(msg));
    }
  });

  test('a signup rule uses every comparison', () {
    // Accept an applicant aged 18 to 65 with a name, or any applicant on the invite list.
    Value rule(String name, int age, bool invited) {
      final inRange = prim(Prim.and, [
        prim(Prim.ge, [lit(age), lit(18)]),
        prim(Prim.le, [lit(age), lit(65)]),
      ]);
      final named = prim(Prim.ne, [lit(name), lit('')]);
      final ok = prim(Prim.or, [
        prim(Prim.and, [inRange, named]),
        lit(invited),
      ]);
      return eval(ok);
    }

    expect(rule('ada', 36, false), const Bool(true));
    expect(rule('', 36, false), const Bool(false));
    expect(rule('tim', 70, false), const Bool(false));
    expect(rule('tim', 70, true), const Bool(true));
    expect(rule('kid', 17, false), const Bool(false));
  });

  test('temperature conversion and negation', () {
    // Fahrenheit to Celsius, (f - 32) * 5 / 9, and a freezer's offset below zero.
    Term c(double f) => prim(Prim.div, [
      prim(Prim.mul, [
        prim(Prim.sub, [lit(f), lit(32.0)]),
        lit(5.0),
      ]),
      lit(9.0),
    ]);
    expect(eval(c(212.0)), Float(100.0));
    expect(eval(prim(Prim.neg, [c(-4.0)])), Float(20.0));
    expect(eval(prim(Prim.neg, [lit(18)])), const Int(-18));
    expect(eval(prim(Prim.neg, [lit(-0x8000000000000000)])).toString(), '9223372036854775808');
  });

  test('a missing price flows through if and sum', () {
    final prices = lit(Family.of([(s('tea'), const Int(250)), (s('cake'), const Int(400))]));
    // `if price > 300 { "dear" } else { "cheap" }` on a missing item is the atom itself.
    Term label(String item) =>
        if_(prim(Prim.gt, [get(prices, lit(s(item))), lit(300)]), lit('dear'), lit('cheap'));
    expect(eval(label('cake')), s('dear'));
    expect(eval(label('scone')), const Atom('notFound'));
    // A basket total with one unknown item is `#notFound`, not a partial sum.
    final basket = Family.set([s('tea'), s('scone'), s('cake')]);
    final total = fold(fam(lit(basket), 'i', get(prices, var_('i'))), plus, lit(0));
    expect(eval(total), const Atom('notFound'));
  });

  test('org chart depth by recursion', () {
    // depth(e) = depth(manager(e)) + 1; the head has no manager, so the read is `#notFound`.
    final managers = lit(
      Family.of([
        for (final (e, m) in const [('bo', 'ann'), ('cy', 'bo'), ('di', 'bo')]) (s(e), s(m)),
      ]),
    );
    final domain = lit(
      Family.set([
        for (final x in ['ann', 'bo', 'cy', 'di']) s(x),
      ]),
    );
    final up = add(get(var_('this'), get(managers, var_('i'))), lit(1));
    final body = Match(up, [(const AtomP('notFound'), lit(0)), (const BindP('d'), var_('d'))]);
    expect(
      eval(definedness(domain, body)).toString(),
      '{"ann" -> 0, "bo" -> 1, "cy" -> 2, "di" -> 2}',
    );
  });

  test('match destructures tuples and atom payloads', () {
    // A parser's result: a record `(name, qty)` or `#parseError(pos, msg)`.
    Value report(Value r) => eval(
      Match(lit(r), [
        (
          const TupleP([BindP('n'), LitP(Int(0))]),
          prim(Prim.concat, [var_('n'), lit(': out of stock')]),
        ),
        (const TupleP([BindP('n'), WildP()]), prim(Prim.concat, [var_('n'), lit(': ok')])),
        (const AtomP('parseError', [BindP('pos'), WildP()]), var_('pos')),
      ]),
    );
    expect(report(Tuple([s('fig'), const Int(0)])), s('fig: out of stock'));
    expect(report(Tuple([s('fig'), const Int(4)])), s('fig: ok'));
    expect(report(Atom('parseError', [const Int(17), s('expected ,')])), const Int(17));
  });

  test('a step or guard of the wrong kind is reported', () {
    final id = lam(['x'], var_('x'));
    final cases = [
      (
        Fix(
          lit(const Family.empty()),
          lam(['r'], id),
          'this',
          'k',
          const Lattice(PrimFn(Prim.union)),
          const {},
        ),
        'a fix step returned a function',
      ),
      (definedness(lit(Family.set([const Int(0)])), id), 'a fix entry is a function'),
      (
        definedness(lit(Family.set([const Int(0)])), app(var_('this'), [lit(0)])),
        'a family is read with `[]`, not called',
      ),
      (
        Gen(lit(0), lam(['f'], id), lam(['f'], lit(true)), GuardPos.before),
        'a gen step returned a function',
      ),
      (Gen(lit(0), id, lam(['f'], lit(3)), GuardPos.before), 'a gen guard returned 3'),
      (fold(lit(3), plus), 'expected a family, found 3'),
      (if_(id, lit(1), lit(2)), 'expected data, found a function'),
      (add(id, lit(1)), 'Add applied to a function'),
    ];
    for (final (t, msg) in cases) {
      expect(evalError(t), KernelTypeError(msg));
    }
  });
}
