/// The time of planning and running at the rule of low complexity (DESIGN.md Part G): each
/// graph is lowered before it is timed, and the timed pass plans it and runs it in the
/// machine, which checks the counts after every node. Each string is `"a" ++ "<i>"` for its
/// own `i`, since lowering merges equal terms into one node.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' as zir show plan, run;
import 'package:zed/zir.dart' show lower;

import '../../support/scaling.dart' as scaling;
import 'machine.dart';

/// `s{i} = "a" ++ "<i>"` for `i` from 1 to `n`, then `(len(s1), upper(s1), …)`: each string read
/// twice, the second read dropping it.
Term wide(int n) {
  Term t = prim(Prim.tuple, [
    for (var i = 1; i <= n; i++) ...[
      prim(Prim.len, [var_('s$i')]),
      prim(Prim.upper, [var_('s$i')]),
    ],
  ]);
  for (var i = n; i >= 1; i--) {
    t = let_('s$i', cat('a', '$i'), t);
  }
  return t;
}

/// `s = "a" ++ "b"`, then `if 0 < d then (if 1 < d then … (s, 1) … else 1) else 0`, `d` deep:
/// each arm captures `s` and passes it on to the next.
Term nest(int d) {
  Term t = prim(Prim.tuple, [var_('s'), lit(1)]);
  for (var i = d - 1; i >= 0; i--) {
    t = if_(prim(Prim.lt, [lit(i), lit(d)]), t, lit(i));
  }
  return let_('s', cat('a', 'b'), t);
}

/// `f = (x) -> len(x)`, then `(f("a" ++ "0"), …)`, `n` calls of one lambda.
Term calls(int n) => let_(
  'f',
  lam(['x'], prim(Prim.len, [var_('x')])),
  prim(Prim.tuple, [
    for (var i = 0; i < n; i++) app(var_('f'), [cat('a', '$i')]),
  ]),
);

/// `x0 = "a" ++ "b"; x1 = (x0, 1); …; x{n-1}`: a chain of `n` pairs, every one live to the end.
Term chain(int n) {
  Term t = var_('x${n - 1}');
  for (var i = n - 1; i >= 1; i--) {
    t = let_('x$i', prim(Prim.tuple, [var_('x${i - 1}'), lit(i)]), t);
  }
  return let_('x0', cat('a', 'b'), t);
}

/// `match ("a" ++ "1", …) { (x1, …, xn) => (len(x1), …, len(xh), x(h+1), …, xn) }`, `h` being
/// `n / 2`: a fresh tuple of `n` strings destructured, every binder kept, the first half only
/// read.
Term destructure(int n) {
  final h = n ~/ 2;
  return Match(prim(Prim.tuple, [for (var i = 1; i <= n; i++) cat('a', '$i')]), [
    (
      TupleP([for (var i = 1; i <= n; i++) BindP('x$i')]),
      prim(Prim.tuple, [
        for (var i = 1; i <= h; i++) prim(Prim.len, [var_('x$i')]),
        for (var i = h + 1; i <= n; i++) var_('x$i'),
      ]),
    ),
  ]);
}

/// Times planning and running the graph of `make` at `n` and `8n`, both lowered first.
void scales(String what, int n, Term Function(int) make) {
  final inputs = {n: lower(make(n)), scaling.factor * n: lower(make(scaling.factor * n))};
  scaling.check(what, n, (m) {
    final g = inputs[m]!;
    zir.run(g, zir.plan(g, true), Evaluator(World()));
  });
}

void main() {
  test('the plans are right on small inputs', () {
    expect(machine(wide(2)).$1, '(2, "A1", 2, "A2")');
    expect(machine(nest(3)).$1, '("ab", 1)');
    expect(machine(calls(3)).$1, '(2, 2, 2)');
    expect(machine(calls(3)).$2.increments, 0);
    expect(machine(chain(3)).$1, '(("ab", 1), 2)');
    // Fused, the binders move out of the freed tuple: the only writes are the drop of the
    // binder read, and the result's drop.
    expect(machine(destructure(3)).$1, '(2, "a2", "a3")');
    expect(machine(destructure(3)).$2.writes, 4);
  });

  // An edge's source is found by a binary search over the nodes' first outputs.
  test('planning and running many strings each read twice scales', () {
    scales('planning and running n strings read twice', 2000, wide);
  });

  // Whether an arm consumes a capture is asked once of each arm, and remembered.
  test('planning and running a deep nest of ifs scales', () {
    scales('planning and running a nest of n ifs', 200, nest);
  });

  // The planner asks its questions of the arms below on a stack, and the machine runs each
  // region it enters on a stack, so neither needs a deeper call stack.
  test('a nest of 12,800 ifs plans and runs', () {
    final (v, s, _) = machine(nest(12800));
    expect(v, '("ab", 1)');
    expect(s.increments, 0);
  });

  // The lambda's edge has a use at each call: whether a use is its last is read off the end of
  // its list of uses, and the parameters are found once.
  test('planning and running many calls of one lambda scales', () {
    scales('planning and running n calls of one lambda', 2000, calls);
  });

  // After each node only the cells it touched are checked, not every live cell.
  test('running a long chain of live pairs scales', () {
    scales('planning and running a chain of n live pairs', 2000, chain);
  });

  // The fused release groups the kept binders by child in a map, and the scrutinee's mode
  // counts the arm's binders once while it looks past those only read.
  test('destructuring a large tuple scales', () {
    scales('planning and running the match of a tuple of n strings', 2000, destructure);
  });
}
