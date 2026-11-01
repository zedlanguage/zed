/// The size of the graph and the time of the lowering at the rule of low complexity (DESIGN.md
/// Part G): a function that uses a port is one `lambda` node, called by `apply` nodes that
/// thread the state, so a chain of such functions, each calling the one before twice, lowers to
/// a graph linear in the chain's length and not exponential in it; and each pass takes time in
/// proportion to the term, however deep it nests. Each term is built before it is timed.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' hide print;

import '../../support/scaling.dart' as scaling;
import 'lowering.dart';

/// `f0 m = push m`, and `f{i} m = (f{i-1} m; f{i-1} m)`, with `f{k}` called once.
Term chain(int k) {
  Term t = app(var_('f$k'), [lit('x')]);
  for (var i = k; i >= 1; i--) {
    final g = var_('f${i - 1}');
    final body = let_('a', app(g, [var_('m')]), app(g, [var_('m')]));
    t = let_('f$i', lam(['m'], body), t);
  }
  return let_('f0', lam(['m'], push('stdout', var_('m'))), t);
}

/// `if i < d then (let y{i} = (if ...) + 1 in y{i}) else i`, `d` deep: each level a match node
/// whose arm holds the next, its edge carrying the hint of a `let`.
Term nest(int d) {
  Term t = lit(0);
  for (var i = 0; i < d; i++) {
    final y = 'y$i';
    final inner = let_(y, prim(Prim.add, [t, lit(1)]), var_(y));
    t = If(prim(Prim.lt, [lit(i), lit(d)]), inner, lit(i));
  }
  return t;
}

/// `let x0 = 1 in let x1 = x0 + 1 in … in x{n-1}`: each binding reads the name bound farthest
/// out.
Term far(int n) {
  Term t = var_('x${n - 1}');
  for (var i = n - 1; i >= 1; i--) {
    t = let_('x$i', prim(Prim.add, [var_('x0'), lit(i)]), t);
  }
  return let_('x0', lit(1), t);
}

/// `g{d} = (x{d}) -> (… (g1 = (x1) -> 1; g1(1)) …); g{d}(d)`: `let`-bound lambdas nested `d`
/// deep.
Term letsOfLambdas(int d) {
  Term t = lit(1);
  for (var i = 1; i <= d; i++) {
    t = let_('g$i', lam(['x$i'], t), app(var_('g$i'), [lit(i)]));
  }
  return t;
}

/// `c{i} = (m) -> stdout <- m; r{i} = c{i}(i); …` for `i` from 1 to `n`, then `0`: functions
/// that push, each called once, so each call lowers in place under the scope it was defined in.
Term callsInPlace(int n) {
  Term t = lit(0);
  for (var i = n; i >= 1; i--) {
    t = let_(
      'c$i',
      lam(['m'], push('stdout', var_('m'))),
      let_('r$i', app(var_('c$i'), [lit(i)]), t),
    );
  }
  return t;
}

/// `r{i} = p{i} <- i; …` for `i` from 1 to `n`, then `0`: pushes to `n` different ports.
Term pushesToManyPorts(int n) {
  Term t = lit(0);
  for (var i = n; i >= 1; i--) {
    t = let_('r$i', push('p$i', lit(i)), t);
  }
  return t;
}

/// Times `pass` on the input `make` gives at `n` and `8n`, both built first.
void scales<T>(String what, int n, T Function(int) make, void Function(T) pass) {
  final inputs = {n: make(n), scaling.factor * n: make(scaling.factor * n)};
  scaling.check(what, n, (m) => pass(inputs[m] as T));
}

/// The value of `t` and what it pushed to `stdout`.
(Value, List<Value>) run(Term t) {
  final ev = Evaluator(World().output('stdout'));
  return (ev.run(t), ev.world.log('stdout'));
}

void main() {
  test('a chain of functions that push lowers to a graph linear in its length', () {
    final (small, large) = (nodes(lower(chain(4))), nodes(lower(chain(16))));
    expect(
      large,
      lessThanOrEqualTo(5 * small),
      reason:
          'a chain of 4 functions that push lowers to $small nodes and one of 16 to $large, '
          "and the graph is to grow linearly in the chain's length",
    );
  });

  test('the chain raises to a term that pushes as often as the original', () {
    for (final k in [0, 1, 3]) {
      final t = chain(k);
      final back = raise(lower(t));
      expect(run(back).$2.length, 1 << k);
      expect(run(back).$2.length, run(t).$2.length);
    }
  });

  test('lowering the chain scales', () {
    scales('lowering a chain of functions that push', 100, chain, lower);
  });

  // CSE keys each node by the hashes of its regions, so a nest is not canonicalized again at
  // every level above it.
  test('lowering a deep nest scales', () {
    scales('lowering a nest of `if`s', 100, nest, lower);
  });

  // A name is found by a map, not by searching the scope.
  test('reading a name bound far out scales', () {
    scales('lowering lets that read the outermost name', 2000, far, lower);
  });

  // The ports of each `let`-bound lambda are found by reading each body once, not the whole
  // body again with the lambdas nested in it.
  test('lowering lambdas bound by nested lets scales', () {
    scales('lowering let-bound lambdas nested n deep', 500, letsOfLambdas, lower);
    final t = letsOfLambdas(3);
    expect(run(raise(lower(t))).$1, run(t).$1);
  });

  // Each function called in place keeps the scope it was defined in, shared, not copied.
  test('lowering many functions called in place scales', () {
    scales('lowering n functions each called once in place', 2000, callsInPlace, lower);
    final t = callsInPlace(3);
    final (v, pushed) = run(t);
    expect(pushed.length, 3);
    final (v2, pushed2) = run(raise(lower(t)));
    expect(v2, v);
    expect(pushed2, pushed);
  });

  // Each state edge's uses are counted in a map, not by searching the edges counted before.
  test('checking a graph of many pushes scales', () {
    scales('checking a graph of n pushes', 4000, (n) => lower(callsInPlace(n)), validate);
  });

  // The current state of each port is found by a map, not by searching the ports used before.
  // A search is cheap beside the rest of the work on a push, so it shows only from 8000 ports.
  test('lowering pushes to many ports scales', () {
    scales('lowering pushes to n ports', 8000, pushesToManyPorts, lower);
  });

  // The raised term is built by a fold over each region's nodes, not by recursion.
  test('raising a long graph scales', () {
    scales(
      'raising the graph of lets that read the outermost name',
      2000,
      (n) => lower(far(n)),
      raise,
    );
  });
}
