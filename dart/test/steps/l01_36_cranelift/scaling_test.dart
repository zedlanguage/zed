/// The counting machine and the native code against the size of the program (the rule of low
/// complexity, DESIGN.md Part G): an atom of many named fields, many lookup ports, many
/// constants, many lambdas and one value used many times each run in time near linear in
/// their number (COMPLEXITY.md Z14). Each term is built before it is timed.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/native.dart' as native;
import 'package:zed/zir.dart' as zir show run;

import '../../support/scaling.dart' as scaling;
import '../l01_34_memory/machine.dart' show cat;
import 'native.dart';

/// A lookup port whose every key holds the same value.
final class Same implements Lookup {
  final Value v;

  Same(this.v);

  @override
  Value get(Value key) => v;
}

/// Lookup ports `p0`, `p1`, … `p{n-1}`.
World Function() world(int n) => () {
  final w = World();
  for (var i = 0; i < n; i++) {
    w.source('p$i', Same(Int(i)));
  }
  return w;
};

/// [t] run by the counting machine and natively in a world from [w]: both values, which
/// agree, printed.
String both(Term t, World Function() w) {
  final (g, p) = planned(t);
  final (v, _) = zir.run(g, p, Evaluator(w()));
  final o = native.run(g, p, Evaluator(w()));
  expect(o.value, v);
  return '$v';
}

/// `#a(f{n-1}: "x{n-1}" ++ "", …, f0: "x0" ++ "")`, the names given last first, matched by a
/// pattern that binds every field, and the binders made a tuple.
Term fields(int n) {
  String name(int i) => 'f${'$i'.padLeft(5, '0')}';
  final names = Tuple([for (var i = n - 1; i >= 0; i--) Str(name(i))]);
  final ins = [lit('a'), lit(names), for (var i = n - 1; i >= 0; i--) cat('x$i', '')];
  final p = FieldsP('a', [for (var i = 0; i < n; i++) (name(i), BindP('v$i'))]);
  final body = prim(Prim.tuple, [for (var i = 0; i < n; i++) var_('v$i')]);
  return Match(prim(Prim.atom, ins), [(p, body)]);
}

/// `(p0(0), p1(0), …)`: `n` lookup ports, each read once.
Term ports(int n) => prim(Prim.tuple, [
  for (var i = 0; i < n; i++) app(Read('p$i'), [lit(0)]),
]);

/// `("s0", "s1", …)`: a tuple of `n` constant strings.
Term consts(int n) => prim(Prim.tuple, [for (var i = 0; i < n; i++) lit('s$i')]);

/// `f0 = (x) -> x ++ "0"; …; (f0("a"), f1("a"), …)`: `n` lambdas, each called once.
Term lambdas(int n) {
  Term t = prim(Prim.tuple, [
    for (var i = 0; i < n; i++) app(var_('f$i'), [lit('a')]),
  ]);
  for (var i = n - 1; i >= 0; i--) {
    t = let_('f$i', lam(['x'], prim(Prim.concat, [var_('x'), lit('$i')])), t);
  }
  return t;
}

/// `x = "a" ++ "b"; (x, x, …)`: one cell used `n` times by one node.
Term dups(int n) =>
    let_('x', cat('a', 'b'), prim(Prim.tuple, [for (var i = 0; i < n; i++) var_('x')]));

/// Times [both] on the terms of [make] at `n` and `8n`, built first. Both sizes are run three
/// times before timing: with fewer, the first timing at `n` is up to twice the later ones, and
/// a quadratic runtime can pass on it.
void scales(String what, int n, World Function() w, Term Function(int) make) {
  final terms = {n: make(n), scaling.factor * n: make(scaling.factor * n)};
  for (var i = 0; i < 3; i++) {
    both(terms[n]!, w);
    both(terms[scaling.factor * n]!, w);
  }
  scaling.check(what, n, (m) => both(terms[m]!, w));
}

void main() {
  test('small programs agree', () {
    final w = world(3);
    expect(both(fields(3), w), '("x0", "x1", "x2")');
    expect(both(consts(3), w), '("s0", "s1", "s2")');
    expect(both(lambdas(3), w), '("a0", "a1", "a2")');
    expect(both(dups(3), w), '("ab", "ab", "ab")');
    expect(both(ports(3), w), '(0, 1, 2)');
  });

  test('an atom of many named fields scales', () {
    scales('an atom of n named fields, matched', 1000, World.new, fields);
  });

  test('a tuple of many lookup ports scales', () {
    scales('a tuple of n lookup ports', 1000, world(8000), ports);
  });

  test('many constants scale', () {
    scales('a tuple of n constants', 1000, World.new, consts);
  });

  test('many lambdas scale', () {
    scales('n lambdas, each called', 1000, World.new, lambdas);
  });

  test('one value used many times scales', () {
    scales('one cell used n times by one node', 1000, World.new, dups);
  });
}
