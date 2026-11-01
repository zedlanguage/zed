/// Each kind of stop is reported, with the term it stopped at, and the preimage at a stop
/// keeps the whole domain, so it stays necessary.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/store.dart';

import 'support.dart';

/// The preimage of `true` under `src` over `ds`, printed, after checking it on the window
/// `-150..=150`.
String holds(String src, List<Dom> ds) {
  final p = pre(src, ds, const BoolDemand(true));
  check(function(src).$2, doms(ds), const BoolDemand(true), p, (-150, 150));
  return shown(p);
}

void main() {
  test('a string operation stops the transfer', () {
    expect(
      holds('ok(x) = String(x) == "12";\n', [('x', null, null)]),
      'x [..]; necessary; stop: string operation Show stops the transfer at String(x)',
    );
    // Below `len` the string stops it; a listed domain is then enumerated, and the stop is
    // still reported.
    const src = 'ok(x) = len(String(x)) <= 2;\n';
    final ds = listed([
      ('x', [-100, -10, -9, 0, 9, 10, 99, 100]),
    ]);
    final p = preimage(function(src).$2, ds, const BoolDemand(true));
    check(function(src).$2, ds, const BoolDemand(true), p, (-100, 100));
    expect(
      shown(p),
      'x [-9..=-9, 0..=0, 9..=10, 99..=99]; exact; enumerated; stop: string operation Show '
      'stops the transfer at String(x)',
    );
    expect(
      holds('ok(x) = len(trim(String(x))) <= 2;\n', [('x', null, null)]),
      'x [..]; necessary; stop: string operation Trim stops the transfer at trim(String(x))',
    );
  });

  test('a string operation on constants only is run', () {
    expect(holds('ok(x) = x < len(String(1000));\n', [('x', null, null)]), 'x [..=3]; exact');
  });

  test('a foreign call stops the transfer', () {
    // `hash` is a foreign function: a name the term does not bind.
    const call = App(Var('hash'), [Var('x')]);
    final t = PrimApp(Prim.lt, [call, Lit(Int(10))]);
    final p = preimage(t, doms([('x', null, null)]), const BoolDemand(true));
    expect(shown(p), 'x [..]; necessary; stop: foreign name `hash` stops the transfer at hash(x)');
    expect(p.stops[0].kind, const ForeignStop('hash'));
  });

  test('a term outside the scalar catalog is reported', () {
    // `sum` of a tuple belongs to the catalog's tuple entries, not its scalar ones.
    final tuple = PrimApp(Prim.tuple, [Var('x'), Lit(Int(1))]);
    final t = PrimApp(Prim.lt, [
      PrimApp(Prim.sum, [tuple]),
      Lit(Int(5)),
    ]);
    final wide = preimage(t, doms([('x', null, null)]), const BoolDemand(true));
    expect(shown(wide), 'x [..]; necessary; stop: no scalar catalog entry for sum((x, 1))');
    expect(wide.stops[0].kind, const OutsideStop());
    // On a listed domain the enumeration decides it, and the stop is still reported.
    final ds = listed([
      ('x', [-10, 2, 3, 5, 10]),
    ]);
    final p = preimage(t, ds, const BoolDemand(true));
    check(t, ds, const BoolDemand(true), p, (-10, 10));
    expect(
      shown(p),
      'x [-10..=-10, 2..=3]; exact; enumerated; stop: no scalar catalog entry for sum((x, 1))',
    );
  });

  test('a length under arithmetic is read through to its stop', () {
    expect(
      holds('ok(x) = len(String(x)) + 1 <= 3;\n', [('x', null, null)]),
      'x [..]; necessary; stop: string operation Show stops the transfer at String(x)',
    );
  });

  test('a call that never returns stops where it calls itself', () {
    // `w(w) >= x` with `w = \g. g(g)`: each call makes another, so the transfer stops at the
    // first call of `w` made while `w` is being read.
    const w = Lam(['g'], App(Var('g'), [Var('g')]));
    const t = PrimApp(Prim.ge, [
      App(w, [w]),
      Var('x'),
    ]);
    final p = preimage(t, doms([('x', null, null)]), const BoolDemand(true));
    expect(p.exact, isFalse, reason: shown(p));
    expect(p.stops.any((s) => s.kind == const RecursionStop()), isTrue, reason: shown(p));
  });
}
