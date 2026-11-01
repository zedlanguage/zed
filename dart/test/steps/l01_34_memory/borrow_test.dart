/// Borrow inference: a lambda's parameter is owned when some use consumes it and borrowed
/// otherwise, and a call passes each argument as the callee takes it when the plan sees the
/// callee, in its region or through captures, and owned otherwise.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' show Mode;

import 'machine.dart';

void main() {
  test('a parameter only read is borrowed', () {
    // `f = x -> len(x)`: `f(s)` lends `s`, which the pair then takes without a dup.
    final f = lam(['x'], prim(Prim.len, [var_('x')]));
    final t = let_(
      'f',
      f,
      let_(
        's',
        cat('a', 'b'),
        prim(Prim.tuple, [
          app(var_('f'), [var_('s')]),
          app(var_('f'), [cat('c', 'd')]),
          var_('s'),
        ]),
      ),
    );
    final (v, s, p) = machine(t);
    expect(v, '(2, 2, "ab")');
    expect(p.at('r.0/0').args, [Mode.borrowed]);
    final call = p.at('r').nodes[2];
    expect(call.callee?.path, 'r.0/0');
    expect(call.modes, [Mode.borrowed, Mode.borrowed]);
    expect(s.increments, 0);
  });

  test('a parameter consumed is owned', () {
    // `g = x -> (x, 1)`: the pair consumes `x`, so `g(s)` gives `s` away; `s` is read again
    // after, so it gets a dup first, and its last reader drops it.
    final g = lam(['x'], prim(Prim.tuple, [var_('x'), lit(1)]));
    final t = let_(
      'g',
      g,
      let_(
        's',
        cat('a', 'b'),
        prim(Prim.tuple, [
          app(var_('g'), [var_('s')]),
          prim(Prim.len, [var_('s')]),
        ]),
      ),
    );
    final (v, s, p) = machine(t);
    expect(v, '(("ab", 1), 2)');
    expect(p.at('r.0/0').args, [Mode.owned]);
    final call = p.at('r').nodes[2];
    expect(call.modes[1], Mode.owned);
    expect(call.dups, [1]);
    expect(s.increments, 1);
  });

  test('a call through a capture sees the callee', () {
    // The arm reaches `f` as a capture, and the plan follows it back to the lambda.
    final f = lam(['x'], prim(Prim.len, [var_('x')]));
    final c = prim(Prim.lt, [
      prim(Prim.len, [var_('s')]),
      lit(5),
    ]);
    final t = let_('f', f, let_('s', cat('a', 'b'), if_(c, app(var_('f'), [var_('s')]), lit(0))));
    final (v, s, p) = machine(t);
    expect(v, '2');
    final arm = p.at('r.4/0');
    expect(arm.nodes[0].callee?.path, 'r.0/0');
    expect(arm.nodes[0].modes, [Mode.borrowed, Mode.borrowed]);
    expect(s.increments, 0);
  });

  test('an unknown callee takes its arguments owned', () {
    // `ap = (h, y) -> h(y)` cannot see `h`, so it passes `y` owned and therefore owns `y`;
    // the lambda it is given only reads its parameter, and the call drops it after.
    final ap = lam(['h', 'y'], app(var_('h'), [var_('y')]));
    final len = lam(['x'], prim(Prim.len, [var_('x')]));
    final t = let_('ap', ap, app(var_('ap'), [len, cat('abc', 'd')]));
    final (v, _, p) = machine(t);
    expect(v, '4');
    final body = p.at('r.0/0');
    expect(body.args, [Mode.borrowed, Mode.owned]);
    expect(body.nodes[0].callee, isNull);
    expect(body.nodes[0].modes, [Mode.borrowed, Mode.owned]);
  });

  test('a closure holds its captures', () {
    // `f = x -> x + len(s)` takes `s` into its cell at its last use, so `s` is never
    // counted; the closure's cell frees `s` when it goes.
    final f = lam(
      ['x'],
      prim(Prim.add, [
        var_('x'),
        prim(Prim.len, [var_('s')]),
      ]),
    );
    final t = let_(
      's',
      cat('ab', 'c'),
      let_(
        'f',
        f,
        prim(Prim.tuple, [
          app(var_('f'), [lit(1)]),
          app(var_('f'), [lit(2)]),
        ]),
      ),
    );
    final (v, s, p) = machine(t);
    expect(v, '(4, 5)');
    expect(p.at('r').nodes[1].modes, [Mode.owned]);
    expect(p.at('r.1/0').args, [Mode.borrowed, Mode.borrowed]);
    expect((s.increments, s.allocations, s.frees, s.peak), (0, 3, 3, 2));
  });
}
