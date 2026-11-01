/// A wrong plan is caught natively as the machine catches it at the end of the run: a missed
/// drop leaves a cell live, a missing dup frees a cell still in use, and a borrowed argument
/// given to a parameter that consumes it is the machine's error, word for word.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/native.dart' as native;
import 'package:zed/zir.dart' as zir show run;
import 'package:zed/zir.dart' show Mode, Plan, Region, RegionPlan, ZirError;

import 'native.dart';

Term readsTwice() => let_(
  's',
  prim(Prim.concat, [lit('ab'), lit('c')]),
  prim(Prim.tuple, [
    prim(Prim.len, [var_('s')]),
    prim(Prim.upper, [var_('s')]),
  ]),
);

String go(Region g, Plan p) => '${native.run(g, p, Evaluator(World())).value}';

Matcher fails(Matcher message) =>
    throwsA(isA<ZirError>().having((e) => e.message, 'message', message));

/// Every region plan under [rp], in preorder.
Iterable<RegionPlan> regions(RegionPlan rp) sync* {
  yield rp;
  for (final n in rp.nodes) {
    for (final r in n.regions) {
      yield* regions(r);
    }
  }
}

void main() {
  test('the right plan runs', () {
    final (g, p) = planned(readsTwice());
    expect(go(g, p), '(3, "ABC")');
  });

  test('a missed drop leaves a cell live', () {
    final (g, p) = planned(readsTwice());
    p.at('r').nodes[2].drops.clear();
    expect(() => go(g, p), fails(equals('memory: 1 cell live after the result is dropped')));
  });

  test('a missing dup frees a cell still in use', () {
    final t = let_(
      's',
      prim(Prim.concat, [lit('ab'), lit('c')]),
      prim(Prim.tuple, [var_('s'), var_('s')]),
    );
    final (g, p) = planned(t);
    p.at('r').nodes.firstWhere((n) => n.dups.isNotEmpty).dups.clear();
    expect(() => go(g, p), fails(contains('freed')));
  });

  test('a borrowed argument to a consuming parameter is the machine\'s error', () {
    final t = let_(
      'f',
      lam(['x'], prim(Prim.concat, [var_('x'), lit('!')])),
      let_(
        's',
        prim(Prim.concat, [lit('a'), lit('b')]),
        prim(Prim.tuple, [
          app(var_('f'), [var_('s')]),
          prim(Prim.len, [var_('s')]),
        ]),
      ),
    );
    final (g, p) = planned(t);
    final n = regions(p.root).expand((r) => r.nodes).firstWhere((n) => n.callee != null);
    n.modes[1] = Mode.borrowed;
    n.callee!.args[0] = Mode.owned;
    String? want;
    try {
      zir.run(g, p, Evaluator(World()));
    } on ZirError catch (e) {
      want = e.message;
    }
    expect(want, contains('is passed borrowed to'));
    expect(() => go(g, p), fails(equals(want)));
  });

  test('a body returning its capture dups it, and without the dup frees it early', () {
    // The body borrows its capture `s` and returns it, so the result is a dup of it.
    final t = let_(
      's',
      prim(Prim.concat, [lit('ab'), lit('c')]),
      let_(
        'f',
        lam(['x'], var_('s')),
        prim(Prim.tuple, [
          app(var_('f'), [lit(1)]),
        ]),
      ),
    );
    final (g, p) = planned(t);
    expect(go(g, p), '("abc")');
    final body = p.at('r.1/0');
    expect(body.resultDups, [0]);
    body.resultDups.clear();
    expect(() => go(g, p), fails(contains('freed')));
  });
}
