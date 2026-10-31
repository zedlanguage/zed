/// The printer's line breaking: a term that fits stays on one line, one that does not puts each
/// part on its own line, and the text differs from the one-line form only in whitespace.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/instances.dart';
import '../../support/kernel.dart';

/// The weekly revenue per region: a fold over a reindex over a filter.
Term revenue() {
  Term sale(String f) => get(var_('s'), lit(f));
  return foldAt(
    reindex(
      discard(var_('sales'), lam(['s'], eq(sale('week'), var_('week')))),
      lam(['k', 's'], path([sale('region'), var_('k')])),
      lam(['k', 's'], mul(sale('qty'), sale('price'))),
    ),
    2,
    const PrimFn(Prim.add),
    lit(0),
  );
}

/// A random term over every generator, `depth` levels deep.
Term random(Rng rng, int depth) {
  const names = ['orders', 'k', 'v', 'total', 'région'];
  if (depth == 0) {
    return switch (rng.below(3)) {
      0 => var_(rng.pick(names)),
      1 => lit(rng.int_(-50, 50)),
      _ => lit('a b'),
    };
  }
  final (a, b, c) = (random(rng, depth - 1), random(rng, depth - 1), random(rng, depth - 1));
  return switch (rng.below(12)) {
    0 => fam(a, 'i', b),
    1 => reindex(a, b, c),
    2 => discard(a, b),
    3 => fold(a, b, c),
    4 => fixLattice(a, b, c),
    5 => fixDefined(a, (self, k) => app(self, [sub(k, b)])),
    6 => Gen(a, b, c, GuardPos.after),
    7 => let_('x', a, if_(b, c, var_('x'))),
    8 => app(lam(['x', 'y'], a), [b, c]),
    9 => Push('stdout', a),
    10 => Match(a, [(const WildP(), b), (const BindP('y'), c)]),
    _ => add(a, mul(b, c)),
  };
}

String noSpace(String s) => s.replaceAll(RegExp(r'\s'), '');

void main() {
  test('a term that fits stays on one line', () {
    final t = revenue();
    final flat = '$t';
    expect(pretty(t, flat.length), flat);
    expect(pretty(t, 1000), flat);
  });

  test('a term that does not fit breaks into indented parts', () {
    expect(pretty(revenue(), 60), '''
fold(
  reindex(
    discard(sales, s -> (get(s, "week") == week)),
    (k, s) -> path(get(s, "region"), k),
    (k, s) -> (get(s, "qty") * get(s, "price")),
    witness: residue
  ),
  (+),
  identity: 0,
  depth: 2,
  ev: {}
)''');
  });

  test('every line fits when the parts do', () {
    final t = revenue();
    for (final width in [40, 50, 60, 80]) {
      final text = pretty(t, width);
      final longest = text.split('\n').map((l) => l.length).reduce((a, b) => a > b ? a : b);
      expect(longest, lessThanOrEqualTo(width), reason: 'width $width:\n$text');
    }
  });

  test('a block and its branches break inside their braces', () {
    final t = let_(
      'subtotal',
      mul(var_('quantity'), var_('unitPrice')),
      if_(
        le(var_('subtotal'), lit(100)),
        var_('subtotal'),
        app(var_('discounted'), [var_('subtotal'), lit(10)]),
      ),
    );
    expect(pretty(t, 40), '''
{
  subtotal = (quantity * unitPrice);
  if (subtotal <= 100) {
    subtotal
  } else {
    discounted(subtotal, 10)
  }
}''');
  });

  test('the broken text is the flat text up to whitespace', () {
    final rng = Rng(15);
    for (var i = 0; i < randomInstances; i++) {
      final t = random(rng, 1 + rng.below(4));
      final flat = '$t';
      expect(flat, isNot(contains('\n')));
      final width = 10 + rng.below(80);
      final text = pretty(t, width);
      expect(noSpace(text), noSpace(flat), reason: 'width $width:\n$text');
      // Breaking only adds lines: a line break replaces a space or follows an opener, and each
      // broken line is indented by an even number of spaces.
      for (final line in text.split('\n')) {
        expect((line.length - line.trimLeft().length) % 2, 0, reason: text);
      }
    }
  });
}
