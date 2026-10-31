/// Unit addresses: an invoicing unit exports `total` and `tax`, with a local helper `rate` that
/// `tax` uses and a local `note` that nothing uses. Its address follows its exports' values and
/// nothing else.
library;

import 'package:test/test.dart';
import 'package:zed/address.dart';
import 'package:zed/canon.dart';
import 'package:zed/kernel.dart';

/// The unit's declarations, `rate` as given and `line` naming each line in `total`.
List<Def> invoicing(int rate, String line) {
  Term field(String f) => prim(Prim.get, [var_(line), lit(f)]);
  final total = Fold(
    Fam(var_('lines'), line, prim(Prim.mul, [field('qty'), field('price')])),
    const PrimFn(Prim.add),
    lit(0),
    1,
    const {},
  );
  final tax = lam(
    ['amount'],
    prim(Prim.intDiv, [
      prim(Prim.mul, [var_('amount'), var_('rate')]),
      lit(100),
    ]),
  );
  return [
    Def('rate', lit(rate)),
    Def('note', lit('prices in cents')),
    Def('total', total),
    Def('tax', tax),
  ];
}

/// The address of the unit whose declarations are `defs`, in dependency order, exporting
/// `exports`.
ContentAddress unit(List<Def> defs, List<String> exports) {
  final known = <String, ContentAddress>{};
  for (final d in defs) {
    known[d.name] = address(d, (x) => known[x]);
  }
  return unitAddress([for (final e in exports) (e, known[e]!)]);
}

const exports = ['total', 'tax'];

void main() {
  test('the address is pinned', () {
    // Any change to this value is a change to every unit's address, so it goes with a new
    // canonicalization version.
    expect(
      '${unit(invoicing(8, 'line'), exports)}',
      'f59b01a226a8aa9dffe695c452c6daf4274c7160aa447522ace60cefd8b32f8a',
    );
  });

  test('local names and export order do not change it', () {
    final a = unit(invoicing(8, 'line'), exports);
    expect(unit(invoicing(8, 'row'), exports), a);
    expect(unit(invoicing(8, 'line'), ['tax', 'total']), a);
  });

  test('a changed local helper changes it through the export that uses it', () {
    final a = unit(invoicing(8, 'line'), exports);
    expect(unit(invoicing(9, 'line'), exports), isNot(a));
    // The unused `note` reaches no export.
    final noted = invoicing(8, 'line')..[1] = Def('note', lit('prices in euros'));
    expect(unit(noted, exports), a);
    // Exporting it does change the address.
    expect(unit(invoicing(8, 'line'), ['total', 'tax', 'note']), isNot(a));
  });

  test('the arrows of an overloaded name are all hashed', () {
    ContentAddress show(String s) => address(Def('show', lam(['x'], lit(s))), (_) => null);
    final (a, b) = (show('int'), show('bool'));
    final both = unitAddress([('show', a), ('show', b)]);
    expect(unitAddress([('show', b), ('show', a)]), both);
    expect(unitAddress([('show', a)]), isNot(both));
  });
}
