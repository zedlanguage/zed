/// The atoms of a named family, `type Color = #red | #green | #blue`, are data. The marking is
/// the type's: `Ty.named` gives it, as a `type` declaration will (step L2.1), and these tests
/// read the rules from the type representation and the operator rule directly.
library;

import 'package:test/test.dart';
import 'package:zed/check.dart';
import 'package:zed/kernel.dart' as k;

/// `#a | #b | …`.
Ty atoms(List<String> names) => Ty.unionAll(names.map((n) => Ty.of(k.Type.atom(n))));

/// `Color`, the named family `#red | #green | #blue`.
Ty color() => atoms(['red', 'green', 'blue']).named;

/// `Color | #ioError`: a family and a loose failure.
Ty readColor() => color().union(atoms(['ioError']));

void main() {
  test('else keeps the family and strips the loose atom', () {
    final t = readColor();
    expect(t.loose, k.Type.atom('ioError'));
    expect(t.withoutLoose, color());
    // Without the name, every atom is loose and `else` strips them all.
    expect(readColor().written.withoutLoose.isEmpty, isTrue);
  });

  test('the pattern form strips a family member', () {
    final t = readColor().diff(atoms(['red']));
    expect('$t', '#blue | #green | #ioError');
    // What is left of the family is still the family's.
    expect('${t.withoutLoose}', '#blue | #green');
  });

  test('a join keeps an atom protected when either side protects it', () {
    final looseRed = atoms(['red']);
    for (final joined in [color().union(looseRed), looseRed.union(color())]) {
      expect(joined.loose, k.Type.empty);
      expect(joined.withoutLoose, color());
    }
  });

  test('a written type makes the atoms loose', () {
    final t = color().union(Ty.carrier(Carrier.integer)).written;
    expect(t.loose, color().atomSet);
    expect(t.withoutLoose, Ty.carrier(Carrier.integer));
  });

  test('narrowing keeps the marking', () {
    final t = readColor().union(Ty.carrier(Carrier.integer));
    final red = t.meet(atoms(['red', 'ioError']));
    expect(red.loose, k.Type.atom('ioError'));
    expect('${red.withoutLoose}', '#red');
    final notInt = t.diff(Ty.carrier(Carrier.integer));
    expect(notInt.withoutLoose, color());
  });

  test('a family atom that selects no arrow is an error', () {
    final int = Ty.carrier(Carrier.integer);
    final (_, errors) = operator('+', [int, color()]);
    expect(errors, ['`+` does not take (int, #blue | #green | #red)']);
    // Loose, the same atoms flow through.
    final (out, errs) = operator('+', [int, color().written]);
    expect(errs, isEmpty);
    expect('$out', '#blue | #green | #red');
    // The loose failure beside a family still flows; the family is still rejected.
    final (out2, errs2) = operator('+', [int, int.union(readColor())]);
    expect(errs2, hasLength(1));
    expect(out2.atomSet.contains(const k.Atom('ioError')), isTrue);
  });
}
