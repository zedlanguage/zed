/// The evidence record of `fold` and `fix`: part of the term, so part of its address, and read
/// by the checker, not by the evaluator.
library;

import 'package:test/test.dart';
import 'package:zed/address.dart';
import 'package:zed/canon.dart';
import 'package:zed/kernel.dart';

/// The total of three sales, its `+` carrying the evidence `ev`.
Term salesTotal(List<(String, Grade)> ev) => Fold(
  lit(
    Family.of([
      for (final (k, x) in [(0, 120), (1, 75), (2, 5)]) (Int(k), Int(x)),
    ]),
  ),
  const PrimFn(Prim.add),
  lit(0),
  1,
  {for (final (p, g) in ev) p: g},
);

ContentAddress addr(Term body) => address(Def('total', body), (_) => null);

void main() {
  test('the evidence is part of the address', () {
    const axioms = [('associative', Grade.axiom), ('commutative', Grade.axiom)];
    final a = addr(salesTotal(axioms));
    // The same record built in another order is the same record.
    expect(addr(salesTotal(axioms.reversed.toList())), a);
    // A different grade, a missing property or no record at all is a different term.
    expect(
      addr(salesTotal([('associative', Grade.axiom), ('commutative', Grade.assumed)])),
      isNot(a),
    );
    expect(addr(salesTotal(axioms.sublist(0, 1))), isNot(a));
    expect(addr(salesTotal([])), isNot(a));
  });

  test('the evaluator does not read the evidence', () {
    expect(eval(salesTotal([('associative', Grade.proved)])), const Int(200));
    expect(eval(salesTotal([('associative', Grade.assumed)])), const Int(200));
  });

  test('only the proof grades may change a type, and each grade prints by name', () {
    expect([for (final g in Grade.values) g.isProofGrade], [true, true, true, false, false, false]);
    expect(
      '${salesTotal([])}',
      'fold({0 -> 120, 1 -> 75, 2 -> 5}, (+), identity: 0, depth: 1, ev: {})',
    );
    final t = salesTotal([for (final (i, g) in Grade.values.indexed) ('p$i', g)]);
    expect(
      '$t',
      endsWith(
        'ev: { p0: axiom, p1: checkedExhaustive, p2: proved, p3: bounded, p4: obligated, '
        'p5: assumed })',
      ),
    );
  });

  test('a fix carries its evidence into the address too', () {
    Term reach(Map<String, Grade> ev) =>
        Fix(var_('start'), var_('next'), 'this', 'k', const Lattice(PrimFn(Prim.union)), ev);
    expect(addr(reach({'monotone': Grade.proved})), isNot(addr(reach({}))));
  });
}
