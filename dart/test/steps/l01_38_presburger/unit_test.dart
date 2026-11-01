/// The relation printer and the Omega test's dark shadow.
library;

import 'package:test/test.dart';
import 'package:zed/presburger.dart';

Lin lin(Map<String, int> terms, int k) {
  var l = Lin.constant(BigInt.from(k));
  terms.forEach((s, c) => l = l.plus(Lin.atom(Sym(s)).times(BigInt.from(c))));
  return l;
}

Formula ge(Map<String, int> terms, int k) => Con(lin(terms, k), Rel.ge);

void main() {
  test('a relation prints with the first atom on the left', () {
    expect('${ge({'a': -1, 'b': -1}, 49)}', 'a + b <= 49');
    expect('${ge({'i': -1, 'n': 1}, -2)}', 'i <= n - 2');
    expect('${ge({'x': 2}, -3)}', '2 * x >= 3');
  });

  test('the dark shadow decides integer points, and the gap is undecided', () {
    // 2x = 2y + 1 has real points and no integer point.
    expect(satisfiable(Con(lin({'x': 2, 'y': -2}, -1), Rel.eq)), isNull);
    // 3 <= 2x <= 3 has none either. 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has none
    // (Pugh's example), but its dark shadow is empty and its real shadow is not: only the
    // splinters, not taken, would settle it.
    expect(
      satisfiable(
        Formula.and([
          ge({'x': 2}, -3),
          ge({'x': -2}, 3),
        ]),
      ),
      isNull,
    );
    final pugh = Formula.and([
      ge({'x': 11, 'y': 13}, -27),
      ge({'x': -11, 'y': -13}, 45),
      ge({'x': 7, 'y': -9}, 10),
      ge({'x': -7, 'y': 9}, 4),
    ]);
    expect(() => satisfiable(pugh), throwsA(isA<Over>()));
    // Shifted to hold the point (2, 1), the dark shadow finds a point.
    final shifted = Formula.and([
      ge({'x': 11, 'y': 13}, -27),
      ge({'x': -11, 'y': -13}, 45),
      ge({'x': 7, 'y': -9}, -5),
      ge({'x': -7, 'y': 9}, 5),
    ]);
    final m = satisfiable(shifted)!;
    expect(shifted.holds(m), isTrue, reason: '$m');
  });
}
