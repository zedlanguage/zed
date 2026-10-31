/// Domain normal forms: integer facts that admit the same integers share a normal form and an
/// address, checked on the examples of sec:constraints and by brute force.
library;

import 'package:test/test.dart';
import 'package:zed/canon.dart';
import 'package:zed/kernel.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';
import 'harness.dart';

/// `index: <domain> = i` as a definition.
Def index(Domain d) => Def('index', var_('i'), domain: d);

/// A random domain: up to three pieces with endpoints in -20..=20 or infinite, a class of
/// modulus 0, 1, 2, 3, 4 or 6, and half the time a finite set in -25..=25.
Domain random(Rng rng) {
  End end(End inf) => rng.below(5) == 0 ? inf : Fin(rng.int_(-20, 20));
  final pieces = [for (var i = rng.below(4); i > 0; i--) (end(negInf), end(posInf))];
  final c = Congruence(rng.pick([0, 1, 1, 2, 3, 4, 6]), rng.int_(-20, 20));
  final finite = rng.below(2) == 0
      ? const FiniteSet<int>.top()
      : FiniteSet.of([for (var i = rng.below(7); i > 0; i--) rng.int_(-25, 25)]);
  return Domain(IntervalSet.fromPieces(pieces), c, finite);
}

/// The members in -60..=60. Beyond ±25 every domain above repeats with a period dividing 12,
/// so this window decides equality of the sets admitted.
List<int> members(Domain d) => [
  for (var v = -60; v <= 60; v++)
    if (d.contains(v)) v,
];

void main() {
  test('one set of integers has one normal form', () {
    final oneModFour = Congruence(4, 1);
    final a = Domain(IntervalSet.of(0, 10), oneModFour, const FiniteSet.top());
    final b = Domain(IntervalSet.of(1, 9), oneModFour, const FiniteSet.top());
    final c = Domain(IntervalSet.top(), Congruence.top, FiniteSet.of([1, 5, 9]));
    final d = Domain(
      IntervalSet.of(1, 1).join(IntervalSet.of(5, 9)),
      oneModFour,
      const FiniteSet.top(),
    );
    for (final x in [b, c, d]) {
      expect(x.normal(), a.normal());
      expect(addr(index(x)), addr(index(a)));
    }
    expect(a.normal().ints, IntervalSet.of(1, 9));
    expect(a.normal().congruence, oneModFour);
    // `int[2..=4]` with `1 mod 4` admits nothing, like every other empty domain.
    final empty = Domain(IntervalSet.of(2, 4), oneModFour, const FiniteSet.top());
    final nothing = Domain(IntervalSet.top(), Congruence.top, FiniteSet.of(<int>[]));
    expect(empty.normal(), nothing.normal());
    // An HTTP status in 400..=499 among the codes the client handles is just 404.
    final status = Domain(IntervalSet.of(400, 499), Congruence.top, FiniteSet.of([200, 404, 500]));
    expect(
      status.normal(),
      Domain(IntervalSet.single(404), Congruence.single(404), const FiniteSet.top()),
    );
    // An even count of at least 2 is not an even count from 0.
    Domain even(int lo) =>
        Domain(IntervalSet.range(Fin(lo), posInf), Congruence(2, 0), const FiniteSet.top());
    expect(even(1).normal(), even(2).normal());
    expect(even(0).normal(), isNot(even(2).normal()));
    expect(addr(index(even(0))), isNot(addr(index(even(2)))));
  });

  test('the normal form admits the same integers and is unique', () {
    final rng = Rng(0xd0d0);
    final byMembers = <String, Domain>{};
    var collisions = 0;
    for (var i = 0; i < randomInstances * 8; i++) {
      final d = random(rng);
      final n = d.normal();
      expect(members(n), members(d), reason: '$d');
      expect(n.normal(), n, reason: 'not idempotent on $d');
      expect(n.rank, 0);
      final key = members(d).join(',');
      if (byMembers[key] case final m?) {
        expect(n, m, reason: 'two normal forms for one set: $d');
        collisions++;
      } else {
        byMembers[key] = n;
      }
    }
    // Many spellings of one set were met, so uniqueness was tested.
    expect(collisions, greaterThan(1000));
  });
}
