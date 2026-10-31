/// The rules: facet ordering and hints, the termination ranks, the independence of the normal
/// form from the order the rules are applied in, and the version tag.
library;

import 'package:test/test.dart';
import 'package:zed/canon.dart';
import 'package:zed/kernel.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';
import 'harness.dart';

/// `balance = (deposits, withdrawals) -> deposits - withdrawals`, in units of cents.
Def balance(String a, String b) => Def(
  'balance',
  lam([a, b], prim(Prim.sub, [var_(a), var_(b)])),
  facets: [facet('units', 'cent'), facet('monotone', const Atom('none'))],
);

bool sorted(List<Facet> f) {
  for (var i = 0; i + 1 < f.length; i++) {
    if (f[i].compareTo(f[i + 1]) >= 0) return false;
  }
  return true;
}

/// A random definition: a body with binders, facets with repeats and hints in random order,
/// and sometimes a domain.
Def random(Rng rng) {
  const names = ['n', 'acc', 'row'];
  var body = var_(rng.pick(names));
  for (var i = rng.below(5); i > 0; i--) {
    final x = rng.pick(names);
    body = rng.below(2) == 0
        ? lam([x], body)
        : let_(x, lit(rng.int_(0, 3)), prim(Prim.add, [body, var_(x)]));
  }
  final facets = [
    for (var i = rng.below(6); i > 0; i--)
      Facet(
        // Dart evaluates arguments in order, so the hint is drawn first, as in the order of
        // the fields.
        hint: rng.below(3) == 0,
        rng.pick(['units', 'monotone', 'doc']),
        Int(rng.int_(0, 2)),
      ),
  ];
  final domain = rng.below(2) == 0
      ? Domain(
          IntervalSet.of(rng.int_(-5, 5), rng.int_(-5, 15)),
          Congruence(rng.pick([1, 2, 3]), rng.int_(0, 2)),
          rng.below(2) == 0
              ? const FiniteSet.top()
              : FiniteSet.of([for (var i = 0; i < 3; i++) rng.int_(-5, 15)]),
        )
      : null;
  return Def('d', body, domain: domain, facets: facets);
}

void main() {
  test('facets in any order and repeated give one address', () {
    final a = balance('deposits', 'withdrawals');
    final b = balance('d', 'w');
    b.facets.setAll(0, b.facets.reversed.toList());
    b.facets.add(facet('units', 'cent'));
    expect(addr(b), addr(a));
    // A hint never changes the address; a changed facet value does.
    b.facets.add(Facet('doc', Str('the account balance'), hint: true));
    expect(addr(b), addr(a));
    final c = a.copy()..facets[0] = facet('units', 'dollar');
    expect(addr(c), isNot(addr(a)));
    // The normal form keeps the facets sorted, once each.
    final n = canonicalize(b);
    expect(n.facets.length, 2);
    expect(sorted(n.facets), isTrue);
  });

  test('every rule decreases its rank and no later rule raises an earlier one', () {
    final rng = Rng(0x7e57);
    final fired = [0, 0, 0, 0];
    for (var i = 0; i < randomInstances; i++) {
      final d = random(rng);
      while (true) {
        final before = ranks(d);
        final r = rules.indexWhere((r) => r.apply(d));
        if (r < 0) break;
        final after = ranks(d);
        fired[r]++;
        expect(after[r], lessThan(before[r]), reason: '${rules[r].name} did not decrease');
        for (var e = 0; e < r; e++) {
          expect(
            after[e],
            lessThanOrEqualTo(before[e]),
            reason: '${rules[r].name} raised the rank of ${rules[e].name}',
          );
        }
      }
    }
    expect(fired.every((n) => n > 50), isTrue, reason: '$fired');
  });

  test('the facet rank counts the pairs out of order and the facets', () {
    final d = def('d', lit(0));
    final (a, b, c) = (facet('doc', 1), facet('doc', 2), facet('doc', 3));
    // `c a a b`: `c` is before three smaller facets; the equal `a`s are not out of order.
    d.facets.addAll([c, a, a, b]);
    expect(ranks(d)[2], 3 + 4);
    d.facets
      ..clear()
      ..addAll([b, c, a]);
    expect(ranks(d)[2], 2 + 3);
  });

  test('the normal form does not depend on the order of the rules', () {
    final rng = Rng(0xc0f1);
    for (var i = 0; i < randomInstances; i++) {
      final d0 = random(rng);
      final d = d0.copy();
      // Any rule that applies, chosen at random, until none does.
      while (true) {
        final live = [
          for (var r = 0; r < rules.length; r++)
            if (rules[r].apply(d.copy())) r,
        ];
        if (live.isEmpty) break;
        rules[live[rng.below(live.length)]].apply(d);
      }
      expect(d == canonicalize(d0), isTrue, reason: '$d0');
    }
  });

  test('the version tag separates rule sets', () {
    final d = balance('deposits', 'withdrawals');
    expect(version, 2);
    expect(addressAt(version, d, none), isNot(addressAt(version + 1, d, none)));
    // The address of this definition under version 2. A change to a rule or to the
    // serialization changes it: increment the version, and pin the new address here.
    expect('${addr(d)}', '44c341e4f0e9d1f74b145c2678686615f33c73594579e44571313e589ba55425');
  });

  test('two normal forms share a serialization only when equal', () {
    final rng = Rng(0x5e71);
    final forms = [for (var i = 0; i < randomInstances ~/ 2; i++) canonicalize(random(rng))];
    var equal = 0;
    for (final a in forms) {
      final sa = serialize(a, none);
      for (final b in forms) {
        final sb = serialize(b, none);
        var same = sa.length == sb.length;
        for (var i = 0; same && i < sa.length; i++) {
          same = sa[i] == sb[i];
        }
        expect(same, a == b, reason: '$a\n$b');
        if (same) equal++;
      }
    }
    // Beyond the diagonal, distinct random definitions met in one normal form.
    expect(equal, greaterThan(forms.length));
    expect('${addr(forms[0])}'.length, 64);
  });
}
