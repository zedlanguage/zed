/// The Trick: split a function on a parameter only when its domain is finite, and only on the
/// values of the domain the program's static calls pass it; the split function computes what
/// the function does.
library;

import 'package:test/test.dart';
import 'package:zed/elab.dart';
import 'package:zed/kernel.dart';
import 'package:zed/stage.dart';

import '../l01_16_elaboration/elab.dart';

List<Value> ints(List<int> vs) => [for (final v in vs) Int(v)];

/// The values `c` splits on, or its reason prefixed with `keep: `.
Object decided(Choice c) => switch (c) {
  Split(:final values) => values,
  Keep(:final why) => 'keep: $why',
};

/// A pricing rule: the tier decides the rate, and each tier's copy has its branch cut.
const price =
    'rate = 8;\n'
    'price(tier, n: int) = if tier == #gold { n * rate } else { n * (rate + 2) };\n'
    'total(m: int) = price(tier: #gold, n: m) + price(tier: #basic, n: 2 * m) + '
    'price(tier: #gold, n: 5);\n';

final tiers = TypeDomain(Type.atom('gold') | Type.atom('basic'));

void main() {
  test('a finite domain is split on the values passed and an infinite one is kept', () {
    const d = Ints(0, 256);
    expect(decided(trick(d, ints([-1, 3, 7, 300]))), ints([3, 7]));
    // No bound on the domain's size: only the values passed are split on.
    expect(decided(trick(const Ints(0, 1 << 40), ints([1 << 39]))), ints([1 << 39]));
    expect(decided(trick(d, ints([300]))), 'keep: no static call passes a value of the domain');
    expect(
      decided(trick(const Ints(0, null), ints([3]))),
      'keep: an unbounded integer domain is infinite',
    );
    expect(trick(TypeDomain(Type.integer), ints([3])), isA<Keep>());
    expect(trick(TypeDomain(Type.string), [Str('a')]), isA<Keep>());
  });

  test('a finite type is split on its members passed', () {
    const bools = [Bool(false), Bool(true)];
    expect(decided(trick(TypeDomain(Type.boolean), bools)), bools);
    const given = [Atom('gold'), Atom('silver')];
    expect(decided(trick(tiers, given)), [const Atom('gold')]);
    // A type with a payload atom or a function is not listed.
    final payload = Type.atomWith('e', Type.tuple([Type.integer]));
    expect(trick(TypeDomain(payload), given), isA<Keep>());
    expect(trick(TypeDomain(Type.partial(Type.integer, Type.integer)), given), isA<Keep>());
  });

  test('a split function computes what the function does', () {
    final u = elab(price);
    final (lam, report) = split(u, 'price', 0, tiers);
    expect(report.left, isEmpty);
    // Each tier's arm has its branch cut and its rate computed; the general body is last.
    expect(
      '$lam',
      '(tier, n) -> match tier { #basic -> (n * 10), #gold -> (n * 8), _ -> if (tier == '
          '#gold) { (n * 8) } else { (n * 10) } }',
    );
    final staged = Unit([
      for (final d in u.defs) d.name == 'price' ? Def(d.name, d.kernel, lam, d.firstOrder) : d,
    ], u.tests);
    for (final tier in ['gold', 'basic']) {
      for (final n in [0, 3, -7]) {
        Value call(Unit unit) =>
            Evaluator(World())
                .run(withPrelude(App(unit.get('price')!, [Lit(Atom(tier)), Lit(Int(n))])));
        expect(call(staged), call(u), reason: '$tier $n');
      }
    }
  });

  test('the values passed are read from the calls once mixed', () {
    var u = elab(price);
    expect(passed(u, 'price', 0), [const Atom('basic'), const Atom('gold')]);
    // `price(tier: #gold, n: 5)` is all build-stage, so the build computes it and leaves no
    // call; `n` is passed no other literal.
    expect(passed(u, 'price', 1), isEmpty);
    // A call in a definition after mixing: `k` is a build-stage name.
    u = elab(
      'k = 2 + 2;\nf(x: int, y: int) = x + y;\n'
      'z(a: int) = f(x: k, y: a) + f(x: 4, y: a + 1) + f(x: a, y: a);\n',
    );
    expect(passed(u, 'f', 0), ints([4]));
    // One arm per value passed, however many calls pass it, and the general body last.
    final (lam, _) = split(u, 'f', 0, const Ints(0, 1 << 40));
    expect(lam, isA<Lam>().having((l) => l.body, 'body', isA<Match>()));
    expect(((lam as Lam).body as Match).arms, hasLength(2));
  });

  test('the trick keeps a function on an infinite domain', () {
    expect(
      () => split(elab(price), 'price', 1, const Ints(null, null)),
      throwsA(isA<Kept>().having((k) => k.why, 'why', 'an unbounded integer domain is infinite')),
    );
  });
}
