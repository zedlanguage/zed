/// Each reduction on its own, the enumeration of listed sets, and controls: the check of `random`
/// rejects a scope that leaves out a value reaching its arm.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart' hide Lattice;
import 'package:zed/presburger.dart' as presburger;
import 'package:zed/store.dart';

import 'shape.dart';
import 'support.dart';

/// The scope of `n` within `lo..=hi`.
Scope within(int lo, int hi) => ints(['n']).assume(
  prim(Prim.and, [
    prim(Prim.ge, [const Var('n'), lit(lo)]),
    prim(Prim.le, [const Var('n'), lit(hi)]),
  ]),
  true,
  none,
);

/// `s` with `t` written as holding, reduced.
Scope written(Scope s, Term t) => s
  ..write(t)
  ..reduce();

/// The scope of `n` of the type listing `vs`.
Scope among(Iterable<int> vs) => Scope([
  ('n', Product.ofType(Type.unionAll([for (final v in vs) Type.lit(Int(v))!]))),
]);

List<int> upTo(int lo, int hi) => [for (var v = lo; v <= hi; v++) v];

/// `count(k) > 1 || n == 0` for a `count` that takes about `2k` steps.
Term slowUnlessZero(Term k) {
  Term half() => prim(Prim.intDiv, [const Var('k'), lit(2)]);
  Term me(Term arg) => App(const Var('me'), [const Var('me'), arg]);
  final body = If(
    prim(Prim.le, [const Var('k'), lit(1)]),
    lit(1),
    prim(Prim.add, [
      me(half()),
      me(prim(Prim.sub, [const Var('k'), half()])),
    ]),
  );
  final f = Lam(['me', 'k'], body);
  final count = App(f, [f, k]);
  // `n == 0` is cheap; at any other `n`, `count` runs first and is false at `k <= 1`.
  return If(
    prim(Prim.eq, [const Var('n'), lit(0)]),
    const Lit(Bool(true)),
    prim(Prim.gt, [count, lit(1)]),
  );
}

/// `scope` with the product of `name` changed by `change` on a copy.
void edit(Scope scope, String name, void Function(Product) change) {
  final p = scope.names[name]!.copy();
  change(p);
  scope.names = scope.names.put(name, p);
}

void main() {
  test('a single value fixes the congruence and the finite set', () {
    final s = ints(['n']).assume(prim(Prim.eq, [const Var('n'), lit(5)]), true, none);
    expect('${s.get('n')}', 'ints [5..=5]\ncongruence 5\nfinite {5}\ntype 5\n');
  });

  test('a congruence narrows the interval ends', () {
    // `n mod 4 == 1` within `2..=20` moves the ends to `5` and `17`.
    final s = within(2, 20).assume(
      prim(Prim.eq, [
        prim(Prim.mod, [const Var('n'), lit(4)]),
        lit(1),
      ]),
      true,
      none,
    );
    expect('${s.get('n').ints.hull()}', '[5..=17]');
    expect('${s.get('n').cell.congruence.element}', '1 mod 4');
  });

  test('enumeration keeps the members a written constraint holds at', () {
    // `n * n mod 5 == 1` among `0..=10`, listed: 1, 4, 6, 9.
    final t = prim(Prim.eq, [
      prim(Prim.mod, [
        prim(Prim.mul, [const Var('n'), const Var('n')]),
        lit(5),
      ]),
      lit(1),
    ]);
    final s = written(among(upTo(0, 10)), t);
    expect('${s.get('n').ints}', '[1..=1, 4..=4, 6..=6, 9..=9]');
  });

  test('enumeration reads the other names when they are static', () {
    // `m` is 3, so `n mod m == 1` among `0..=10`, listed, keeps 1, 4, 7, 10.
    var s = among(upTo(0, 10));
    s.names = s.names.put('m', Product.literal(const Int(3)));
    final t = prim(Prim.eq, [
      prim(Prim.mod, [const Var('n'), const Var('m')]),
      lit(1),
    ]);
    s = written(s, t);
    expect('${s.get('n').ints}', '[1..=1, 4..=4, 7..=7, 10..=10]');
    // With `m` known only at run time, the constraint has two open names and is not
    // enumerated.
    s = within(0, 10);
    s.names = s.names.put('m', Product.ofType(Type.integer));
    s = written(s, t);
    expect('${s.get('n').ints}', '[0..=10]');
  });

  test('a written constraint on static names that fails makes the scope bottom', () {
    var s = Scope([('m', Product.literal(const Int(3)))]);
    expect(s.bottom, isFalse);
    s = written(s, prim(Prim.gt, [const Var('m'), lit(5)]));
    expect(s.bottom, isTrue);
  });

  test('a listed set is enumerated and a range is not', () {
    // `n * n mod 7` is 1, 4, 2, 2, 4, 1 at 1..=6.
    final t = prim(Prim.ne, [
      prim(Prim.mod, [
        prim(Prim.mul, [const Var('n'), const Var('n')]),
        lit(7),
      ]),
      lit(2),
    ]);
    expect('${written(among(upTo(1, 6)), t).get('n').ints}', '[1..=2, 5..=6]');
    // The same members as a range are left to interval reasoning, however few they are.
    expect('${written(within(1, 6), t).get('n').ints}', '[1..=6]');
  });

  test('a constraint whose form does not show it ends removes nothing', () {
    // `count` calls itself through its parameter `me`, so however cheap it is at each member
    // (`count(1) = 1`, so the constraint is false at 1), the constraint is not evaluated.
    final s = written(among(upTo(0, 3)), slowUnlessZero(const Var('n')));
    expect('${s.get('n').ints}', '[0..=3]');
    // A constraint whose form shows it ends, over the same members, removes 1 and 3.
    final even = prim(Prim.or, [
      prim(Prim.eq, [
        prim(Prim.mod, [const Var('n'), lit(2)]),
        lit(0),
      ]),
      prim(Prim.eq, [const Var('n'), lit(-1)]),
    ]);
    expect('${written(among(upTo(0, 3)), even).get('n').ints}', '[0..=0, 2..=2]');
  });

  test('a type widens to its whole base type', () {
    final one = TypeElement(Type.lit(const Int(1))!);
    final two = TypeElement(Type.lit(const Int(2))!);
    final none = Landmarks.none();
    final integer = TypeElement(Type.integer);
    expect(one.widen(one.join(two), none), one.join(integer));
    expect(one.widen(one.join(two), none).type.subtype(Type.integer), isTrue);
    // A part that does not grow is kept.
    expect(one.widen(one, none), one);
    // A narrowing takes a part only while it is whole: `int` narrows to `1`, and `1 | 2`
    // stays, so a chain of narrowings is finite.
    expect(integer.narrow(one, none), one);
    expect(one.join(two).narrow(one, none), one.join(two));
    expect(integer.join(TypeElement(Type.boolean)).narrow(one, none), one);
    expect(TypeElement(Type.empty).leq(one) && one.leq(TypeElement(Type.top)), isTrue);
  });

  test('an empty interval removes int from the type', () {
    var p = Product.ofType(Type.integer | Type.boolean);
    p.cell.ints.element = Bounds.ints(IntervalSet.empty());
    expect(Scope([('v', p)]).get('v').ty.element.type, Type.boolean);
    // With only `int`, the product is empty and the scope bottom.
    p = Product.ofType(Type.integer);
    p.cell.ints.element = Bounds.ints(IntervalSet.empty());
    expect(Scope([('v', p)]).bottom, isTrue);
  });

  test('the check rejects a scope that leaves out a reached value', () {
    // `x >= 0` then `y < x`; the first arm holds every `x` in `0..`.
    final s = Shape(
      const Var('x'),
      prim(Prim.ge, [const Var('x'), lit(0)]),
      prim(Prim.lt, [const Var('y'), const Var('x')]),
      0,
    );
    var a = s.arms();
    expect(check(s, a), greaterThan(0));
    // Leave `x = 3` out of the first arm.
    edit(a[0].scope, 'x', (x) {
      x.cell.ints.element = Bounds.ints(IntervalSet.single(3).complementIn(x.ints));
    });
    expect(
      () => check(s, a),
      throwsA(isA<StateError>().having((e) => e.message, 'message', contains('reaches arm 0'))),
    );
    // Mark the inner arm unreachable: points with `y < x` reach it.
    a = s.arms();
    a[1].scope.bottom = true;
    expect(
      () => check(s, a),
      throwsA(isA<StateError>().having((e) => e.message, 'message', contains('reaches arm 1'))),
    );
    // Drop the relation's effect: put `y = 4` beside `x = 2` in the inner arm by a wrong
    // relation `y >= x`.
    a = s.arms();
    a[1].scope.relation = presburger.Formula.and([
      a[1].scope.relation,
      presburger.Con.ge(
        presburger.Lin.atom(const presburger.Sym('y')),
        presburger.Lin.atom(const presburger.Sym('x')),
      ),
    ]);
    expect(
      () => check(s, a),
      throwsA(isA<StateError>().having((e) => e.message, 'message', contains('reaches arm 1'))),
    );
  });

  test('an equality between names of different parity is unreachable', () {
    // `x` even, `y` odd and `x == y`: no value meets all three. Passing the relation and the
    // congruences to each other one at a time moves `x`'s lower bound up by one step per
    // pass, without end; the relation must read the congruences itself.
    const src =
        'ok = (x, y) -> if x mod 2 == 0 && y mod 2 == 1 && x >= 0 && x == y { x } else { 0 };';
    final (_, _, a) = armsOf(src);
    final then = arm(a, '(x == y)', true);
    expect(then.reachable, isFalse, reason: '${then.scope}');
  });
}
