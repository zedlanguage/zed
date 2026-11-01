/// The tonicity of each scalar primitive in each argument, checked by running it. Each
/// claim is tested on every pair of points within one sign part of the argument, the other
/// argument fixed at each value of a window; `false` is below `true`, and a failure is
/// skipped, since no demand holds it.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/store.dart';

const w = 9;

/// The values an argument of `p` ranges over.
List<Value> values(Prim p) => switch (p) {
  Prim.and || Prim.or || Prim.not => const [Bool(false), Bool(true)],
  _ => [for (var n = -w; n <= w; n++) Int(n)],
};

/// A value's place in the order, null for a failure.
int? key(Value v) => switch (v) {
  Int(:final value) => value,
  Bool(:final value) => value ? 1 : 0,
  _ => null,
};

int? run(Prim p, List<Value> args) => key(eval(PrimApp(p, [for (final a in args) Lit(a)])));

/// Which way the result must move as the argument rises from `a` to `b`, with the other
/// argument `other`: `(dir: true)` up, `(dir: false)` down, `(dir: null)` either; null when
/// the claim says nothing about the pair.
({bool? dir})? direction(Tonicity t, int a, int b, int? other) {
  final o = other ?? 0;
  return switch (t) {
    Tonicity.up => (dir: true),
    Tonicity.down => (dir: false),
    Tonicity.constant => (dir: null),
    Tonicity.upWhereOtherNonneg => (dir: o >= 0),
    Tonicity.downWhereOtherNonneg => (dir: o < 0),
    Tonicity.downThenUp when b <= 0 => (dir: false),
    Tonicity.downThenUp when a >= 0 => (dir: true),
    // A pair across 0 is not in one sign part.
    Tonicity.downThenUp || Tonicity.none => null,
  };
}

/// Checks that `p` moves in argument `arg` as `t` says; returns the number of pairs checked.
/// Throws a [String] naming the first pair that does not.
int holds(Prim p, int arg, Tonicity t, int arity) {
  final vs = values(p);
  final others = arity == 1 ? const <Value?>[null] : <Value?>[...vs];
  var n = 0;
  for (final o in others) {
    for (final a in vs) {
      for (final b in vs) {
        final (ka, kb) = (key(a)!, key(b)!);
        // Within one sign part of the argument: both below 0 or both at least 0.
        if (ka >= kb || (ka < 0) != (kb < 0) && t != Tonicity.downThenUp) continue;
        final d = direction(t, ka, kb, o == null ? null : key(o));
        if (d == null) continue;
        int? at(Value x) => run(p, [if (o != null && arg == 1) o, x, if (o != null && arg == 0) o]);
        final (fa, fb) = (at(a), at(b));
        if (fa == null || fb == null) continue;
        final ok = switch (d.dir) {
          true => fa <= fb,
          false => fa >= fb,
          null => fa == fb,
        };
        if (!ok) throw '$p arg $arg $t: $a -> $fa, $b -> $fb, other $o';
        n++;
      }
    }
  }
  return n;
}

const table = <(Prim, int, Tonicity?)>[
  (Prim.add, 0, Tonicity.up),
  (Prim.add, 1, Tonicity.up),
  (Prim.sub, 0, Tonicity.up),
  (Prim.sub, 1, Tonicity.down),
  (Prim.mul, 0, Tonicity.upWhereOtherNonneg),
  (Prim.mul, 1, Tonicity.upWhereOtherNonneg),
  (Prim.intDiv, 0, Tonicity.upWhereOtherNonneg),
  (Prim.intDiv, 1, Tonicity.downWhereOtherNonneg),
  (Prim.mod, 0, null),
  (Prim.mod, 1, null),
  (Prim.min, 0, Tonicity.up),
  (Prim.min, 1, Tonicity.up),
  (Prim.max, 0, Tonicity.up),
  (Prim.max, 1, Tonicity.up),
  (Prim.neg, 0, Tonicity.down),
  (Prim.abs, 0, Tonicity.downThenUp),
  (Prim.lt, 0, Tonicity.down),
  (Prim.lt, 1, Tonicity.up),
  (Prim.le, 0, Tonicity.down),
  (Prim.le, 1, Tonicity.up),
  (Prim.gt, 0, Tonicity.up),
  (Prim.gt, 1, Tonicity.down),
  (Prim.ge, 0, Tonicity.up),
  (Prim.ge, 1, Tonicity.down),
  (Prim.not, 0, Tonicity.down),
  (Prim.and, 0, Tonicity.up),
  (Prim.and, 1, Tonicity.up),
  (Prim.or, 0, Tonicity.up),
  (Prim.or, 1, Tonicity.up),
  (Prim.eq, 0, null),
  (Prim.ne, 1, null),
  (Prim.concat, 0, null),
];

int arity(Prim p) => p.arity ?? 2;

void main() {
  test('the table gives each primitive its tonicity', () {
    for (final (p, arg, t) in table) {
      expect(primTonicity(p, arg), t, reason: '$p arg $arg');
    }
  });

  test('each claimed tonicity holds when the primitive is run', () {
    var checked = 0;
    for (final (p, arg, t) in table) {
      if (t == null) continue;
      final n = holds(p, arg, t, arity(p));
      expect(n, greaterThan(0), reason: '$p arg $arg: no pair checked');
      checked += n;
    }
    expect(checked, greaterThan(10000));
  });

  test('each power with a constant exponent has its tonicity', () {
    for (var k = 0; k <= 5; k++) {
      final t = tonicity(Op.pow(k), 0);
      int pw(int x) => run(Prim.pow, [Int(x), Int(k)])!;
      for (var a = -w; a <= w; a++) {
        for (var b = a + 1; b <= w; b++) {
          final d = direction(t, a, b, null);
          if (d == null) continue;
          final ok = switch (d.dir) {
            true => pw(a) <= pw(b),
            false => pw(a) >= pw(b),
            null => pw(a) == pw(b),
          };
          expect(ok, isTrue, reason: 'x ** $k $t: $a, $b');
        }
      }
    }
  });

  test('a wrong claim is caught', () {
    for (final (p, arg, t) in const [
      (Prim.sub, 1, Tonicity.up),
      (Prim.mul, 0, Tonicity.up),
      (Prim.intDiv, 1, Tonicity.upWhereOtherNonneg),
      (Prim.abs, 0, Tonicity.up),
      (Prim.lt, 0, Tonicity.up),
      (Prim.not, 0, Tonicity.up),
      (Prim.or, 0, Tonicity.down),
      (Prim.mod, 0, Tonicity.up),
      (Prim.max, 1, Tonicity.constant),
    ]) {
      expect(() => holds(p, arg, t, arity(p)), throwsA(isA<String>()), reason: '$p arg $arg $t');
    }
  });
}
