/// Soundness on random terms: every point that meets the demand is in the preimage, and where
/// the preimage is marked exact, every point in it meets the demand. The terms mix the scalar
/// operators, including divisions that can fail, with tests, branches and `min` and `max`,
/// over random domains: finite ones the enumeration may take, and wide or unbounded ones it
/// cannot, so that the catalog's own exactness is checked too.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/store.dart';

import '../../support/instances.dart';
import 'support.dart';

/// The window each domain is checked over.
const window = (-15, 15);

Term lit(int n) => Lit(Int(n));

/// A random integer term over `x` and `y`, of depth at most `d`.
Term intTerm(Rng rng, int d) {
  if (d == 0 || rng.below(4) == 0) {
    return switch (rng.below(5)) {
      0 || 1 => const Var('x'),
      2 => const Var('y'),
      _ => lit(rng.int_(-6, 6)),
    };
  }
  Term sub() => intTerm(rng, d - 1);
  // One operand a constant half the time, as the exact entries need.
  Term pair(Prim p) {
    final a = sub();
    final b = rng.below(2) == 0 ? lit(rng.int_(-5, 5)) : sub();
    return rng.below(2) == 0 ? PrimApp(p, [a, b]) : PrimApp(p, [b, a]);
  }

  switch (rng.below(12)) {
    case 0 || 1:
      return pair(Prim.add);
    case 2:
      return pair(Prim.sub);
    case 3 || 4:
      return pair(Prim.mul);
    case 5:
      return pair(Prim.intDiv);
    case 6:
      return pair(Prim.mod);
    case 7:
      return PrimApp(Prim.neg, [sub()]);
    case 8:
      return PrimApp(Prim.abs, [sub()]);
    case 9:
      return pair(rng.pick(const [Prim.min, Prim.max]));
    case 10:
      final base = sub();
      return PrimApp(Prim.pow, [base, lit(rng.int_(0, 3))]);
    default:
      final g = boolTerm(rng, d - 1);
      final a = sub();
      return If(g, a, sub());
  }
}

/// A random test over `x` and `y`, of depth at most `d`.
Term boolTerm(Rng rng, int d) {
  const cmp = [Prim.lt, Prim.le, Prim.gt, Prim.ge, Prim.eq, Prim.ne];
  if (d == 0 || rng.below(3) != 0) {
    final e = d == 0 ? 0 : d - 1;
    final a = intTerm(rng, e);
    final b = rng.below(2) == 0 ? lit(rng.int_(-12, 12)) : intTerm(rng, e);
    return PrimApp(rng.pick(cmp), [a, b]);
  }
  Term sub() => boolTerm(rng, d - 1);
  switch (rng.below(4)) {
    case 0:
      return PrimApp(Prim.not, [sub()]);
    case 1:
      final a = sub();
      return PrimApp(Prim.and, [a, sub()]);
    case 2:
      final a = sub();
      return PrimApp(Prim.or, [a, sub()]);
    default:
      final g = sub();
      final a = sub();
      return If(g, a, sub());
  }
}

/// `t` with each variable leaf, one time in two, read through a call of one of the functions
/// `g0` to `g{fs - 1}` on itself plus a constant.
Term withCalls(Rng rng, Term t, int fs) {
  switch (t) {
    case Var() when fs > 0 && rng.below(2) == 0:
      final g = Var('g${rng.below(fs)}');
      return App(g, [
        PrimApp(Prim.add, [t, lit(rng.int_(-2, 2))]),
      ]);
    case PrimApp(:final prim, :final args):
      return PrimApp(prim, [for (final a in args) withCalls(rng, a, fs)]);
    case If(:final cond, :final then, :final orElse):
      final g = withCalls(rng, cond, fs);
      final a = withCalls(rng, then, fs);
      return If(g, a, withCalls(rng, orElse, fs));
    default:
      return t;
  }
}

/// `t` with `x` renamed `v`.
Term overV(Term t) => switch (t) {
  Var(name: 'x') => const Var('v'),
  PrimApp(:final prim, :final args) => PrimApp(prim, [for (final a in args) overV(a)]),
  If(:final cond, :final then, :final orElse) => If(overV(cond), overV(then), overV(orElse)),
  _ => t,
};

/// A random term over `x` and `y` that calls the functions `g0` to `g{functions - 1}`, each a
/// random term over its parameter `v` and `y` that may call the ones before it.
Term withFunctions(Rng rng, Term t) {
  const functions = 3;
  var out = withCalls(rng, t, functions);
  final bodies = [for (var k = 0; k < functions; k++) withCalls(rng, overV(intTerm(rng, 2)), k)];
  for (var k = functions - 1; k >= 0; k--) {
    out = Let('g$k', Lam(const ['v'], bodies[k]), out);
  }
  return out;
}

/// A random domain: small and finite, wide, or unbounded on one or both sides.
IntervalSet domain(Rng rng) {
  final lo = rng.int_(-15, 10);
  final hi = lo + rng.int_(0, 20);
  return switch (rng.below(5)) {
    0 || 1 => IntervalSet.of(lo, hi),
    2 => IntervalSet.range(Fin(lo), posInf),
    3 => IntervalSet.range(negInf, Fin(hi)),
    _ => IntervalSet.top(),
  };
}

/// Random domains of `x` and `y`; one case in two is a listed box: `x` listed, its values
/// apart from one another, and `y` one value.
Domains domains(Rng rng) {
  final IntervalSet x, y;
  if (rng.below(2) == 0) {
    final lo = rng.int_(-15, 10);
    final n = rng.int_(1, 8);
    x = IntervalSet.fromPieces([for (var k = 0; k < n; k++) (Fin(lo + 2 * k), Fin(lo + 2 * k))]);
    y = IntervalSet.single(rng.int_(-15, 15));
  } else {
    x = domain(rng);
    y = domain(rng);
  }
  return Domains()
    ..['x'] = x
    ..['y'] = y;
}

/// A random demand on an integer term: up to two intervals.
Demand intDemand(Rng rng) {
  final pieces = <Piece>[];
  for (var i = rng.int_(1, 2); i > 0; i--) {
    final lo = rng.int_(-30, 30);
    final End loEnd = rng.below(5) == 0 ? negInf : Fin(lo);
    final End hiEnd = rng.below(5) == 0 ? posInf : Fin(lo + rng.int_(0, 15));
    pieces.add((loEnd, hiEnd));
  }
  return IntsDemand(IntervalSet.fromPieces(pieces));
}

/// Counts, over the cases run, of exact and enumerated results, so that a test that claims
/// nothing fails.
final class Tally {
  var exact = 0, exactUnenumerated = 0, enumerated = 0, nonempty = 0;

  @override
  String toString() =>
      'exact $exact, exact unenumerated $exactUnenumerated, enumerated $enumerated, '
      'nonempty $nonempty';
}

/// Runs `cases` random terms, tests when `test` holds, each reading through calls when
/// `calls` holds.
Tally run(int seed, int cases, bool test, {bool calls = false}) {
  final rng = Rng(seed);
  final tally = Tally();
  for (var i = 0; i < cases; i++) {
    final (Term t, Demand demand) = test
        ? (boolTerm(rng, 3), BoolDemand(rng.below(2) == 0))
        : (intTerm(rng, 3), intDemand(rng));
    final term = calls ? withFunctions(rng, t) : t;
    final ds = domains(rng);
    final p = preimage(term, ds, demand);
    expect(p.stops, isEmpty, reason: '$term');
    for (final MapEntry(:key, :value) in p.domains.entries) {
      expect(value.isSubset(ds[key]!), isTrue, reason: '$term: $key $value is outside its domain');
    }
    if (check(term, ds, demand, p, window) > 0) tally.nonempty++;
    if (p.exact) tally.exact++;
    if (p.exact && !p.enumerated) tally.exactUnenumerated++;
    if (p.enumerated) tally.enumerated++;
  }
  return tally;
}

/// Counts, over the cases run under `@exact`, of results the search found and of results with
/// a point meeting the demand.
final class ExactTally {
  var searched = 0, nonempty = 0, several = 0;

  @override
  String toString() => 'searched $searched, nonempty $nonempty, several $several';
}

/// Under `@exact`, over random bounded boxes within the window, `x` in a random class one case
/// in three: where the result is enumerated or exact, each input's set, over the members of its
/// class, is the projection of the points that meet the demand, found by running every point;
/// and the result is exact just when every point of its box in the classes meets the demand.
ExactTally runExact(int seed, int cases, bool test) {
  final rng = Rng(seed);
  final tally = ExactTally();
  const names = ['x', 'y'];
  for (var i = 0; i < cases; i++) {
    final (Term term, Demand demand) = test
        ? (boolTerm(rng, 3), BoolDemand(rng.below(2) == 0))
        : (intTerm(rng, 3), intDemand(rng));
    IntervalSet bounded() {
      final lo = rng.int_(-15, 10);
      final hi = lo + rng.int_(0, 20);
      return IntervalSet.of(lo, hi < 15 ? hi : 15);
    }

    final bx = bounded();
    final ds = Domains()
      ..['x'] = bx
      ..['y'] = bounded();
    final classes = <String, Congruence>{};
    if (rng.below(3) == 0) {
      final m = rng.int_(2, 4);
      classes['x'] = Congruence(m, rng.int_(0, m - 1));
    }
    bool member(String k, int v) => classes[k]?.contains(v) ?? true;
    final p = exactPreimage(term, ds, classes, demand);
    for (final MapEntry(:key, :value) in p.domains.entries) {
      expect(value.isSubset(ds[key]!), isTrue, reason: '$term: $key $value is outside its domain');
    }
    final all = points(ds, names, window);
    bool inside(List<int> pt) =>
        [for (var j = 0; j < names.length; j++) member(names[j], pt[j])].every((b) => b);
    final met = [
      for (final pt in all)
        if (inside(pt) && meets(term, names, pt, demand)) pt,
    ];
    for (final pt in met) {
      for (var j = 0; j < names.length; j++) {
        expect(p.domains[names[j]]!.contains(pt[j]), isTrue, reason: '$term: $pt outside $p');
      }
    }
    if (!(p.exact || p.enumerated)) continue;
    tally.searched++;
    if (met.isNotEmpty) tally.nonempty++;
    for (var j = 0; j < names.length; j++) {
      final n = names[j];
      for (var v = window.$1; v <= window.$2; v++) {
        final shown = p.domains[n]!.contains(v) && member(n, v);
        final projected = met.any((pt) => pt[j] == v);
        expect(shown, projected, reason: '$term over $ds $classes: $n = $v, $p');
      }
    }
    final inBox = [
      for (final pt in all)
        if (inside(pt) &&
            [for (var j = 0; j < names.length; j++) p.domains[names[j]]!.contains(pt[j])]
                .every((b) => b))
          pt,
    ];
    final wide = p.domains.values.where(
      (s) => switch (s.bounds) {
        (final a, final b) => a != b,
        null => false,
      },
    );
    if (wide.length > 1) tally.several++;
    final every = inBox.every((pt) => meets(term, names, pt, demand));
    expect(p.exact, every, reason: '$term over $ds: exact $p');
  }
  return tally;
}

void main() {
  test('integer preimages are sound and exact where claimed', () {
    final t = run(25, 250, false);
    expect(
      t.exactUnenumerated >= 60 && t.enumerated >= 5 && t.nonempty >= 100,
      isTrue,
      reason: '$t',
    );
  });

  test('test preimages are sound and exact where claimed', () {
    final t = run(2025, 250, true);
    // The catalog makes most tests exact before a listed box is enumerated.
    expect(
      t.exactUnenumerated >= 40 && t.enumerated >= 2 && t.nonempty >= 100,
      isTrue,
      reason: '$t',
    );
  });

  // The same through calls of functions that call one another, so that summaries are reached
  // from more than one call.
  test('preimages through calls are sound and exact where claimed', () {
    for (final (seed, test) in const [(7, false), (77, true)]) {
      final t = run(seed, 400, test, calls: true);
      expect(t.nonempty, greaterThanOrEqualTo(100), reason: '$t');
    }
  });

  test('a remainder inverts to its first and last periods and one piece between', () {
    // Against every point of the domain: the preimage holds each point whose remainder is
    // demanded, is exact when the domain meets at most two periods, and otherwise, unless a
    // later stage made it exact, has at most `2p + 1` pieces for `p` pieces of remainders.
    final rng = Rng(1585);
    var (exact, necessary) = (0, 0);
    for (var i = 0; i < 1500; i++) {
      var c = 0;
      while (c == 0) {
        c = rng.int_(-9, 9);
      }
      final m = c.abs();
      final rs = <Piece>[];
      for (var k = rng.int_(1, 3); k > 0; k--) {
        final lo = rng.int_(-2, m + 1);
        rs.add((Fin(lo), Fin(lo + rng.int_(0, 2))));
      }
      final z = IntervalSet.fromPieces(rs);
      final lo = rng.int_(-200, 200);
      final span = rng.below(2) == 0 ? 400 : m;
      final hi = lo + rng.int_(0, span);
      final body = PrimApp(Prim.mod, [const Var('i'), lit(c)]);
      final ds = Domains()..['i'] = IntervalSet.of(lo, hi);
      final demand = IntsDemand(z);
      final p = preimage(body, ds, demand);
      check(body, ds, demand, p, (lo - 5, hi + 5));
      if (p.enumerated) continue;
      final rem = z.meet(IntervalSet.of(0, m - 1));
      final pieces = p.domains['i']!.pieces.length;
      expect(
        p.exact || pieces <= 2 * rem.pieces.length + 1,
        isTrue,
        reason: '$c $z over $lo..=$hi: $pieces',
      );
      if (_floor(hi, m) <= _floor(lo, m) + 1) {
        expect(p.exact, isTrue, reason: '$c $z over $lo..=$hi');
        exact++;
      } else {
        necessary++;
      }
    }
    expect(exact > 300 && necessary > 150, isTrue, reason: '$exact exact, $necessary necessary');
  });

  test('exact integer preimages are the projection of the points that meet the demand', () {
    final t = runExact(7, 250, false);
    expect(t.searched >= 200 && t.nonempty >= 100 && t.several >= 20, isTrue, reason: '$t');
  });

  test('exact test preimages are the projection of the points that meet the demand', () {
    final t = runExact(77, 250, true);
    expect(t.searched >= 200 && t.nonempty >= 100 && t.several >= 20, isTrue, reason: '$t');
  });
}

/// `a` divided by `m > 0`, rounded down.
int _floor(int a, int m) => (a - a % m) ~/ m;
