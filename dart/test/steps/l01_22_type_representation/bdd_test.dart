/// Step L1.22: the three-valued operations emptiness decides a tuple or morphism part by,
/// against the part evaluated at each assignment of its atoms, for parts kept as diagrams and
/// as expressions, shared subexpressions among them.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/src/kernel/types.dart';

import '../../support/scaling.dart';

/// The tuple type of one integer, an atom independent of the others.
Components atom(int i) => Components([Type.lit(Int(i))!]);

/// A linear congruential generator, its high bits the pick.
final class Seed {
  int state;
  Seed(this.state);

  int next() {
    state = state * 6364136223846793005 + 1442695040888963407;
    return state >>> 33;
  }
}

Part<Components> random(Seed s, int depth) {
  final pick = s.next();
  if (depth == 0 || pick % 5 == 0) return Part.literal(atom(pick % 6));
  final (a, b) = (random(s, depth - 1), random(s, depth - 1));
  return switch (pick % 3) {
    0 => a.zip(b, true),
    1 => a.zip(b, false),
    _ => ~a,
  };
}

/// The part built from `random`'s connectives as expressions, so that every form is met; an
/// operand is at times one built before, kept in `pool`, so that expressions are shared.
Part<Components> randomExpr(Seed s, int depth, List<Part<Components>> pool) {
  final pick = s.next();
  if (pool.isNotEmpty && pick % 7 == 3) return pool[(pick ~/ 7) % pool.length];
  if (depth == 0 || pick % 5 == 0) return random(s, 2);
  final (a, b) = (randomExpr(s, depth - 1, pool), randomExpr(s, depth - 1, pool));
  final p = switch (pick % 3) {
    0 => Expr(ExprOp.or, a, b),
    1 => Expr(ExprOp.and, a, b),
    _ => Expr(ExprOp.not, a),
  };
  pool.add(p);
  return p;
}

void main() {
  test('three-valued operations keep the assignments', () {
    // Each set of the six atoms is one assignment, and a partial assignment fixes the atoms of
    // `known` to their membership in `fixed`. A three-valued value is the value of every
    // assignment that agrees with it; restricting keeps the value of every assignment agreeing
    // with what it fixes; settling keeps every assignment in the part, and makes it empty only
    // when the part is; an atom forced taken is in every assignment in the part, and one forced
    // refused in none.
    final atoms = [for (var i = 0; i < 6; i++) atom(i)];
    int? index(Components t) {
      for (var i = 0; i < 6; i++) {
        if (t == atoms[i]) return i;
      }
      return null;
    }

    bool Function(Components) holds(int set) => (t) {
      final i = index(t);
      return i != null && set & (1 << i) != 0;
    };
    final s = Seed(7);
    var (exprs, decided, forced, settled) = (0, 0, 0, 0);
    for (var k = 0; k < 3000; k++) {
      final p = s.state % 2 == 0 ? random(s, 6) : randomExpr(s, 5, []);
      if (p is Expr) exprs++;
      final inside = [
        for (var set = 0; set < 64; set++)
          if (p.eval(holds(set))) set,
      ];
      final (known, fixed) = (k % 64, (k ~/ 64) % 64);
      bool? fix(Components t) {
        final i = index(t);
        return i != null && known & (1 << i) != 0 ? fixed & (1 << i) != 0 : null;
      }

      bool agree(int set) => (set ^ fixed) & known == 0;
      if (p.eval3(fix) case final v?) {
        decided++;
        for (var set = 0; set < 64; set++) {
          if (agree(set) && p.eval(holds(set)) != v) fail('$p: eval3 at ${set.toRadixString(2)}');
        }
      }
      final r = p.restrict(fix);
      final t = p.settle();
      if (inside.isEmpty && t.leaf == false) settled++;
      for (var set = 0; set < 64; set++) {
        final v = p.eval(holds(set));
        if (agree(set) && r.eval(holds(set)) != v) {
          fail('$p: restrict at ${set.toRadixString(2)}');
        }
        if (v && !t.eval(holds(set))) fail('$p: settle at ${set.toRadixString(2)}');
      }
      final (taken, refused) = p.forced();
      forced += taken.length + refused.length;
      for (final a in taken) {
        final i = index(a)!;
        if (!inside.every((s) => s & (1 << i) != 0)) fail('$p takes $i');
      }
      for (final a in refused) {
        final i = index(a)!;
        if (!inside.every((s) => s & (1 << i) == 0)) fail('$p refuses $i');
      }
      // On a diagram every atom in all assignments, or in none, is found.
      if (p is Bdd<Components> && inside.isNotEmpty) {
        for (var i = 0; i < 6; i++) {
          bool at(int s) => s & (1 << i) != 0;
          expect(taken.contains(atoms[i]), inside.every(at), reason: '$p at $i');
          expect(refused.contains(atoms[i]), !inside.any(at), reason: '$p at $i');
        }
      }
    }
    expect(
      exprs > 500 && decided > 300 && forced > 1000 && settled > 100,
      isTrue,
      reason: '$exprs $decided $forced $settled',
    );
  });

  test('the forced atoms of a long chain scale', () {
    // `w & ((x_1 & … & x_m) | z)`: `true` is reached past `z` from every `x_k`, so no branch
    // below `w` is on every path. `w` is the first atom in the order and `z` the last, and
    // the conjunction is built by halves, since a union or intersection counts the nodes of
    // its result.
    (Part<Components>, Components) chain(int m) {
      final xs = [for (var i = 0; i < m + 2; i++) atom(i)]..sort((a, b) => a.compareTo(b));
      Part<Components> all(int from, int to) => to - from == 1
          ? Part.literal(xs[from])
          : all(from, (from + to) ~/ 2).zip(all((from + to) ~/ 2, to), false);
      final body = all(1, m + 1).zip(Part.literal(xs[m + 1]), true);
      return (Part.literal(xs[0]).zip(body, false), xs[0]);
    }

    const n = 1 << 12;
    final built = {
      for (final m in [n, factor * n]) m: chain(m),
    };
    check('the forced atoms of a chain, by its length', n, (m) {
      final (p, w) = built[m]!;
      expect(p, isA<Bdd<Components>>());
      final (taken, refused) = p.forced();
      expect(taken, [w]);
      expect(refused, isEmpty);
    });
  });

  test('comparing equal expressions built apart scales', () {
    // `x_{k+1} = x_k & !x_k`, built twice: both operands of each level lead to the level
    // below, so comparing operand by operand met the bottom `2^depth` times.
    Part<Components> build(int depth) {
      Part<Components> x = Part.literal(atom(0));
      for (var k = 0; k < depth; k++) {
        x = Expr(ExprOp.and, x, ~x);
      }
      return x;
    }

    const n = 1 << 12;
    final built = {
      for (final m in [n, factor * n]) m: (build(m), build(m)),
    };
    check('comparing equal expressions built apart, by depth', n, (m) {
      final (a, b) = built[m]!;
      expect(identical(a, b), isFalse);
      expect(a.compareTo(b), 0);
    });
  });
}
