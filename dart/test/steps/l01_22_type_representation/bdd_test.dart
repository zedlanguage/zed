/// Step L1.22: the paths of a tuple or morphism part, as emptiness reads them, against the
/// part evaluated at each assignment of its atoms, for parts kept as diagrams and as
/// expressions, shared subexpressions among them.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/src/kernel/types.dart';

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

/// Whether an expression in `p` is an operand of two connectives.
bool shares(Part<Components> p) {
  final seen = Set<Expr<Components>>.identity();
  bool go(Part<Components> p) {
    if (p is! Expr<Components>) return false;
    if (!seen.add(p)) return true;
    return go(p.a) || (p.b != null && go(p.b!));
  }

  return go(p);
}

void main() {
  test('the paths of a part are its assignments', () {
    // Each set of the six atoms is one assignment. It is outside the part exactly when every
    // path excludes it: takes an atom not in the set, or refuses one in it. That test holds of
    // a path whenever it holds of a path with fewer atoms, as `paths` asks.
    final atoms = [for (var i = 0; i < 6; i++) atom(i)];
    final s = Seed(7);
    var (exprs, shared, found) = (0, 0, 0);
    for (var n = 0; n < 3000; n++) {
      final p = s.state % 2 == 0 ? random(s, 6) : randomExpr(s, 5, []);
      if (p is Expr) exprs++;
      if (shares(p)) shared++;
      for (var set = 0; set < 64; set++) {
        bool holds(Components t) =>
            [for (var i = 0; i < 6; i++) i].any((i) => set & (1 << i) != 0 && t == atoms[i]);
        final out = p.paths((pos, neg) => pos.any((a) => !holds(a)) || neg.any(holds));
        if (out == p.eval(holds)) fail('${set.toRadixString(2)}: paths and eval disagree');
        if (!out) found++;
      }
    }
    expect(exprs > 500 && shared > 200 && found > 10000, isTrue, reason: '$exprs $shared $found');
  });
}
