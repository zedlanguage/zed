/// Dup/drop fusion: a `match` that owns its scrutinee releases it at the arm's entry, keeping
/// the binders the arm uses; a unique scrutinee's cell is freed and its kept parts move out
/// without a count write.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' show Mode;

import 'machine.dart';

Term first(Term scrutinee) => Match(scrutinee, [
  (const TupleP([BindP('x'), WildP()]), var_('x')),
]);

/// The count writes of [t] with fusion and without, after the same value.
(int, int, String) writes(Term t) {
  final (g, p) = planned(t, true);
  final (v, fused) = run(g, p);
  final (g2, p2) = planned(t, false);
  final (w, unfused) = run(g2, p2);
  expect(v, w);
  expect((fused.frees, fused.allocations), (unfused.frees, unfused.allocations));
  return (fused.writes, unfused.writes, v);
}

void main() {
  test('a fresh pair destructured costs one write fused and four unfused', () {
    // Fused: the pair's cell is freed and `x` moves out of it; only "cd" is decremented.
    // Unfused: a dup of `x`, then the pair's drop and its two parts'. The result's own drop
    // after the run adds one write to each.
    final t = first(prim(Prim.tuple, [cat('a', 'b'), cat('c', 'd')]));
    final (_, p) = planned(t, true);
    expect(p.at('r').nodes[3].modes, [Mode.owned]);
    expect(p.at('r.3/0').args, [Mode.owned]);
    expect(writes(t), (1 + 1, 4 + 1, '"ab"'));
  });

  test('a shared scrutinee dups what it keeps', () {
    // `t = (p, p)` holds the pair twice, so the match's pair is shared: the arm's entry dups
    // `x` and decrements the pair, fused or not, and nothing is freed early.
    final pair = prim(Prim.tuple, [cat('a', 'b'), cat('c', 'd')]);
    final get = prim(Prim.tupleGet, [var_('t'), lit(0)]);
    final t = let_(
      'p',
      pair,
      let_(
        't',
        prim(Prim.tuple, [var_('p'), var_('p')]),
        prim(Prim.tuple, [first(get), var_('t')]),
      ),
    );
    final (f, u, v) = writes(t);
    expect(v, '("ab", (("ab", "cd"), ("ab", "cd")))');
    expect(f, u);
  });

  test('a struct binder is found by field name', () {
    // `#point(x: "a" ++ "b", y: "c" ++ "d")` matched by `#point(y: v)`: the payload is
    // sorted by field name, and the arm keeps the cell of `y`.
    final names = Tuple([Str('y'), Str('x')]);
    final atom = prim(Prim.atom, [lit('point'), lit(names), cat('c', 'd'), cat('a', 'b')]);
    const p = FieldsP('point', [('y', BindP('v'))]);
    final t = Match(atom, [(p, var_('v'))]);
    expect(writes(t), (1 + 1, 4 + 1, '"cd"'));
  });
}
