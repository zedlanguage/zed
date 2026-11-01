/// Static last-use drops and precise counts: which values are cells, a value used once is
/// never counted, a borrowed value is dropped at its last use, and each owned use but the
/// last gets a dup.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' show Mode;

import 'machine.dart';

void main() {
  test('a value used once is never counted', () {
    // Two fresh strings moved into a fresh pair: three cells, no dup and no drop in the
    // program; the three decrements are the result's, dropped after the run.
    final t = prim(Prim.tuple, [cat('a', 'b'), cat('c', 'd')]);
    final (v, s, p) = machine(t);
    expect(v, '("ab", "cd")');
    final r = p.at('r');
    expect(r.nodes.every((n) => n.dups.isEmpty && n.drops.isEmpty), isTrue);
    expect(r.nodes[2].modes, [Mode.owned, Mode.owned]);
    expect((s.increments, s.decrements, s.allocations, s.frees), (0, 3, 3, 3));
  });

  test('a borrowed value is dropped at its last use', () {
    // `s = "ab" ++ "c"; (len(s), upper(s))`: both reads borrow `s`, and the second drops it,
    // so `s` is freed before the pair is made: at most two cells are ever live.
    final t = let_(
      's',
      cat('ab', 'c'),
      prim(Prim.tuple, [
        prim(Prim.len, [var_('s')]),
        prim(Prim.upper, [var_('s')]),
      ]),
    );
    final (v, s, p) = machine(t);
    expect(v, '(3, "ABC")');
    final r = p.at('r');
    expect(r.nodes[1].drops, isEmpty);
    expect(r.nodes[2].drops.map(show), ['0.0']);
    expect((s.increments, s.peak), (0, 2));
  });

  test('each owned use but the last gets a dup', () {
    // `(s, s)`: the pair holds `s` twice, so `s` gets one dup and its cell is shared.
    final t = let_('s', cat('ab', 'c'), prim(Prim.tuple, [var_('s'), var_('s')]));
    final (v, s, p) = machine(t);
    expect(v, '("abc", "abc")');
    expect(p.at('r').nodes[1].dups, [0]);
    expect((s.increments, s.shared, s.allocations), (1, 1, 2));
  });

  test('strings, tuples and big integers are cells and scalars are not', () {
    // A tuple, a big integer and a string are cells; an integer, a float and a boolean are
    // unboxed; a constant string is static. So the tuple below allocates three cells.
    final big = prim(Prim.pow, [lit(2), lit(70)]);
    final t = prim(Prim.tuple, [
      big,
      lit(1),
      prim(Prim.castF64, [lit(2)]),
      lit(true),
      cat('s', 't'),
      lit('static'),
    ]);
    final (v, s, _) = machine(t);
    expect(v, '(1180591620717411303424, 1, 2.0, true, "st", "static")');
    expect((s.allocations, s.frees), (3, 3));
  });

  test('an arm that ignores an owned capture drops it on entry', () {
    // `if len(s) > 5 { (s, 1) } else { 0 }`: the first arm consumes `s`, so the `if` passes it
    // owned; the second arm, which runs, does not use it and drops it on entry.
    final c = prim(Prim.gt, [
      prim(Prim.len, [var_('s')]),
      lit(5),
    ]);
    final t = let_('s', cat('ab', 'c'), if_(c, prim(Prim.tuple, [var_('s'), lit(1)]), lit(0)));
    final (v, s, p) = machine(t);
    expect(v, '0');
    expect(p.at('r.3/1').entryDrops, [0]);
    expect((s.allocations, s.frees, s.increments), (1, 1, 0));
  });

  test('a borrowed value returned gets a dup', () {
    // `f = x -> s` returns its capture, which the closure holds: the result is a dup of it.
    final f = lam(['x'], var_('s'));
    final call = app(var_('f'), [lit(0)]);
    final t = let_('s', cat('ab', 'c'), let_('f', f, call));
    final (v, s, p) = machine(t);
    expect(v, '"abc"');
    expect(p.at('r.1/0').resultDups, [0]);
    expect(s.increments, 1);
  });
}
