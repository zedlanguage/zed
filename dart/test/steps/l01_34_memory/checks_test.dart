/// The machine's checks fail on a wrong plan: a missed drop, an extra dup, a missing dup and
/// a borrowed argument given to a parameter that consumes it are each reported, with the node
/// and the edge.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' show Mode, ZirError;

import 'machine.dart';

Term readsTwice() => let_(
  's',
  cat('ab', 'c'),
  prim(Prim.tuple, [
    prim(Prim.len, [var_('s')]),
    prim(Prim.upper, [var_('s')]),
  ]),
);

Matcher fails(Matcher message) =>
    throwsA(isA<ZirError>().having((e) => e.message, 'message', message));

void main() {
  test('a missed drop is a leak', () {
    final (g, p) = planned(readsTwice(), true);
    p.at('r').nodes[2].drops.clear();
    expect(
      () => run(g, p),
      fails(equals('memory: r.2: edge 0.0 is still owned after its last use, a leak')),
    );
  });

  test('an extra dup is a count above its references', () {
    final (g, p) = planned(readsTwice(), true);
    p.at('r').nodes[1].dups.add(0);
    expect(
      () => run(g, p),
      fails(startsWith('memory: at node r.1, cell 0 has count 2 and 1 reference')),
    );
  });

  test('a missing dup consumes an edge twice', () {
    final t = let_('s', cat('ab', 'c'), prim(Prim.tuple, [var_('s'), var_('s')]));
    final (g, p) = planned(t, true);
    p.at('r').nodes[1].dups.clear();
    expect(
      () => run(g, p),
      fails(
        equals(
          'memory: r.1: input 1, taken owned consumes edge 0.0, already consumed or past its '
          'last use',
        ),
      ),
    );
  });

  test('a borrowed argument to a consuming parameter is refused', () {
    final g = lam(['x'], prim(Prim.tuple, [var_('x'), lit(1)]));
    final t = let_('g', g, app(var_('g'), [cat('a', 'b')]));
    final (graph, p) = planned(t, true);
    p.at('r').nodes[2].modes[1] = Mode.borrowed;
    expect(
      () => run(graph, p),
      fails(equals('memory: r.2: argument 0 is passed borrowed to `r.0/0`, which consumes it')),
    );
  });
}
