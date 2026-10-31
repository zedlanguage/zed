/// Provenance at the rule of low complexity (DESIGN.md Part G). A fact's address holds the
/// call sites and the keypath the run is inside, which a recursion of depth `n` makes `n`
/// long; the addresses share them, so recording the `O(n)` facts of the recursion costs
/// `O(n)`, not `O(n²)`.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/kernel.dart';
import '../../support/scaling.dart' as scaling;
import 'provenance.dart';

/// `let f = (f, n) -> if n == 0 then 0 else f(f, n - 1) + 1 in f(f, depth)`: a recursion of
/// `depth` nested calls.
Term countdown(int depth) {
  final f = lam(
    ['f', 'n'],
    if_(
      eq(var_('n'), lit(0)),
      lit(0),
      add(app(var_('f'), [var_('f'), sub(var_('n'), lit(1))]), lit(1)),
    ),
  );
  return app(f, [f, lit(depth)]);
}

/// The balanced tree of `op` over the leaves `leaf(lo..hi)`.
Term tree(int lo, int hi, Term Function(Term, Term) op, Term Function(int) leaf) {
  if (hi - lo == 1) return leaf(lo);
  final mid = (lo + hi) ~/ 2;
  return op(tree(lo, mid, op, leaf), tree(mid, hi, op, leaf));
}

void main() {
  test('recording a deep recursion scales', () {
    // Each fact copied the call sites it was inside: the facts of a recursion of depth `n`
    // held `n²/2` of them.
    scaling.check('the provenance of a recursion, by depth', 1000, (n) {
      final (v, p) = trace(countdown(n));
      expect(v, Int(n));
      expect(p.facts.length, greaterThan(5 * n));
    });
  });

  test('the facts of a recursion are at their call sites', () {
    // The fact of `n == 0` at depth `d` is `d + 1` call sites deep: the outer call, then the
    // recursive call site `d` times; no two facts share an address.
    final (_, p) = trace(countdown(30));
    unique(p);
    final depths = {for (final f in at(p, '(n == 0)')) f.address.node.length}.toList()..sort();
    expect(depths, hasLength(31), reason: '$depths');
    expect(depths.last - depths.first, 30, reason: '$depths');
  });

  test('the term of every fact scales', () {
    // The term at a node is found by walking the term in preorder to its position, so
    // reading the term of each of the `O(n)` facts of an `n`-node term one at a time took
    // `O(n²)` steps. `terms()` reads them all in one walk.
    scaling.check('the term at each fact, by term size', 1000, (n) {
      final (v, p) = trace(tree(0, n, add, (_) => lit(1)));
      expect(v, Int(n));
      final terms = p.terms();
      expect(p.facts.where((f) => terms[f.address.node.position] is PrimApp), hasLength(n - 1));
    });
  });

  test('the origins of a failure with many members scale', () {
    // The product of `n` distinct loose atoms: its `#errs` has `n` members, each first
    // appearing at its literal. Each member's search tested every input fact by walking its
    // value, an `#errs` of up to `n` members: `O(n² log n)` steps.
    scaling.check('the origins of an n-member failure, by n', 64, (n) {
      final (v, p) = trace(tree(0, n, mul, (i) => atom('e$i')));
      expect(v.errs?.length, n, reason: '$v');
      final o = p.origins(p.result);
      expect(o, hasLength(n));
      expect(o.every((j) => p.term(p.facts[j].address.node) is Lit), isTrue);
    });
  });
}
