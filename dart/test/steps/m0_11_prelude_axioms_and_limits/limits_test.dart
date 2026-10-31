/// The minimum resource limits: an evaluation within them is accepted by the reference
/// evaluator with its default settings. Each program is sized to its limit, and one step or one
/// call more is shown to cross it, so the sizes are measured and not estimated.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

/// `f(f, arg)`: the self-application by which these programs recurse.
Term selfApply(List<String> params, Term body, List<Term> args) {
  final f = lam(params, body);
  return app(f, [f, ...args]);
}

/// Counts the leaves of a balanced split of `n` items, as a merge sort recurses:
/// `count(n) = if n <= 1 { 1 } else { count(n div 2) + count(n - n div 2) }`, which makes
/// `2n - 1` calls, each one step.
Term countLeaves(int n) {
  Term half() => prim(Prim.intDiv, [var_('n'), lit(2)]);
  Term me(Term arg) => app(var_('me'), [var_('me'), arg]);
  final body = if_(
    prim(Prim.le, [var_('n'), lit(1)]),
    lit(1),
    prim(Prim.add, [
      me(half()),
      me(prim(Prim.sub, [var_('n'), half()])),
    ]),
  );
  return selfApply(['me', 'n'], body, [lit(n)]);
}

Value withFuel(int fuel, Term t) => Evaluator(World(), fuel: fuel).run(t);

/// A chain of `n` calls, each nested in the one before:
/// `depth(k) = if k == 1 { 1 } else { 1 + depth(k - 1) }`.
Term nested(int n) => selfApply(
  ['me', 'k'],
  if_(
    prim(Prim.eq, [var_('k'), lit(1)]),
    lit(1),
    prim(Prim.add, [
      lit(1),
      app(var_('me'), [
        var_('me'),
        prim(Prim.sub, [var_('k'), lit(1)]),
      ]),
    ]),
  ),
  [lit(n)],
);

void main() {
  test('ten million steps are accepted', () {
    // 5,000,000 items make 9,999,999 calls; 5,000,001 make 10,000,001.
    expect(withFuel(minSteps, countLeaves(5000000)), const Int(5000000));
    expect(() => withFuel(minSteps, countLeaves(5000001)), throwsA(isA<OutOfFuelError>()));
  });

  test('twenty thousand nested calls are accepted', () {
    expect(maxDepth, greaterThanOrEqualTo(minNestedCalls));
    expect(eval(nested(minNestedCalls)), const Int(minNestedCalls));
    expect(() => eval(nested(minNestedCalls + 1)), throwsA(isA<TooDeepError>()));
  });

  test('a value of almost a gibibyte is accepted', () {
    // A string doubled 29 times reaches 512 MiB; with the halves the recursion still holds,
    // the strings alive at the end total 2^30 - 1 bytes.
    final body = if_(
      prim(Prim.eq, [var_('k'), lit(0)]),
      var_('s'),
      app(var_('me'), [
        var_('me'),
        prim(Prim.concat, [var_('s'), var_('s')]),
        prim(Prim.sub, [var_('k'), lit(1)]),
      ]),
    );
    final out = eval(selfApply(['me', 's', 'k'], body, [lit('z'), lit(29)]));
    // A join is kept unwritten until read; reading the text writes all of it out.
    expect((out as Str).text.text.length, minMemory ~/ 2);
    var sum = 1;
    for (var k = 1; k <= 29; k++) {
      sum += 1 << k;
    }
    expect(sum, minMemory - 1);
  });
}
