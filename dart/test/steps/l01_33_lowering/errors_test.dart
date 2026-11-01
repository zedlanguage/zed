/// What the lowering refuses, and why.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' hide print;

import '../../support/kernel.dart' show fold;
import 'lowering.dart';

/// The message `run` throws.
String refusal(void Function() run) {
  try {
    run();
  } on ZirError catch (e) {
    return e.message;
  }
  fail('no error');
}

void main() {
  test('a port inside a fold is refused', () {
    final xs = lit(Family.set([const Int(1), const Int(2)]));
    final leak = fold(xs, lam(['a', 'b'], push('stdout', var_('a'))));
    expect(
      refusal(() => lower(leak)),
      'port `stdout` is used inside a function region, and a state edge enters only a match '
      'or port region or the region of a `let`-bound lambda (step L1.31): a port is read or '
      'pushed outside loops and families, and a function that uses one is bound by `let` '
      'and called by its name',
    );
  });

  test('a function that pushes is only called', () {
    Term say() => lam(['m'], push('stdout', var_('m')));
    final asValue = let_('say', say(), prim(Prim.tuple, [var_('say')]));
    expect(
      refusal(() => lower(asValue)),
      'a function of 1 parameter that uses the ports `stdout` is used as a value: a call '
      "threads the states of those ports, and only a call by the function's name knows them, "
      'so such a function is only called',
    );
    final two = let_('say', say(), App(var_('say'), [lit('a'), lit('b')]));
    expect(
      refusal(() => lower(two)),
      'a function of 1 parameter that uses a port is called with 2 arguments',
    );
  });

  test('a name bound inside a function is not the function of that name outside', () {
    // `h` calls its own `say`, which pushes nothing, so `h` uses no port and is a value; with
    // the outer `say` called instead, `h` uses `stdout` and is only called.
    Term h(bool inner) {
      final call = App(var_('say'), [var_('v')]);
      final body = inner ? let_('say', lam(['u'], var_('u')), call) : call;
      return let_(
        'say',
        lam(['m'], push('stdout', var_('m'))),
        let_('h', lam(['v'], body), prim(Prim.tuple, [var_('h')])),
      );
    }

    lower(h(true));
    expect(
      refusal(() => lower(h(false))),
      startsWith('a function of 1 parameter that uses the ports `stdout` is used as a value'),
    );
  });

  test('names and primitives are checked', () {
    expect(
      refusal(() => lower(var_('ghost'))),
      '`ghost` is not bound, and a term lowers only when every name it reads is bound in it '
      'or is a prelude word',
    );
    final tuple = let_('t', const PrimFn(Prim.tuple), var_('t'));
    expect(
      refusal(() => lower(tuple)),
      endsWith(
        'takes any number of arguments, so with no inputs its node is a call, not the '
        'function; call it instead of passing it as a value',
      ),
    );
    final neg = prim(Prim.neg, [lit(1), lit(2)]);
    expect(refusal(() => lower(neg)), endsWith('takes 1 argument and is given 2'));
  });

  test('raise wants one value and a state per port', () {
    final g = Region(RegionKind.function, [], [], [const Const(Int(1)), const Const(Int(2))]);
    expect(
      refusal(() => raise(g)),
      "the root region has 0 arguments and 2 results, and a term's root has one value and "
      'a state result for each state argument',
    );
  });
}
