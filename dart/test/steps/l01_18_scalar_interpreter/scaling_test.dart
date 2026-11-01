/// The scalar tier at the rule of low complexity (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/scaling.dart' as scaling;
import '../l01_16_elaboration/elab.dart';

/// The term of `x = <expr(n)>;` under the prelude, built once per size; its value, printed.
String Function(int) run(String Function(int) expr) {
  final terms = <int, Term>{};
  return (n) {
    final t = terms[n] ??= withPrelude(elab('x = ${expr(n)};\n').close(const Var('x')));
    return '${eval(t)}';
  };
}

/// The numbers `0` to `n - 1`, written as a tuple.
String tuple(int n) => '(${[for (var i = 0; i < n; i++) '$i'].join(', ')})';

void main() {
  test('`sum` and `String` of a long tuple scale', () {
    final sum = run((n) => 'sum(${tuple(n)})');
    scaling.check('`sum` of n numbers', 20000, sum);
    expect(sum(4), '6');
    final shown = run((n) => 'len(String(${tuple(n)}))');
    scaling.check('`String` of n numbers', 20000, shown);
    expect(shown(3), '9');
  });

  test('the string words on a long string scale', () {
    final words = run((n) => 'len(trim(upper(lower(" ${'Ab' * n} "))))');
    scaling.check('the string words on 2n letters', 100000, words);
    expect(words(2), '4');
  });

  test('a chain of n failures merging scales', () {
    // Each `+` merged the failures so far with one more by copying them into a new set. The
    // chain is a kernel term, so that only the evaluator is timed.
    Term chain(int n) =>
        [for (var i = 1; i < n; i++) i]
            .fold(const Lit(Atom('e0')), (t, i) => PrimApp(Prim.add, [t, Lit(Atom('e$i'))]));
    String merged(int n) => '${eval(chain(n))}';
    scaling.check('n failures merged by a chain of `+`', 1000, merged);
    expect(merged(3), '#errs({#e0, #e1, #e2})');
  });
}
