/// Atom payloads at the rule of low complexity (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/elab.dart';
import 'package:zed/kernel.dart';
import 'package:zed/resolve.dart';

import '../../support/scaling.dart' as scaling;
import '../l01_16_elaboration/elab.dart';

/// An atom with `n` named fields, and an `else` that matches it naming them all.
String fields(int n) {
  final fs = [for (var i = 0; i < n; i++) 'f$i'];
  return 'e = #big(${[for (final f in fs) '$f: 1'].join(', ')});\n'
      'x = e else #big(${[for (final f in fs) '$f:'].join(', ')}) -> f0;\n';
}

void main() {
  final built = <int, (List<Stmt>, Resolution)>{};

  /// The elaboration of [fields] of size `n`, timed alone.
  Unit elaborated(int n) {
    final (stmts, res) = built[n] ??= () {
      final s = stmtsOf(fields(n));
      return (s, resolve(s));
    }();
    return elaborate(stmts, res);
  }

  test('an atom and a pattern with many named fields scale', () {
    // Each field of a pattern was looked for among those before it, to report a repeat.
    scaling.check('n named fields', 2000, (n) => elaborated(n));
    expect(value(fields(3), 'x'), '1');
  });

  test('matching many named fields scales', () {
    // Each field of the pattern was looked for in the atom's payload from its start.
    final terms = <int, Term>{};
    scaling.check('matching n named fields', 2000, (n) {
      final u = terms[n] ??= withPrelude(elaborated(n).close(Var('x')));
      expect('${Evaluator(World()).run(u)}', '1');
    });
  });
}
