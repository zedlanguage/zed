/// Name resolution at the rule of low complexity (DESIGN.md Part G).
library;

import 'package:test/test.dart';

import 'package:zed/ast.dart';
import 'package:zed/resolve.dart';

import '../../support/scaling.dart' as scaling;
import 'res.dart';

/// Blocks nested `n` deep, each binding a name, the innermost reading the top-level `c` `n`
/// times.
String nested(int n) => [
  'c = 1;\nmain = ',
  for (var i = 0; i < n; i++) '{\ny$i = c;\n',
  '${List.filled(n, 'c').join(' + ')}\n',
  '}\n' * n,
  ';\n',
].join();

/// `k` overloads of `f`, at most 8^5: five parameters, each with no written type or one of the
/// seven types of L1, so no two have the same parameter types.
String overloads(int k) {
  const types = ['', ': int', ': rat', ': f64', ': bool', ': String', ': Lines', ': Files'];
  return [
    for (var i = 0; i < k; i++)
      'f(${[for (var j = 0; j < 5; j++) 'p$j${types[i >> (3 * j) & 7]}'].join(', ')}) = 0;\n',
  ].join();
}

/// The resolution of `text`, timed alone: the statements of each size are built once, by the
/// run that warms the code, so the parse does not hide the resolver's growth.
Resolution timed(Map<int, List<Stmt>> built, int n, String Function(int) text) =>
    resolve(built[n] ??= stmtsOf(text(n)));

void main() {
  final nestedUnits = <int, List<Stmt>>{}, overloadUnits = <int, List<Stmt>>{};

  test('names read inside deeply nested blocks scale', () {
    // A name was looked for in each open scope in turn, innermost first.
    scaling.check('names read in blocks nested n deep', 800, (n) => timed(nestedUnits, n, nested));
    expect(at(nested(3), 'c', 2), ['binding c = 1;']);
  });

  test('declaring many overloads scales', () {
    // Each overload's parameter types were compared with those of every one before it.
    scaling.check('k overloads of one function', 1000, (k) {
      expect(timed(overloadUnits, k, overloads).binders, hasLength(6 * k));
    });
    expect(errors('f(x: int) = x;\nf(y: int) = 1;\ng = 1;\ng(x) = x;\n'), [
      '`f` is already declared in this scope with these parameter types '
          '[f(y: int) = 1;]; the first `f` with these parameter types [f(x: int) = x;]',
      '`g` is already bound in this scope [g(x) = x;]; the first binding of `g` [g = 1;]',
    ]);
  });
}
