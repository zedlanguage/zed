/// The natural order (DESIGN.md sec:keys): kinds in a fixed order, numbers by value across
/// `int`, `rat` and floats, an `int` before a `rat` before a float of equal value.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../l01_16_elaboration/elab.dart';

/// The values of the definitions `names` of `src`.
List<Value> values(String src, List<String> names) {
  final u = elab(src);
  return [for (final n in names) Evaluator(World()).run(withPrelude(u.get(n)!))];
}

void main() {
  test('numbers order by value across kinds', () {
    const src =
        'a = 1;\nb = 1r;\nc = 1.0;\nd = 3r / 2r;\ne = 1.25;\nf = 2;\n'
        'g = -100000000000000000000;\nh = 100000000000000000000;\ni = 0.0 / 0.0;\n'
        'j = 1.0 / 0.0;\nk = -1.0 / 0.0;\n';
    final vs = values(src, 'abcdefghijk'.split(''))..sort();
    expect(
      [for (final v in vs) '$v'],
      [
        '-inf',
        '-100000000000000000000',
        '1',
        '1r',
        '1.0',
        '1.25',
        '3r/2r',
        '2',
        '100000000000000000000',
        'inf',
        'nan',
      ],
    );
  });

  test('kinds order atoms, bools, numbers, strings, tuples', () {
    const src =
        'a = (1, 2);\nb = "apple";\nc = 7;\nd = true;\ne = #none;\nf = (1, 2, 3);\n'
        'g = #err(code: 2);\nh = #err(1);\n';
    final vs = values(src, 'abcdefgh'.split(''))..sort();
    expect(
      [for (final v in vs) '$v'],
      ['#err(1)', '#err(code: 2)', '#none', 'true', '7', '"apple"', '(1, 2)', '(1, 2, 3)'],
    );
  });

  test('equal rationals are one value, in a hash set too', () {
    final vs = values('a = 1r / 3r;\nb = 2r / 6r;\n', ['a', 'b']);
    expect(vs[0], vs[1]);
    expect(vs.toSet(), hasLength(1));
  });

  test('a family keyed by mixed numbers visits them by value', () {
    const keys = ['10', '2r', '1.5', '100000000000000000000', '-3'];
    final src = [for (var i = 0; i < keys.length; i++) 'k$i = ${keys[i]};\n'].join();
    final vs = values(src, [for (var i = 0; i < keys.length; i++) 'k$i']);
    final f = Family.of([for (final k in vs) (k, const Bool(true))]);
    expect([for (final k in f.keys) '$k'], ['-3', '1.5', '2r', '10', '100000000000000000000']);
  });
}
