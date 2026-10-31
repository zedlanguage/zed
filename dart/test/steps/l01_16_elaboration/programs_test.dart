/// Blocks, operators, strings, `if`, `else`, `?.`, lambdas, ports and `test` tables.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import 'elab.dart';

void main() {
  test('statements run in dependency order, not written order', () {
    const src = 'net = gross - fee;\nfee = gross div 20;\ngross = 1200;\n';
    expect(value(src, 'net'), '1140');
    expect([for (final d in elab(src).defs) d.name], ['gross', 'fee', 'net']);
  });

  test('a block is its lets over its export', () {
    const src = 'area = { w = 3; h = w + 1; w * h };\n';
    expect(value(src, 'area'), '12');
    expect(term(src, 'area'), '{ w = 3; h = (w + 1); (w * h) }');
  });

  test('return of several values is a tuple, and destructuring reads it', () {
    const src =
        'bounds(positional xs) {\n  return xs[0], xs[2];\n}\n'
        'lo, hi = bounds((3, 5, 9));\nwidth = hi - lo;\n';
    expect(value(src, 'width'), '6');
    // `_` binds nothing; the tuple is still read by position.
    expect(value('_, mid, _ = (1, 2, 3);\ntwice = mid * 2;\n', 'twice'), '4');
  });

  test('a block without an export is the empty tuple', () {
    const src = 'main() -> (stdout: Lines) {\n  stdout <- "ready";\n}\nrun = main();\n';
    final ev = Evaluator(World().output('stdout'));
    expect('${ev.run(withPrelude(elab(src).get('run')!))}', '()');
    expect('${ev.world.log('stdout')[0]}', '"ready"');
    expect(term(src, 'main'), r'() -> { $1 = port.push(stdout, "ready"); () }');
  });

  test('arithmetic, comparison and power', () {
    const src =
        'a = 2 ** 3 ** 2;\nb = -7 div 2;\nc = -7 mod 2;\nd = 1.5 * 4.0;\n'
        'e = 3 <= 3;\nf = !(2 > 3);\ng = 10.0 / 4.0;\n';
    expect(value(src, 'a'), '512', reason: '`**` is right-associative');
    expect(value(src, 'b'), '-4', reason: 'Euclidean division');
    expect(value(src, 'c'), '1', reason: 'Euclidean modulus');
    expect(value(src, 'd'), '6.0');
    expect(value(src, 'e'), 'true');
    expect(value(src, 'f'), 'true');
    expect(value(src, 'g'), '2.5');
    expect(term(src, 'a'), '(2 ** (3 ** 2))');
  });

  test('and and or are if forms, so they short-circuit', () {
    // The right operand would be the atom `#divByZero` if it were evaluated.
    const src = 'ok = true || 1 div 0 == 0;\nno = false && 1 div 0 == 0;\n';
    expect(value(src, 'ok'), 'true');
    expect(value(src, 'no'), 'false');
    expect(term(src, 'ok'), 'if true { true } else { ((1 div 0) == 0) }');
  });

  test('concatenation and interpolation', () {
    const src = 'who = "Ada";\nhello = "hello, " ++ who;\nline = "\${hello}! (\${who})";\n';
    expect(value(src, 'hello'), '"hello, Ada"');
    expect(value(src, 'line'), '"hello, Ada! (Ada)"');
    expect(term(src, 'line'), '(((String(hello) ++ "! (") ++ String(who)) ++ ")")');
    // A hole of any type goes through `String`, which the interpreter binds.
    expect(term('n = 3;\nmsg = "n = \${n + 1}";\n', 'msg'), '("n = " ++ String((n + 1)))');
  });

  test('if chains', () {
    const src =
        'grade(positional score) = if score >= 90 { #a } else if score >= 80 { #b } '
        'else { #c };\nx = grade(85);\ny = grade(95);\nz = grade(10);\n';
    expect(value(src, 'x'), '#b');
    expect(value(src, 'y'), '#a');
    expect(value(src, 'z'), '#c');
  });

  test('else replaces an atom and passes any other value', () {
    const src =
        'per(positional total, positional n) = total div n;\n'
        'a = per(90, 3) else 0;\nb = per(90, 0) else 0;\n'
        'c = per(90, 0) else #divByZero -> -1;\nd = per(90, 0) else #overflow -> -1;\n';
    expect(value(src, 'a'), '30');
    expect(value(src, 'b'), '0');
    expect(value(src, 'c'), '-1');
    expect(value(src, 'd'), '#divByZero', reason: 'a pattern that does not match passes it');
    expect(term(src, 'b'), r'match per(90, 0) { #_ -> 0, $2 -> $2 }');
  });

  test('a safe member passes an atom through', () {
    const src =
        'half(positional x) = x div 2;\nm = #missing;\nn = 8;\na = m?.half;\nb = n?.half;\n';
    expect(value(src, 'a'), '#missing');
    expect(value(src, 'b'), '4');
    expect(term(src, 'b'), r'{ $2 = n; match $2 { #_ -> $2, _ -> half($2) } }');
  });

  test('lambdas are called by position and capture their scope', () {
    const src =
        'rate = 3;\nscale = x -> x * rate;\nr = scale(14);\n'
        'both = (a, b) -> { s = a + b; s * s };\nq = both(1, 2);\n';
    expect(value(src, 'r'), '42');
    expect(value(src, 'q'), '9');
  });

  test('a name bound twice gets one kernel name per binder', () {
    const src = 'x = 1;\nnext(positional x) = x + 1;\ny = next(x);\n';
    expect(term(src, 'next'), 'x@2 -> (x@2 + 1)');
    expect(term(src, 'y'), 'next(x@1)');
    expect(value(src, 'y'), '2');
    // A binder named like a prelude word is renamed too, so the word stays free.
    const len = 'len = 4;\nw = len * 2;\n';
    expect(term(len, 'w'), '(len@1 * 2)');
    expect(value(len, 'w'), '8');
  });

  test('test tables check each case', () {
    const src =
        'square(positional x) = x * x test { 3 -> 9, 4 -> 15 }\n'
        'area(w, h) = w * h test { (2, 3) -> 6 }\n';
    final u = elab(src);
    expect(
      [for (final t in u.tests) (t.function, '${eval(withPrelude(u.close(t.check)))}')],
      [('square', 'true'), ('square', 'false'), ('area', 'true')],
    );
    // The tuple key gives the arguments in declaration order, whatever their kinds.
    expect('${u.tests[2].check}', '(area(2, 3) == 6)');
  });
}
