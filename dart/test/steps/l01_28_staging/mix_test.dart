/// `mix`: the build evaluates the demanded build-stage definitions and subterms, leaves the
/// port-dependent ones to run, and the staged program writes what the program writes.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/stage.dart';

import 'staging.dart';

/// A log filter: the day length and the cutoff are computed at build, the rest per line.
const uptime =
    'day = 60 * 60 * 24;\nweek = 7 * day;\n'
    'main(stdin: Lines) -> (stdout: Lines) {\n  '
    'secs = int(stdin[1]) else 0;\n  '
    'stdout <- String(week - secs) ++ " left of " ++ String(week);\n}\n';

void main() {
  test('constants are computed at build', () {
    final (p, s, report) = staged(uptime);
    expect(report.built, ['day', 'week']);
    expect(term(s, 'week'), '604800');
    expect(report.unread, isEmpty);
    expect(report.left, isEmpty);
    for (final input in ['700000\n', '12\n', 'noise\n']) {
      expect(out(s, input), out(p, input));
    }
    expect(out(s, '4800\n'), '600000 left of 604800\n');
  });

  test('a port-dependent definition is run-stage', () {
    final (p, s, _) = staged(uptime);
    expect(color(p.unit), contains(('week', Stage.build)));
    // `main` is a function, so it is known at build; its body reads the port and stays.
    final main = term(s, 'main');
    expect(main, contains('604800'));
    expect(main, contains('stdin'));
  });

  test('a definition nothing reads is never evaluated', () {
    final (p, s, report) = staged('broken = 1 / 0;\nunused = broken + 1;\n$uptime');
    expect(report.unread, ['broken', 'unused']);
    expect(report.left, isEmpty);
    expect(s.unit.defs.every((d) => d.name != 'broken'), isTrue);
    expect(out(s, '5\n'), out(p, '5\n'));
  });

  test('a failure atom is a value the build computes', () {
    const src =
        'ratio = int("n/a");\nmain(stdin: Lines) -> (stdout: Lines) {\n  '
        'stdout <- String(ratio) else "no ratio";\n}\n';
    final (p, s, report) = staged(src);
    expect(report.built, ['ratio']);
    expect(term(s, 'ratio'), '#invalid');
    expect(out(s, 'x\n'), 'no ratio\n');
    expect(out(s, 'x\n'), out(p, 'x\n'));
  });

  test('an evaluation error is left to run', () {
    // An integer past the evaluator's size limit stops evaluation: the build leaves it, and
    // the run reports it in the ordinary way.
    const src =
        'huge = 10 ** 100000000;\nmain(stdin: Lines) -> (stdout: Lines) {\n  '
        'stdout <- String(huge);\n}\n';
    final (p, s, report) = staged(src);
    expect(report.built, isEmpty);
    expect(report.left, hasLength(1), reason: '${report.left}');
    expect(term(s, 'huge'), term(p, 'huge'));
    expect(out(s, 'x\n'), out(p, 'x\n'));
    expect(out(s, 'x\n'), startsWith('error: '));
  });

  test('a term whose form shows it ends is built with no fuel', () {
    var (p, s, report) = staged(
      'twice(positional n: int) = n + n;\nbig = twice(twice(twice(3)));\n'
      'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- String(big);\n}\n',
    );
    expect(report.built, ['big']);
    expect(term(s, 'big'), '24');
    expect(out(s, 'x\n'), out(p, 'x\n'));
    // A fold with an operator that ends, through a lambda bound by `let`, is built too.
    (_, s, report) = staged(
      'main(stdin: Lines) -> (stdout: Lines) {\n  add(a: int, b: int) = a + b;\n  '
      'k = add(a: add(a: 1, b: 2), b: 3);\n  stdout <- String(k);\n}\n',
    );
    expect(report.left, isEmpty);
    expect(term(s, 'main'), contains('6'));
  });

  test('a term whose form does not show it ends is left to run', () {
    // `w(w)` calls through a parameter: the build does not run it, whatever fuel it would
    // take, and the residual program keeps it as written.
    final (_, s, report) = staged(
      'w(positional f) = f(f);\nspin = w(w);\n'
      'main(stdin: Lines) -> (stdout: Lines) {\n  '
      'stdout <- if false { String(spin) } else { "x" };\n}\n',
    );
    expect(report.built, isEmpty);
    expect(report.left, hasLength(1), reason: '${report.left}');
    expect(report.left[0].$2, 'its form does not show that it ends');
    expect(term(s, 'spin'), 'w(w)');
  });

  test('the form rule reads calls and family operators', () {
    Term lt(String x, Term e, Term b) => Let(x, e, b);
    const one = Lit(Int(1));
    // A lambda called directly, by a `let` name, or a prelude word ends.
    expect(ends(const App(Lam(['x'], Var('x')), [one])), isTrue);
    expect(ends(lt('f', const Lam(['x'], Var('x')), const App(Var('f'), [one]))), isTrue);
    expect(ends(const App(Var('len'), [one])), isTrue);
    // A call through a parameter does not, nor through a name bound to one.
    const w = Lam(['f'], App(Var('f'), [Var('f')]));
    expect(ends(w), isFalse, reason: 'its body calls a parameter');
    // A lambda bound by `let` and never called is not evaluated, so it may be one.
    expect(ends(lt('w', w, one)), isTrue);
    expect(ends(lt('w', w, const App(Var('w'), [Var('w')]))), isFalse);
    expect(ends(const App(w, [w])), isFalse);
    final g = Lam(['f'], lt('h', const Var('f'), const App(Var('h'), [one])));
    expect(ends(g), isFalse);
    // A `let` name shadowed by a parameter is the parameter.
    final shadow = lt('f', const Lam(['x'], Var('x')), const Lam(['f'], App(Var('f'), [one])));
    expect(ends(shadow), isFalse);
  });

  test('a dead branch is cut at build', () {
    final (p, s, _) = staged(
      'verbose = false;\nmain(stdin: Lines) -> (stdout: Lines) {\n  '
      'line = stdin[1] else "";\n  '
      'stdout <- if verbose { "read: " ++ line } else { line };\n}\n',
    );
    expect(term(s, 'main'), isNot(contains('read: ')));
    expect(out(s, 'abc\n'), out(p, 'abc\n'));
  });

  test('a local definition is computed where it is read', () {
    // `k` is build-stage, so its reads are computed and its definition dropped; `inc`, a
    // function nothing reads, is never evaluated; `n` reads the port and stays.
    final (p, s, report) = staged(
      'main(stdin: Lines) -> (stdout: Lines) {\n  k = 6 * 7;\n  '
      'inc(y: int) = y + 1;\n  n = int(stdin[1]) else 0;\n  '
      'stdout <- String(n + k);\n}\n',
    );
    final main = term(s, 'main');
    expect(main, contains('42'));
    expect(main.contains('k') || main.contains('inc'), isFalse, reason: main);
    expect(report.unread, contains('inc'));
    expect(out(s, '8\n'), '50\n');
    expect(out(s, '8\n'), out(p, '8\n'));
  });

  test('a write of a constant is left to run', () {
    // The text is build-stage; the write is an effect, so the build does not run it.
    final (p, s, report) = staged(
      'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- "a" ++ "b";\n}\n',
    );
    expect(report.left, isEmpty);
    expect(term(s, 'main'), contains('"ab"'));
    expect(out(s, 'x\n'), 'ab\n');
    expect(out(s, 'x\n'), out(p, 'x\n'));
  });
}
