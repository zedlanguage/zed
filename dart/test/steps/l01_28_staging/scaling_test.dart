/// Staging at the rule of low complexity (DESIGN.md Part G). Deciding the stage of a term
/// reads its free names; deciding it at every node `mix` enters would read a body of `n`
/// nested definitions `O(n)` times, each through a scope of `O(n)` names, so the stage of each
/// subterm is one range query over an index of the term made once.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/elab.dart';
import 'package:zed/kernel.dart';
import 'package:zed/run.dart';
import 'package:zed/stage.dart';

import '../../support/scaling.dart';
import '../l01_16_elaboration/elab.dart';
import 'staging.dart';

/// `main` with `n` local definitions in a chain from a port, each read by the next; `all`
/// writes their sum, so the last term reads every one.
String chain(int n, bool all) {
  final s = StringBuffer('main(stdin: Lines) -> (stdout: Lines) {\n')
    ..write('  x0 = int(stdin[1]) else 0;\n');
  for (var i = 1; i <= n; i++) {
    s.write('  x$i = x${i - 1} + $i;\n');
  }
  final last = all ? [for (var i = 0; i <= n; i++) 'x$i'].join(' + ') : 'x$n';
  s.write('  stdout <- String($last);\n}\n');
  return '$s';
}

/// `f` and `n` definitions, each calling it with its own literal.
String callers(int n) {
  final s = StringBuffer('f(x: int, y: int) = x + y;\n');
  for (var i = 0; i < n; i++) {
    s.write('z$i(a: int) = f(x: $i, y: a);\n');
  }
  return '$s';
}

/// `n` nested lets, each calling the prelude word `len` on the one before.
Term lets(int n) {
  Term b = Var('x$n');
  for (var i = n; i >= 1; i--) {
    b = Let('x$i', App(const Var('len'), [Var('x${i - 1}')]), b);
  }
  return b;
}

void main() {
  test('mixing a chain of local definitions scales', () {
    // Loading the program is timed by its own steps' tests, and here would hide the mix.
    final programs = {
      for (final n in [400, factor * 400]) n: load(utf8.encode(chain(n, false))),
    };
    check('mixing a chain of n run-stage definitions', 400, (n) {
      final (s, report) = programs[n]!.stage();
      expect(report.left, isEmpty);
      expect(out(s, '1\n'), '${1 + n * (n + 1) ~/ 2}\n');
    });
  });

  test('mixing a term that reads every definition scales', () {
    final programs = {
      for (final n in [200, factor * 200]) n: load(utf8.encode(chain(n, true))),
    };
    check('mixing a chain of n definitions all read at the end', 200, (n) {
      final (s, _) = programs[n]!.stage();
      var want = 0;
      for (var i = 0; i <= n; i++) {
        want += 1 + i * (i + 1) ~/ 2;
      }
      expect(out(s, '1\n'), '$want\n');
    });
  });

  test('the values passed by many definitions are read in time that scales', () {
    // Each definition was looked for among the names of all of them.
    final units = <int, Unit>{
      for (final n in [2000, factor * 2000]) n: elab(callers(n)),
    };
    check('the values passed by n definitions', 2000, (n) {
      expect(passed(units[n]!, 'f', 0), hasLength(n));
    });
  });

  test('the form rule on many nested lets calling a prelude word scales', () {
    // Each call through a name looked for it among every name bound around the call, and a
    // prelude word is bound by none of them.
    final terms = <int, Term>{
      for (final n in [1000, factor * 1000]) n: lets(n),
    };
    check('the form rule on n nested lets', 1000, (n) {
      expect(ends(terms[n]!), isTrue);
    });
    expect(ends(Lam(['f'], lets(3))), isTrue, reason: '`len` is not `f`');
    expect(ends(Lam(['f'], App(const Var('f'), [lets(3)]))), isFalse);
  });
}
