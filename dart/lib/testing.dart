/// The test runner (step L1.21, DESIGN.md sec:lexical, the test table row): `zedc test` runs
/// every `test { }` table of a unit and checks its `// ✗` marks.
///
/// A row of a function's table passes when the call equals the expected value under `==`. A
/// row of `main`'s table is a wave: the key gives the input ports, a `Lines` port as the
/// `String` of its bytes and a `Files` port as a function from path to contents, and the
/// value gives the `String` each output port writes. A unit that is rejected passes when
/// every diagnostic is on a line marked ✗ and every marked line has one; its tables do not
/// run. A wave that aborts fails its row: no form expects an abort at L1.
library;

import 'dart:convert';
import 'dart:io';

import 'ast.dart' show FunctionDef;
import 'elab.dart' show Cones, Test;
import 'fence.dart' as fence;
import 'interp.dart';
import 'kernel.dart';
import 'query.dart';
import 'run.dart';
import 'source.dart' as source;

/// One check of a unit: a row of a table, a marked line, or a diagnostic on an unmarked line.
final class Outcome {
  /// Its line and column, counted from 1.
  final int line, col;

  /// Why it fails; null when it passes.
  final String? failure;

  Outcome(this.line, this.col, this.failure);
}

/// The checks of the unit `text`, in source order.
List<Outcome> testUnit(String text) => testIn(Db(), text);

/// The checks of the unit `text`, in source order, reusing what `db` holds (step L1.30).
List<Outcome> testIn(Db db, String text) {
  final marked = fence.marks(text).lines;
  final out = <Outcome>[];
  try {
    final (stmts, unit) = db.front(text);
    final b = utf8.encode(text);
    final lines = source.Lines(b);
    final cones = Cones(unit);
    for (final line in marked) {
      out.add(Outcome(line, 1, 'the line is marked ✗ and the unit is accepted'));
    }
    Program? p;
    for (final s in stmts) {
      if (s case FunctionDef(name: 'main')) {
        try {
          p = program(stmts, unit);
        } on RunError catch (e) {
          final (line, col) = lines.lineCol(b, s.span.start);
          out.add(Outcome(line, col, e.message));
        }
        break;
      }
    }
    final main = [
      for (final d in unit.defs)
        if (d.name == 'main') Var(d.kernel),
    ].firstOrNull;
    for (final t in unit.tests) {
      String? fails(void Function() check) {
        try {
          check();
          return null;
        } on _Fail catch (e) {
          return e.why;
        }
      }

      final String? why;
      if (t.function != 'main') {
        why = db.row(
          Query.row,
          key('row', [
            cone(cones, [t.check]),
          ]),
          () => fails(() => _row(cones, t)),
        );
      } else if (p case final p?) {
        final ports = utf8.encode('${p.inputs} ${p.outputs}');
        final k = key('wave', [
          cone(cones, [main!, t.want, ...t.args]),
          ports,
        ]);
        why = db.row(Query.wave, k, () => fails(() => _wave(cones, p, t)));
      } else {
        continue;
      }
      final (line, col) = lines.lineCol(b, t.span.start);
      final case_ = utf8.decode(b.sublist(t.span.start, t.span.end));
      out.add(Outcome(line, col, why == null ? null : '`$case_` of `${t.function}`: $why'));
    }
  } on Diagnostics catch (e) {
    // The first diagnostic on each line.
    final first = <int, Diagnostic>{};
    for (final d in e.all) {
      first.putIfAbsent(d.line, () => d);
    }
    for (final line in marked) {
      final d = first[line];
      out.add(
        Outcome(line, d?.col ?? 1, d == null ? 'the line is marked ✗ and has no diagnostic' : null),
      );
    }
    final isMarked = marked.toSet();
    for (final d in e.all) {
      // The message and its derivation (DESIGN.md "Diagnostics"), after the place the outcome
      // already gives.
      if (!isMarked.contains(d.line)) {
        out.add(Outcome(d.line, d.col, '$d'.substring('${d.line}:${d.col}: '.length)));
      }
    }
  }
  out.sort((a, b) => a.line != b.line ? a.line - b.line : a.col - b.col);
  return out;
}

/// Why a row fails.
final class _Fail implements Exception {
  final String why;

  _Fail(this.why);
}

/// The value of `term` under the definitions it reaches and the prelude.
Value _value(Cones cones, Term term) {
  try {
    return Evaluator(World()).run(prelude(cones.close(term)));
  } on KernelError catch (e) {
    throw _Fail('$e');
  }
}

/// Checks a row of a function's table.
void _row(Cones cones, Test t) {
  if (_value(cones, t.check) != const Bool(true)) {
    final PrimApp(args: [call, _]) = t.check as PrimApp;
    throw _Fail('the result is ${_value(cones, call)}');
  }
}

/// Checks a row of `main`'s table: runs the wave its key gives, and compares the writes.
void _wave(Cones cones, Program program, Test t) {
  final lines = <String, List<int>>{};
  final files = <String, Lookup>{};
  for (final ((name, kind), arg) in _zip(program.inputs, t.args)) {
    switch (kind) {
      case PortKind.lines:
        lines[name] = switch (_value(cones, arg)) {
          Str(:final text) => utf8.encode(text.text),
          final v => throw _Fail('the `Lines` port `$name` is given as a String, not $v'),
        };
      case PortKind.files:
        files[name] = _Given(prelude(cones.close(arg)));
    }
  }
  final Wave wave;
  try {
    wave = program.run(lines, (name) => files[name]!);
  } on RunError catch (e) {
    throw _Fail(e.message);
  }
  final outputs = program.outputs;
  final wants = switch ((outputs.length, _value(cones, t.want))) {
    (1, final v) => [v],
    (final n, Tuple(:final items)) when items.length == n => items,
    (final n, final v) => throw _Fail(
      'the expected value is a String for each of the $n output ports, not $v',
    ),
  };
  // The first write to each port.
  final written = <String, List<int>>{};
  for (final (name, bytes) in wave.writes) {
    written.putIfAbsent(name, () => bytes);
  }
  for (final (name, want) in _zip(outputs, wants)) {
    if (want is! Str) throw _Fail('the expected value of port `$name` is a String, not $want');
    final got = written[name] ?? const <int>[];
    if (!_same(got, utf8.encode(want.text.text))) {
      throw _Fail('port `$name` writes ${Str(utf8.decode(got, allowMalformed: true))}');
    }
  }
}

Iterable<(A, B)> _zip<A, B>(List<A> a, List<B> b) sync* {
  for (var i = 0; i < a.length && i < b.length; i++) {
    yield (a[i], b[i]);
  }
}

bool _same(List<int> a, List<int> b) {
  if (a.length != b.length) return false;
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

/// A `Files` port a test gives as a function from path to contents.
final class _Given implements Lookup {
  final Term _f;

  _Given(this._f);

  @override
  Value get(Value key) {
    try {
      return Evaluator(World()).run(App(_f, [Lit(key)]));
    } on KernelError catch (e) {
      throw PortFailure('$e');
    }
  }
}

/// `zedc test <file> …`, with `args` the words after `test`: writes each failing check as
/// `file:line:col: why`, then the counts. Returns the exit status: 0 when every check passes,
/// 1 when one fails, 2 for a usage error or a file that cannot be read.
int command(List<String> args, StringSink stdout, StringSink stderr) {
  if (args.isEmpty) {
    stderr.writeln('usage: zedc test <file> …');
    return 2;
  }
  var (passed, failed) = (0, 0);
  for (final file in args) {
    final List<int> bytes;
    try {
      bytes = File(file).readAsBytesSync();
    } on FileSystemException catch (e) {
      stderr.writeln('$file: ${e.osError?.message ?? e.message}');
      return 2;
    }
    final String text;
    try {
      text = source.load(bytes);
    } on source.Reject catch (e) {
      stdout.writeln('$file: $e');
      failed++;
      continue;
    }
    for (final o in testUnit(text)) {
      if (o.failure case final why?) {
        stdout.writeln('$file:${o.line}:${o.col}: $why');
        failed++;
      } else {
        passed++;
      }
    }
  }
  stdout.writeln('$passed passed, $failed failed');
  return failed > 0 ? 1 : 0;
}
