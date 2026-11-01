/// The differential oracle (step L1.37, DESIGN.md Part G): the interpreter and the native code
/// run the same source, and what each gives is compared byte for byte.
///
/// A unit is compared two ways. Each top-level binding bound by `=` whose type, as the checker
/// gives it, has no function component is run alone, and its outcome is compared: the value
/// as [Value.toString] prints it, or the error. A binding the checker types `_` may still be a
/// function; both engines then refuse it with the same error, so its outcome is still
/// compared. And every check of the unit's `test` tables, `main`'s waves included, is run by
/// each engine and compared with the interpreter's. A program is compared by the bytes of each
/// port it writes, or by its error.
///
/// A float whose type carries the reorder facet of `unordered` is to be compared by its type
/// and keys only; the facet arrives at layer L9, and with it that rule.
library;

import 'dart:convert';
import 'dart:io';

import 'package:zed/elab.dart' show Cones, Unit;
import 'package:zed/interp.dart' show prelude;
import 'package:zed/kernel.dart';
import 'package:zed/native.dart' as native;
import 'package:zed/query.dart' show Db;
import 'package:zed/run.dart';
import 'package:zed/testing.dart';

import 'support.dart';

/// The highest layer whose fences and corpus programs are enabled.
const enabled = 1;

/// A named way to run a closed term, compared against the interpreter.
typedef Engine = (String, Through);

/// The two native engines: the plan with fused match release, and without it.
final List<Engine> natives = [
  ('native (fused)', native.through(true)),
  ('native (unfused)', native.through(false)),
];

/// What one comparison found.
final class Report {
  /// How many outcomes were compared, counting each engine once.
  var compared = 0;

  /// Each disagreement, with both outcomes.
  final mismatches = <String>[];

  void _compare(String what, String engine, String want, String got) {
    compared++;
    if (want != got) {
      mismatches.add('$what: the interpreter gives $want, and $engine gives $got');
    }
  }

  /// Adds [other]'s counts and mismatches, each prefixed with [at].
  void add(String at, Report other) {
    compared += other.compared;
    mismatches.addAll(other.mismatches.map((m) => '$at: $m'));
  }
}

/// The outcome of running [t] by [engine] with no ports, as the oracle compares it.
String _printed(Through engine, Term t) {
  try {
    return 'the value ${engine(t, Evaluator(World()))}';
  } on RunError catch (e) {
    return 'the error `${e.message}`';
  } on KernelError catch (e) {
    return 'the error `$e`';
  }
}

/// The checks of a unit as the oracle compares them.
String _checks(List<Outcome> os) =>
    [for (final o in os) '${o.line}:${o.col}: ${o.failure}'].toString();

/// Compares the unit [text] under each of [engines]: its bindings with no function component,
/// and the checks of its tables. A rejected unit compares nothing.
Report unit(String text, List<Engine> engines) {
  final Unit u;
  try {
    (_, u) = Db().front(text);
  } on Diagnostics {
    return Report();
  }
  final r = bindings(u, engines);
  final want = _checks(testUnit(text));
  for (final (name, engine) in engines) {
    final got = _checks(testThrough(text, engine));
    r.compared++;
    if (got != want) {
      r.mismatches.add('the table checks: the interpreter gives $want, and $name gives $got');
    }
  }
  return r;
}

/// Compares the bindings of [u] with no function component under each of [engines].
Report bindings(Unit u, List<Engine> engines) {
  final r = Report();
  final cones = Cones(u);
  for (final d in u.defs.where((d) => d.firstOrder)) {
    final t = prelude(cones.close(Var(d.kernel)));
    final want = _printed(direct, t);
    for (final (name, engine) in engines) {
      r._compare('binding `${d.name}`', name, want, _printed(engine, t));
    }
  }
  return r;
}

/// The bytes each port writes, or the error, as the oracle compares them.
String _writes(Wave Function() run) {
  final Wave w;
  try {
    w = run();
  } on RunError catch (e) {
    return 'the error `${e.message}`';
  }
  if (w.writes.isEmpty) return 'no writes';
  return [
    for (final (port, bytes) in w.writes)
      'port `$port` writes ${Str(utf8.decode(bytes, allowMalformed: true))}',
  ].join(', ');
}

/// A `Files` port whose every path holds the same text.
final class _Same implements Lookup {
  final Value v;

  _Same(this.v);

  @override
  Value get(Value key) => v;
}

/// Runs the program [text] with every `Lines` input given [input] and every path of every
/// `Files` input holding [input] as a `String`, and compares its writes under each of
/// [engines]. The interpreter's writes are returned beside the report; a program that does not
/// load compares nothing.
(Report, String?) program(String text, List<int> input, List<Engine> engines) {
  final r = Report();
  final Program p;
  try {
    p = load(utf8.encode(text));
  } on RunError {
    return (r, null);
  }
  final lines = {
    for (final (name, kind) in p.inputs)
      if (kind == PortKind.lines) name: input,
  };
  final same = _Same(Str(utf8.decode(input, allowMalformed: true)));
  Lookup files(String _) => same;
  final want = _writes(() => p.run(lines, files));
  for (final (name, engine) in engines) {
    r._compare('the wave', name, want, _writes(() => p.runThrough(lines, files, engine)));
  }
  return (r, want);
}

/// The corpus directory, `zed/corpus/`.
final Directory corpusDir = Directory('${packageDir.parent.path}/zed/corpus');

final _layer = RegExp(r'^// layer L(\d+)');

/// Each corpus program and the layer its first line labels, in name order.
List<(File, int)> corpus() {
  final files =
      corpusDir.listSync().whereType<File>().where((f) => f.path.endsWith('.zed')).toList()
        ..sort((a, b) => a.path.compareTo(b.path));
  return [
    for (final f in files)
      if (_layer.firstMatch(f.readAsLinesSync().first) case final m?)
        (f, int.parse(m[1]!))
      else
        throw StateError('${f.path} has no `// layer L<n>` line'),
  ];
}

/// The step units, `test/steps/*/zed/*.zed`, in path order.
List<File> stepUnits() => [
  for (final step in stepsDir.listSync().whereType<Directory>())
    if (Directory('${step.path}/zed') case final d when d.existsSync())
      ...d.listSync().whereType<File>(),
]..sort((a, b) => a.path.compareTo(b.path));

/// [f]'s path relative to the package's parent folder.
String shown(File f) => f.path.substring(packageDir.parent.path.length + 1);
