/// Running a program against its ports (step L1.19): `main`'s header names the ports, each
/// input is read once, whole, the wave runs, and each output is written once, at the end.
///
/// An input `Lines` port is the family of its lines, keyed by line number from 1; a `Files`
/// port is a lookup, `Path ->? String | #ioError`, answered by the world at each path read and
/// kept, so the wave sees one value per path. An output `Lines` port takes one whole-value
/// push, a `String` (one line) or a family of them (one line per entry, in key order); keyed
/// and multi-site pushes arrive at layer L7. The writes are buffered and committed when the
/// wave ends, each with its acknowledgment, `#ok` or `#ioError(why)`; the program has no name
/// for the acknowledgment, so a failed write takes the default policy and aborts the wave.
///
/// A [Record] holds every input the wave read, so [Program.replay] runs it again without
/// reading the world.
library;

import 'dart:collection';
import 'dart:convert';
import 'dart:io';
import 'dart:typed_data';

import 'ast.dart' show BuildError, FunctionDef, Port, Stmt, TypeExpr, TypeName, unit;
import 'elab.dart' show ElabErrors, Unit, elaborate;
import 'interp.dart';
import 'kernel.dart';
import 'lex.dart' show LexError, lex;
import 'parse.dart' show ParseError, parse, top;
import 'resolve.dart' show ResolveErrors, resolve;
import 'source.dart' as source;

/// The kinds of input port `main` declares at L1.
enum PortKind {
  /// `Lines`, a stream read whole.
  lines,

  /// `Files`, a lookup by path.
  files,
}

/// Why a program could not be loaded or its wave could not run.
final class RunError implements Exception {
  final String message;

  const RunError(this.message);

  @override
  String toString() => message;
}

/// A program ready to run: its elaboration and `main`'s ports.
final class Program {
  final Unit _unit;

  /// The input ports, in header order.
  final List<(String, PortKind)> inputs;

  /// The output ports, in header order.
  final List<String> outputs;

  Program._(this._unit, this.inputs, this.outputs);

  /// `main` closed over the definitions it reaches, made at the first wave.
  late final Term _main = _unit.get('main')!;

  /// Runs one wave: `lines` gives the bytes of each `Lines` input, and `files` the lookup
  /// behind each `Files` input. An error stops the wave before anything is written; throws a
  /// [RunError].
  Wave run(Map<String, List<int>> lines, Lookup Function(String port) files) =>
      _wave(lines, files, null).$1;

  /// Runs one wave as [run] does, and records its provenance (step L1.20), every keypath
  /// beginning with the wave stamp, 0 for the one wave a program runs.
  (Wave, Provenance) provenance(Map<String, List<int>> lines, Lookup Function(String port) files) {
    final (wave, provenance) = _wave(lines, files, const [Int(0)]);
    return (wave, provenance!);
  }

  (Wave, Provenance?) _wave(
    Map<String, List<int>> lines,
    Lookup Function(String port) files,
    List<Value>? root,
  ) {
    final world = World();
    final record = Record();
    for (final (name, kind) in inputs) {
      switch (kind) {
        case PortKind.lines:
          final bytes = lines[name] ?? (throw RunError('no input for port `$name`'));
          world.input(name, splitLines(bytes));
          record.lines[name] = bytes;
        case PortKind.files:
          world.source(name, files(name));
      }
    }
    for (final name in outputs) {
      world.output(name);
    }
    final ev = Evaluator(world, provenanceRoot: root);
    try {
      ev.run(prelude(App(_main, [for (final (name, _) in inputs) Read(name)])));
    } on KernelError catch (e) {
      throw RunError('$e');
    }
    final writes = <(String, List<int>)>[];
    for (final name in outputs) {
      switch (world.log(name)) {
        case []:
          break;
        case [final v]:
          writes.add((name, _joinLines(name, v)));
        case final pushes:
          throw RunError(
            'port `$name` is pushed ${pushes.length} times in one wave; several pushes to '
            'one port arrive at layer L7',
          );
      }
    }
    record.files.addAll(world.reads);
    return (Wave(writes, record), ev.provenance);
  }

  /// Runs the wave `record` holds, reading nothing from the world.
  Wave replay(Record record) =>
      run(record.lines, (name) => _Recorded(record.files[name] ?? SplayTreeMap()));
}

/// The outcome of one wave: the writes, by port in header order, and the inputs it read.
final class Wave {
  /// Each output port pushed, and the bytes it writes.
  final List<(String, List<int>)> writes;

  /// What a replay needs.
  final Record record;

  Wave(this.writes, this.record);
}

/// The program in `bytes`; throws a [RunError] with its errors, one per line as
/// `line:col: why`.
Program load(List<int> bytes) {
  final String text;
  try {
    text = source.load(bytes);
  } on source.Reject catch (e) {
    throw RunError(e.render(bytes));
  }
  try {
    final (stmts, elaborated) = compile(text);
    return program(stmts, elaborated);
  } on Diagnostics catch (e) {
    throw RunError(e.all.join('\n'));
  }
}

/// A message of the compiler, at a line and column of the source, both counted from 1.
final class Diagnostic {
  final int line, col;
  final String message;

  Diagnostic(this.line, this.col, this.message);

  @override
  String toString() => '$line:$col: $message';
}

/// The diagnostics of the first phase that rejects a unit.
final class Diagnostics implements Exception {
  final List<Diagnostic> all;

  Diagnostics(this.all);

  @override
  String toString() => all.join('\n');
}

/// The statements and elaboration of the unit `text`; throws its [Diagnostics].
(List<Stmt>, Unit) compile(String text) {
  final b = utf8.encode(text);
  final lines = source.Lines(b);
  Diagnostic at(source.Span span, String why) {
    final (line, col) = lines.lineCol(b, span.start);
    return Diagnostic(line, col, why);
  }

  Diagnostics all(List<BuildError> errors) =>
      Diagnostics([for (final e in errors) at(e.span, e.message)]);
  try {
    final tokens = lex(text);
    final stmts = unit(text, tokens, parse(text, tokens, 'Unit', top));
    return (stmts, elaborate(stmts, resolve(stmts)));
  } on LexError catch (e) {
    throw Diagnostics([at(e.span, '$e')]);
  } on ParseError catch (e) {
    throw Diagnostics([at(e.span, '$e')]);
  } on BuildError catch (e) {
    throw all([e]);
  } on ResolveErrors catch (e) {
    throw all(e.errors);
  } on ElabErrors catch (e) {
    throw all(e.errors);
  }
}

/// The program `elaborated` is, with the ports its one `main` declares; throws a [RunError].
Program program(List<Stmt> stmts, Unit elaborated) {
  final mains = [
    for (final s in stmts)
      if (s case FunctionDef(name: 'main')) s,
  ];
  if (mains.length != 1) {
    throw RunError('a program declares one `main` function; this one declares ${mains.length}');
  }
  final main = mains.single;
  PortKind kind(String name, TypeExpr? type) => switch (type) {
    TypeName(name: 'Lines') => PortKind.lines,
    TypeName(name: 'Files') => PortKind.files,
    _ => throw RunError('port `$name` of `main` is `Lines` or `Files` at layer L1'),
  };
  final inputs = [for (final p in main.params) (p.name, kind(p.name, p.type))];
  final outputs = <String>[];
  for (final p in main.ports ?? const <Port>[]) {
    if (kind(p.name, p.type) != PortKind.lines) {
      throw RunError('output port `${p.name}` of `main` is `Lines` at layer L1');
    }
    outputs.add(p.name);
  }
  return Program._(elaborated, inputs, outputs);
}

/// Commits `writes` in order through `sink`, giving each write's acknowledgment, `#ok` or
/// `#ioError(why)`, where `why` is what `sink` threw. The first failure aborts the wave, as
/// the default policy does, so no later port is written.
List<(String, Value)> commit(
  List<(String, List<int>)> writes,
  void Function(String port, List<int> bytes) sink,
) {
  final acks = <(String, Value)>[];
  for (final (port, bytes) in writes) {
    try {
      sink(port, bytes);
    } on Object catch (e) {
      acks.add((port, Atom('ioError', [Str('$e')])));
      break;
    }
    acks.add((port, const Atom('ok')));
  }
  return acks;
}

/// The lines of `bytes`, keyed from 1. A line ends at `\n`, a `\r` before it is dropped, and
/// a last line needs no `\n`; a line that is not UTF-8 is `#ioError`, bare, as a failed read
/// of a `Files` port is (`LineNo -> String | #ioError`).
Value splitLines(List<int> bytes) {
  final lines = <(Value, Value)>[];
  for (var start = 0, n = 1; start < bytes.length; n++) {
    final nl = bytes.indexOf(0x0a, start);
    final next = nl < 0 ? bytes.length : nl + 1;
    var end = nl < 0 ? bytes.length : nl;
    if (end > start && bytes[end - 1] == 0x0d) end--;
    lines.add((Int(n), _text(bytes.sublist(start, end)) ?? const Atom('ioError')));
    start = next;
  }
  return Family.of(lines);
}

/// `bytes` as a string, or null when they are not UTF-8.
Value? _text(List<int> bytes) {
  try {
    return Str(utf8.decode(bytes));
  } on FormatException {
    return null;
  }
}

/// The bytes a push of `v` writes to `Lines` port `port`: each string, then `\n`.
List<int> _joinLines(String port, Value v) {
  final out = BytesBuilder(copy: false);
  for (final line in v is Family ? [for (final (_, leaf) in v.leaves()) leaf] : [v]) {
    if (line is! Str) throw RunError('port `$port` takes strings; $line was pushed');
    out
      ..add(utf8.encode(line.text.text))
      ..addByte(0x0a);
  }
  return out.takeBytes();
}

/// A `Files` port over the file system: each path is read when the program reads it.
final class Disk implements Lookup {
  const Disk();

  @override
  Value get(Value key) {
    if (key is! Str) throw PortFailure('a path is a String, not $key');
    try {
      return _text(File(key.text.text).readAsBytesSync()) ?? const Atom('ioError');
    } on PathNotFoundException {
      return const Atom('notFound');
    } on FileSystemException {
      return const Atom('ioError');
    }
  }
}

/// A `Files` port answered from a [Record].
final class _Recorded implements Lookup {
  final Map<Value, Value> _reads;

  _Recorded(this._reads);

  @override
  Value get(Value key) => _reads[key] ?? (throw PortFailure('the record holds no read of $key'));
}

const _magic = 'zed record 1\n';

/// The inputs a wave read: each `Lines` port's bytes and each `Files` port's reads, each in
/// key order.
final class Record {
  /// The bytes of each `Lines` port.
  final SplayTreeMap<String, List<int>> lines = SplayTreeMap();

  /// The paths read from each `Files` port and what each read gave.
  final SplayTreeMap<String, SplayTreeMap<Value, Value>> files = SplayTreeMap();

  Record();

  /// The record as bytes. After a first line `zed record 1`, each entry is a line of words,
  /// its kind and the lengths of its fields, then the fields' bytes and a `\n`:
  /// `lines P B` (port, bytes), `text P K B` (port, path, contents), and `missing P K` and
  /// `error P K` (port, path) for a read that gave `#notFound` or `#ioError`.
  Uint8List toBytes() {
    final out = BytesBuilder(copy: false)..add(utf8.encode(_magic));
    void entry(String kind, List<List<int>> fields) {
      out.add(utf8.encode('$kind ${[for (final f in fields) f.length].join(' ')}\n'));
      fields.forEach(out.add);
      out.addByte(0x0a);
    }

    for (final MapEntry(key: port, value: bytes) in lines.entries) {
      entry('lines', [utf8.encode(port), bytes]);
    }
    for (final MapEntry(key: port, value: reads) in files.entries) {
      final p = utf8.encode(port);
      for (final MapEntry(key: path, value: v) in reads.entries) {
        final k = utf8.encode((path as Str).text.text);
        switch (v) {
          case Str(:final text):
            entry('text', [p, k, utf8.encode(text.text)]);
          case Atom(name: 'notFound'):
            entry('missing', [p, k]);
          case Atom(name: 'ioError'):
            entry('error', [p, k]);
          default:
            throw StateError('a file read gives a String or an atom, not $v');
        }
      }
    }
    return out.takeBytes();
  }

  /// The record `bytes` holds; throws a [RunError] when they are not one.
  factory Record.fromBytes(List<int> bytes) {
    const bad = RunError('not a Zed record');
    final magic = utf8.encode(_magic);
    if (bytes.length < magic.length) throw bad;
    for (var i = 0; i < magic.length; i++) {
      if (bytes[i] != magic[i]) throw bad;
    }
    String text(List<int> f) {
      try {
        return utf8.decode(f);
      } on FormatException {
        throw bad;
      }
    }

    final record = Record();
    var at = magic.length;
    while (at < bytes.length) {
      final end = bytes.indexOf(0x0a, at);
      if (end < 0) throw bad;
      final [kind, ...lens] = text(bytes.sublist(at, end)).split(' ');
      at = end + 1;
      final fields = <List<int>>[];
      for (final w in lens) {
        final n = int.tryParse(w);
        if (n == null || n < 0 || w.startsWith('+') || at + n > bytes.length) throw bad;
        fields.add(bytes.sublist(at, at + n));
        at += n;
      }
      if (at >= bytes.length || bytes[at] != 0x0a) throw bad;
      at++;
      switch ((kind, fields)) {
        case ('lines', [final p, final b]):
          record.lines[text(p)] = b;
        case ('text', [final p, final k, final b]):
          record._read(text(p), text(k), Str(text(b)));
        case ('missing', [final p, final k]):
          record._read(text(p), text(k), const Atom('notFound'));
        case ('error', [final p, final k]):
          record._read(text(p), text(k), const Atom('ioError'));
        default:
          throw bad;
      }
    }
    return record;
  }

  void _read(String port, String path, Value v) =>
      files.putIfAbsent(port, SplayTreeMap.new)[Str(path)] = v;
}

/// A failed command: its exit status and what it prints.
final class _Exit implements Exception {
  final int status;
  final String why;

  _Exit(this.status, this.why);
}

/// `zedc run <file> [port=path …] [--record <out>]` and
/// `zedc replay <file> <record> [port=path …]`, with `args` the words after `zedc`. A `Lines`
/// input reads the file bound to it, or standard input if it is `stdin`; a `Lines` output
/// writes the file bound to it, or standard output or error if it is `stdout` or `stderr`.
/// Returns the exit status: 0, 1 when the program fails or a write fails, 2 for a usage
/// error.
Future<int> command(
  List<String> args,
  Future<List<int>> Function() stdin,
  void Function(List<int>) stdout,
  void Function(List<int>) stderr,
) async {
  try {
    await _command(args, stdin, stdout, stderr);
    return 0;
  } on _Exit catch (e) {
    stderr(utf8.encode('${e.why}\n'));
    return e.status;
  }
}

/// The bytes of the file at `path`; an [_Exit] with `status` when it cannot be read.
List<int> _read(String path, int status) {
  try {
    return File(path).readAsBytesSync();
  } on FileSystemException catch (e) {
    throw _Exit(status, '$path: ${_why(e)}');
  }
}

String _why(FileSystemException e) => e.osError?.message ?? e.message;

Future<void> _command(
  List<String> args,
  Future<List<int>> Function() stdin,
  void Function(List<int>) stdout,
  void Function(List<int>) stderr,
) async {
  final usage = _Exit(
    2,
    'usage: zedc run <file> [port=path …] [--record <out>]\n'
    '       zedc replay <file> <record> [port=path …]',
  );
  final (replay, file, rest) = switch (args) {
    ['run', final file, ...final rest] => (null, file, rest),
    ['replay', final file, final record, ...final rest] => (record, file, rest),
    _ => throw usage,
  };
  String? recordTo;
  final binds = SplayTreeMap<String, String>();
  for (var i = 0; i < rest.length; i++) {
    final word = rest[i];
    final eq = word.indexOf('=');
    if (word == '--record' && replay == null) {
      if (++i == rest.length) throw usage;
      recordTo = rest[i];
    } else if (eq >= 0) {
      binds[word.substring(0, eq)] = word.substring(eq + 1);
    } else {
      throw usage;
    }
  }
  final Program program;
  try {
    program = load(_read(file, 2));
  } on RunError catch (e) {
    throw _Exit(1, '$file:$e');
  }
  final known = {for (final (n, _) in program.inputs) n, ...program.outputs};
  for (final p in binds.keys) {
    if (!known.contains(p)) throw _Exit(2, '`main` has no port `$p`');
  }
  for (final name in program.outputs) {
    if (!binds.containsKey(name) && name != 'stdout' && name != 'stderr') {
      throw _Exit(2, 'output port `$name` needs a file: `$name=path`');
    }
  }
  final Wave wave;
  try {
    if (replay != null) {
      final Record record;
      try {
        record = Record.fromBytes(_read(replay, 2));
      } on RunError catch (e) {
        throw _Exit(2, '$replay: $e');
      }
      wave = program.replay(record);
    } else {
      final lines = <String, List<int>>{};
      for (final (name, kind) in program.inputs) {
        if (kind != PortKind.lines) continue;
        lines[name] = switch (binds[name]) {
          final path? => _read(path, 2),
          null when name == 'stdin' => await stdin(),
          null => throw _Exit(2, 'input port `$name` needs a file: `$name=path`'),
        };
      }
      wave = program.run(lines, (_) => const Disk());
    }
  } on RunError catch (e) {
    throw _Exit(1, '$e');
  }
  if (recordTo != null) {
    try {
      File(recordTo).writeAsBytesSync(wave.record.toBytes());
    } on FileSystemException catch (e) {
      throw _Exit(1, '$recordTo: ${_why(e)}');
    }
  }
  final acks = commit(wave.writes, (port, bytes) {
    switch (binds[port]) {
      case final path?:
        try {
          File(path).writeAsBytesSync(bytes);
        } on FileSystemException catch (e) {
          throw '$path: ${_why(e)}';
        }
      case null when port == 'stdout':
        stdout(bytes);
      case null:
        stderr(bytes);
    }
  });
  for (final (port, ack) in acks) {
    if (ack case Atom(name: 'ioError')) {
      throw _Exit(1, 'writing port `$port` failed: $ack');
    }
  }
}
