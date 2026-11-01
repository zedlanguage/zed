/// Step L1.28: staging. A term is build-stage when it reads only build-stage definitions and
/// prelude words and no port; the build evaluates the demanded ones to literals, leaves the
/// rest to run, never evaluates a definition nothing reads, and leaves a build-stage term
/// whose form does not show that it ends, or whose evaluation fails, to run whole. The Trick
/// specializes a function on a parameter only when the parameter's domain is finite.
library;

import 'dart:convert';

import 'package:zed/run.dart';
import 'package:zed/stage.dart';

/// The program `src`, and it staged, with the report.
(Program, Program, Report) staged(String src) {
  final p = load(utf8.encode(src));
  final (s, report) = p.stage();
  return (p, s, report);
}

/// What one wave of `p` writes to `stdout` on `stdin`, or its error.
String out(Program p, String stdin) {
  try {
    final w = p.run({'stdin': utf8.encode(stdin)}, (_) => throw StateError('no `Files` port'));
    return [for (final (_, b) in w.writes) utf8.decode(b, allowMalformed: true)].join();
  } on RunError catch (e) {
    return 'error: $e';
  }
}

/// The term of definition `name` of `p`, printed.
String term(Program p, String name) {
  final d = p.unit.defs.where((d) => d.name == name).firstOrNull;
  return '${(d ?? (throw StateError('no definition `$name`'))).term}';
}
