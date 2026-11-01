/// Step L1.29: diagnostics. A rejection shows its derivation: each type constraint and each
/// step of propagation that led to it, numbered and placed in the source, the declarations
/// and signatures it met, every failing combination of a signature search, and the repairs
/// the checker discharges.
library;

import 'dart:convert';

import 'package:zed/run.dart';

/// The rendered diagnostics of the rejected program `src`.
String rejected(String src) {
  try {
    load(utf8.encode(src));
  } on RunError catch (e) {
    return e.message;
  }
  throw StateError('accepted:\n$src');
}

final _step = RegExp(r'^\[\d+\] +[^:]*:[^:]*: (.*)$');

/// The step texts of the rendered diagnostics `out`, without their places.
List<String> steps(String out) => [
  for (final l in out.split('\n'))
    if (_step.firstMatch(l.trimLeft()) case final m?) m[1]!,
];
