/// The port runtime of one wave (step L1.36, sec:ports): a `Lines` input's bytes as the
/// family of its lines, and the bytes a push to a `Lines` output writes. Written apart from
/// the interpreter's (`splitLines` and `joinLines` of the runner), so the differential test
/// compares the two.
library;

import 'dart:convert';

import '../kernel/value.dart';
import '../../run.dart' show RunError;

/// The lines of [bytes], keyed from 1: a line ends at `\n`, which a last line may lack; a
/// `\r` before the `\n` is not part of the line; a line that is not UTF-8 is a bare
/// `#ioError`.
Value lines(List<int> bytes) {
  final out = <(Value, Value)>[];
  var start = 0;
  while (start < bytes.length) {
    var end = start;
    while (end < bytes.length && bytes[end] != 0x0a) {
      end++;
    }
    final last = end > start && bytes[end - 1] == 0x0d ? end - 1 : end;
    Value v;
    try {
      v = Str(const Utf8Decoder().convert(bytes, start, last));
    } on FormatException {
      v = const Atom('ioError');
    }
    out.add((Int(out.length + 1), v));
    start = end + 1;
  }
  return Family.of(out);
}

/// The bytes a push of [v] to `Lines` port [port] writes: each line of a family, or the one
/// string, followed by `\n`.
List<int> write(String port, Value v) {
  final out = <int>[];
  for (final line in v is Family ? [for (final (_, leaf) in v.leaves()) leaf] : [v]) {
    switch (line) {
      case Str(:final text):
        out
          ..addAll(utf8.encode(text.text))
          ..add(0x0a);
      case final other:
        throw RunError('port `$port` takes strings; $other was pushed');
    }
  }
  return out;
}
