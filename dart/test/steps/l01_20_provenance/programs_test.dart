/// Provenance of whole programs with ports, through `Program.provenance`.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/run.dart';

import 'provenance.dart' show origins;

/// A `Files` port holding `files`; every other path is `#notFound`.
final class Disk implements Lookup {
  final Map<String, String> files;

  Disk(this.files);

  @override
  Value get(Value key) => switch (key) {
    Str(:final text) when files.containsKey(text.text) => Str(files[text.text]!),
    _ => const Atom('notFound'),
  };
}

Provenance trace(String src, String stdin, Map<String, String> files) {
  final disk = Disk(files);
  final (_, p) = load(utf8.encode(src)).provenance({'stdin': utf8.encode(stdin)}, (_) => disk);
  expect(p.repeated(), isEmpty);
  return p;
}

void main() {
  test('a failed total names the bad quantity and the missing price file', () {
    const src =
        'main(stdin: Lines, fs: Files) -> (stdout: Lines) {\n  '
        'qty = int(stdin[1]);\n  unit = int(fs["price.txt"]);\n  '
        'total = qty * unit;\n  stdout <- String(total) else "no total";\n}\n';
    final p = trace(src, 'three\n', {});
    final i = p.facts.lastIndexWhere((f) => f.value?.errs != null);
    expect(i, isNonNegative, reason: 'the merged failure');
    expect(origins(p, i), [
      ('fs("price.txt")', '#notFound'),
      ('int(tupleGet(stdin, 1))', '#invalid'),
    ]);
  });

  test('every keypath of a wave starts with its stamp', () {
    const src =
        'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- "\${int(stdin[1]) else 0}";\n}\n';
    final p = trace(src, '4\n', {});
    expect(p.facts.every((f) => f.address.keypath.first == const Int(0)), isTrue);
  });
}
