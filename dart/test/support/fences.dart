/// The documentation's fences, copied from the spec into `zed/fences/` by `tools/bin/sync.dart`
/// (step L1.7), and the hand-written fixtures of their commented ✗ variants.
library;

import 'dart:io';

import 'package:zed/fence.dart' as fence;

import 'support.dart';

/// A fence of DESIGN.md or EXAMPLES.md, with what `tools/bin/sync.dart` recorded about it: the
/// document and line of its ```` ```zed ```` (`DESIGN.md:196`), the layer from which it is
/// parsed, checked and run, the lowest ring of sec:grammar at which it parses, whether it parses
/// only under the documentation notation of sec:grammar, and its text.
typedef DocFence = ({String at, int layer, int ring, bool notation, String text});

/// A rejected variant, a fence with one commented ✗ line made live: the fixture's file name
/// without `.zed`, the commented line of the fence it is a variant of, trimmed, and the
/// fixture's text, its first line, `// variant: …`, included.
typedef Variant = ({String name, String of, String text});

/// The folder `zed/fences/`.
final Directory dir = Directory('${packageDir.parent.path}/zed/fences');

final _header = RegExp(r'^<!-- (.*?) layer L(\d+): ring L(\d+),');

/// The fences of the copy `file` (`design.md` or `examples.md`), in order.
List<DocFence> of(String file) => [
  for (final f in fence.extract(File('${dir.path}/$file').readAsStringSync()))
    if (_header.firstMatch(f.before) case final m?)
      (
        at: m[1]!,
        layer: int.parse(m[2]!),
        ring: int.parse(m[3]!),
        notation: f.before.endsWith(', documentation notation -->'),
        text: f.text,
      )
    else
      throw StateError('no header before the fence at line ${f.line}: ${f.before}'),
];

/// Every fence: DESIGN.md's, then EXAMPLES.md's.
List<DocFence> all() => [...of('design.md'), ...of('examples.md')];

/// Every variant fixture, by name.
List<Variant> variants() {
  final files = Directory('${dir.path}/variants').listSync().whereType<File>().toList()
    ..sort((a, b) => a.path.compareTo(b.path));
  return [
    for (final f in files)
      if (f.readAsStringSync() case final text)
        (
          name: f.uri.pathSegments.last.replaceFirst(RegExp(r'\.zed$'), ''),
          of: text.split('\n').first.startsWith('// variant: ')
              ? text.split('\n').first.substring('// variant: '.length)
              : throw StateError('${f.path} has no `// variant:` line'),
          text: text,
        ),
  ];
}
