/// `Files` ports: `fs[path]` is `String | #ioError | #notFound`, and each path is read from
/// the world at most once per wave.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/run.dart';

import 'ports.dart';

/// A `Files` port that counts the reads the world answers.
final class Counting implements Lookup {
  var reads = 0;

  @override
  Value get(Value key) {
    reads++;
    return Str('contents of $key');
  }
}

void main() {
  test('a config file is read and a missing one falls back', () async {
    final d = dir('config').path;
    File('$d/app.conf').writeAsStringSync('  verbose  \n');
    final src =
        'main(fs: Files) -> (stdout: Lines) {\n  '
        'mode = trim(fs["$d/app.conf"]) else "quiet";\n  '
        'extra = (fs["$d/absent.conf"] else #notFound -> "(no overrides)") else "(unreadable)";\n  '
        'stdout <- "mode=\${mode} \${extra}";\n}\n';
    final out = await run('config', src, '');
    expect((out.status, out.stdout), (0, 'mode=verbose (no overrides)\n'));
  });

  test('a file that is not UTF-8 is an I/O error', () async {
    final bin = '${dir('binary').path}/blob.bin';
    File(bin).writeAsBytesSync([0xff, 0x00, 0xfe]);
    final src =
        'main(fs: Files) -> (stdout: Lines) {\n  '
        'stdout <- (fs["$bin"] else #ioError -> "unreadable") else "missing";\n}\n';
    expect((await run('binary', src, '')).stdout, 'unreadable\n');
    expect(const Disk().get(Str(bin)), const Atom('ioError'));
    expect(
      () => const Disk().get(const Int(3)),
      throwsA(isA<PortFailure>().having((e) => e.why, 'why', 'a path is a String, not 3')),
    );
  });

  test('each path is read once, so the wave sees one value', () {
    const src =
        'main(fs: Files) -> (stdout: Lines) {\n  '
        'a = fs["notes.txt"];\n  b = fs["notes.txt"];\n  c = fs["todo.txt"];\n  '
        'stdout <- "\${a == b} \${c else "none"}";\n}\n';
    final p = load(src.codeUnits);
    final port = Counting();
    final wave = p.run({}, (_) => port);
    expect(port.reads, 2, reason: 'notes.txt once, todo.txt once');
    expect(wave.writes[0].$2, 'true contents of "todo.txt"\n'.codeUnits);
    expect([for (final k in wave.record.files['fs']!.keys) '$k'], ['"notes.txt"', '"todo.txt"']);
  });

  test('ports are `Lines` or `Files` at L1', () {
    String err(String src) {
      try {
        load(src.codeUnits);
      } on RunError catch (e) {
        return e.message;
      }
      fail('$src: loaded');
    }

    expect(
      err('main(n: int) -> (stdout: Lines) {\n  stdout <- "x";\n}\n'),
      'port `n` of `main` is `Lines` or `Files` at layer L1',
    );
    expect(
      err('main(fs: Files) -> (out: Files) {\n  out <- fs;\n}\n'),
      'output port `out` of `main` is `Lines` at layer L1',
    );
    expect(err('helper = 1;\n'), 'a program declares one `main` function; this one declares 0');
  });
}
