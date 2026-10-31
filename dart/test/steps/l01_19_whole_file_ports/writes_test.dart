/// Writes: one whole-value push per port per wave, committed when the wave ends, each with an
/// acknowledgment; a failed write aborts the wave.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/run.dart';

import 'ports.dart';

void main() {
  test('a report goes to a file bound on the command line', () async {
    final path = '${dir('report').path}/report.txt';
    File(path).writeAsStringSync('stale\n');
    const src =
        'main(stdin: Lines) -> (report: Lines, stdout: Lines) {\n  '
        'report <- stdin;\n  stdout <- "wrote the report";\n}\n';
    var out = await run('report', src, 'total: 42\nitems: 3\n', ['report=$path']);
    expect((out.status, out.stdout), (0, 'wrote the report\n'));
    expect(File(path).readAsStringSync(), 'total: 42\nitems: 3\n');
    // A port other than `stdout` and `stderr` must be bound before the wave runs.
    out = await run('report', src, '');
    expect((out.status, out.stderr), (2, 'output port `report` needs a file: `report=path`\n'));
  });

  test('an error stops the wave before anything is written', () async {
    final path = '${dir('abort').path}/out.txt';
    File(path).writeAsStringSync('previous\n');
    // `out` is pushed first in the text, then `1 + "x"` is a type error.
    const src =
        'main() -> (out: Lines, stdout: Lines) {\n  '
        'out <- "half done";\n  stdout <- String(1 + "x");\n}\n';
    final out = await run('abort', src, '', ['out=$path']);
    expect(out.status, 1, reason: out.stderr);
    expect(out.stderr, startsWith('type error'));
    expect(out.stdout, '');
    expect(File(path).readAsStringSync(), 'previous\n');
  });

  test('a port pushed twice in one wave is an error', () async {
    var src =
        'say(positional s) -> (stdout: Lines) {\n  stdout <- s;\n}\n'
        'main() -> (stdout: Lines) {\n  a = say("one");\n  b = say("two");\n}\n';
    final out = await run('twice', src, '');
    expect(out.status, 1);
    expect(
      out.stderr,
      'port `stdout` is pushed 2 times in one wave; several pushes to one port arrive at '
      'layer L7\n',
    );
    expect(out.stdout, '', reason: 'nothing is written');
    // Two push sites on different branches are fine: one of them runs.
    src =
        'accept() -> (stdout: Lines) {\n  stdout <- "accepted";\n}\n'
        'decline() -> (stdout: Lines) {\n  stdout <- "declined";\n}\n'
        'main(stdin: Lines) -> (stdout: Lines) {\n  '
        'done = if stdin[1] == "yes" { accept() } else { decline() };\n}\n';
    expect((await run('branches', src, 'no\n')).stdout, 'declined\n');
  });

  test('only strings are written as lines', () async {
    const src = 'main() -> (stdout: Lines) {\n  stdout <- 42;\n}\n';
    final out = await run('number', src, '');
    expect((out.status, out.stderr), (1, 'port `stdout` takes strings; 42 was pushed\n'));
  });

  test('the first failed write aborts the rest', () async {
    final writes = [
      ('audit', 'a\n'.codeUnits),
      ('stdout', 'b\n'.codeUnits),
      ('stderr', 'c\n'.codeUnits),
    ];
    final done = <String>[];
    final acks = commit(writes, (port, _) {
      done.add(port);
      if (port == 'stdout') throw 'disk full';
    });
    expect(done, ['audit', 'stdout'], reason: 'stderr is never written');
    expect(
      [for (final (p, v) in acks) (p, '$v')],
      [('audit', '#ok'), ('stdout', '#ioError("disk full")')],
    );
    // Through the command, a failed write exits 1 and names the port.
    const src = 'main() -> (log2: Lines) {\n  log2 <- "x";\n}\n';
    final out = await run('unwritable', src, '', ['log2=/nonexistent-dir-l01-19/x.txt']);
    expect(out.status, 1);
    expect(
      out.stderr,
      startsWith('writing port `log2` failed: #ioError("/nonexistent-dir-l01-19/x.txt: '),
    );
  });

  test('usage errors exit 2', () async {
    const src = 'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin;\n}\n';
    var out = await run('usage', src, '', ['nosuch=x']);
    expect((out.status, out.stderr), (2, '`main` has no port `nosuch`\n'));
    out = await run('usage', src, '', ['--bogus']);
    expect(out.status, 2);
    expect(out.stderr, startsWith('usage: zedc run'));
    out = await run('usage', 'main( = ;\n', '');
    expect(out.status, 1, reason: 'a program that does not parse fails, with its position');
    expect(out.stderr, contains('prog.zed:1:'));
  });
}
