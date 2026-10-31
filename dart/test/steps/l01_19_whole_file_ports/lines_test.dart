/// `Lines` ports: standard input as the family of its lines, keyed from 1, and a pushed
/// string or family written as lines.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/run.dart';

import 'ports.dart';

void main() {
  test('`cat` echoes standard input line by line', () async {
    const src = 'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin;\n}\n';
    var out = await run('cat', src, 'first\nsecond\n');
    expect((out.status, out.stdout), (0, 'first\nsecond\n'));
    // A last line without `\n` is still a line, and is written with one.
    out = await run('cat', src, 'only');
    expect(out.stdout, 'only\n');
    // An empty input has no lines, so nothing is written.
    out = await run('cat', src, '');
    expect((out.status, out.stdout), (0, ''));
  });

  test('lines are numbered from one and CRLF is one line end', () async {
    const src =
        'main(stdin: Lines) -> (stdout: Lines) {\n  '
        'stdout <- "\${stdin[1]}|\${stdin[2]}|\${stdin[3] else "none"}";\n}\n';
    final out = await run('numbers', src, 'name: Ada\r\nrole: admin\r\n');
    expect(out.stdout, 'name: Ada|role: admin|none\n');
    expect(
      '${splitLines(utf8.encode('a\r\n\nb'))}',
      '{1 -> "a", 2 -> "", 3 -> "b"}',
      reason: 'an empty line in the middle is kept',
    );
  });

  test('a line that is not UTF-8 is an I/O error at its key', () {
    final lines = splitLines([...utf8.encode('ok\n'), 0xff, 0xfe, ...utf8.encode('\nfine\n')]);
    expect(lines, isA<Family>());
    final f = lines as Family;
    expect(f[const Int(1)], Str('ok'));
    expect(f[const Int(2)], const Atom('ioError'));
    expect(f[const Int(3)], Str('fine'));
  });

  test('a greeting reads one line and writes one', () async {
    const src =
        'main(stdin: Lines) -> (stdout: Lines) {\n  '
        'name = trim(stdin[1]) else "stranger";\n  '
        'stdout <- "Hello, \${name}!";\n}\n';
    expect((await run('greet', src, '  Grace \n')).stdout, 'Hello, Grace!\n');
    expect((await run('greet', src, '')).stdout, 'Hello, stranger!\n');
  });

  test('a computed line number reads that line', () async {
    // The first line says which later line to print; a key that is not a literal reads the
    // family by value, as a literal one does.
    const src =
        'main(stdin: Lines) -> (stdout: Lines) {\n  '
        'pick = int(stdin[1]) else 0;\n  '
        'stdout <- stdin[pick + 1] else "no such line";\n}\n';
    expect((await run('pick', src, '2\nred\ngreen\nblue\n')).stdout, 'green\n');
    expect((await run('pick', src, '9\nred\n')).stdout, 'no such line\n');
  });
}
