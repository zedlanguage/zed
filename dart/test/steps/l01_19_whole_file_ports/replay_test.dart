/// The replay harness: `--record` saves every input the wave read, and `zedc replay` runs the
/// wave again from the record alone.
library;

import 'dart:collection';
import 'dart:convert';
import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/run.dart';

import 'ports.dart';

/// The error `f` throws, or a failure when it throws none.
String error(void Function() f) {
  try {
    f();
  } on RunError catch (e) {
    return e.message;
  }
  fail('no error');
}

void main() {
  test('a replay reads the record, not the world', () async {
    final d = dir('replay').path;
    final prices = File('$d/prices.txt')..writeAsStringSync('4\n');
    final rec = '$d/wave.rec';
    final src =
        'main(stdin: Lines, fs: Files) -> (stdout: Lines) {\n  '
        'unit = int(trim(fs["${prices.path}"])) else 0;\n  qty = int(stdin[1]) else 0;\n  '
        'stdout <- "total \${unit * qty}";\n}\n';
    var out = await run('replay', src, '3\n', ['--record', rec]);
    expect((out.status, out.stdout), (0, 'total 12\n'));
    // The world changes; the replay still sees the wave as recorded.
    prices.writeAsStringSync('100\n');
    out = await zedc(['replay', '$d/prog.zed', rec], '999\n');
    expect((out.status, out.stdout), (0, 'total 12\n'));
    // A fresh run sees the new world.
    expect((await run('replay', src, '3\n')).stdout, 'total 300\n');
  });

  test('a read the record lacks stops the replay', () {
    final p = load(
      'main(fs: Files) -> (stdout: Lines) {\n  stdout <- fs["a.txt"] else "-";\n}\n'.codeUnits,
    );
    expect(error(() => p.replay(Record())), 'port `fs`: the record holds no read of "a.txt"');
  });

  test('a record round-trips any bytes', () {
    final record = Record();
    record.files['fs'] = SplayTreeMap.of({
      Str('dir/with space\nand newline'): Str('x\n\ny'),
      Str('gone.txt'): const Atom('notFound'),
      Str('locked'): const Atom('ioError'),
    });
    record.lines['stdin'] = [0xff, ...utf8.encode(' 12 34\n\n')];
    final bytes = record.toBytes();
    expect(
      utf8.decode(bytes.sublist(0, 30), allowMalformed: true),
      startsWith('zed record 1\nlines 5 9\nstdin'),
    );
    final back = Record.fromBytes(bytes);
    expect(back.lines, record.lines);
    expect(back.files, record.files);
    expect(back.toBytes(), bytes);
  });

  test('a damaged record is rejected', () {
    final good = utf8.encode('zed record 1\nlines 5 3\nstdinab\n\n');
    expect(Record.fromBytes(good).lines['stdin'], utf8.encode('ab\n'));
    for (final bad in [
      'zed record 2\n',
      'zed record 1\nlines 5 9\nstdinab\n\n',
      'zed record 1\nlines 5 3\nstdinab\n',
      'zed record 1\nsocket 1\nx\n',
      'zed record 1\nmissing 2 1 4\nfsa\n',
    ]) {
      expect(error(() => Record.fromBytes(utf8.encode(bad))), 'not a Zed record', reason: bad);
    }
  });
}
