/// `zedc test <file> …`.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/testing.dart';

(int, String, String) run(List<String> args) {
  final (out, err) = (StringBuffer(), StringBuffer());
  final status = command(args, out, err);
  return (status, '$out', '$err');
}

late final Directory dir;

String unit(String name, String text) {
  final f = File('${dir.path}/$name')..writeAsStringSync(text);
  return f.path;
}

void main() {
  setUpAll(() => dir = Directory.systemTemp.createTempSync('zed-l01-21'));
  tearDownAll(() => dir.deleteSync(recursive: true));

  test('passing units exit 0 with the counts', () {
    final a = unit('pass.zed', 'double(positional x) = x * 2 test { 0 -> 0, 2 -> 4 }\n');
    expect(run([a, a]), (0, '4 passed, 0 failed\n', ''));
  });

  test('a failing check is printed at its file and line', () {
    final a = unit('fail.zed', 'double(positional x) = x * 2 test { 0 -> 0, 2 -> 5 }\n');
    expect(run([a]), (
      1,
      '$a:1:45: `2 -> 5` of `double`: the result is 4\n1 passed, 1 failed\n',
      '',
    ));
  });

  test('a file that is not UTF-8 fails, and a missing file is a usage error', () {
    final bad = '${dir.path}/bad.zed';
    File(bad).writeAsBytesSync([0xff, 0xfe]);
    final (status, out, _) = run([bad]);
    expect(status, 1);
    expect(out, startsWith('$bad: '));
    expect(out, endsWith('0 passed, 1 failed\n'));
    final (missing, _, err) = run(['/nonexistent/zed-l01-21.zed']);
    expect(missing, 2);
    expect(err, startsWith('/nonexistent/zed-l01-21.zed: '));
    expect(run([]), (2, '', 'usage: zedc test <file> …\n'));
  });
}
