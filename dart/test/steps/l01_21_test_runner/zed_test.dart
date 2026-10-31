/// The Zed-written tests of every step.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/testing.dart';

import '../../support/support.dart';

/// The units of every step's `zed/` folder, by path.
List<File> units() => [
  for (final step in stepsDir.listSync().whereType<Directory>())
    if (Directory('${step.path}/zed') case final dir when dir.existsSync())
      ...dir.listSync().whereType<File>(),
]..sort((a, b) => a.path.compareTo(b.path));

void main() {
  test('every Zed test of every step passes', () {
    var passed = 0;
    for (final file in units()) {
      for (final o in testUnit(file.readAsStringSync())) {
        expect(o.failure, isNull, reason: '${file.path}:${o.line}:${o.col}');
        passed++;
      }
    }
    // The four units of this step hold 22 rows; a runner that skipped them would pass the loop
    // above.
    expect(passed, greaterThanOrEqualTo(22));
  });
}
