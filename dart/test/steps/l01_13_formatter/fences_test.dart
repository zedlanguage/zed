/// The formatter's standing rule (DESIGN.md, step L1.13) over the documentation's fences and the
/// corpus: every unit that builds is formatted, and the result builds to the same statements,
/// keeps its comments, and formats to itself.
library;

import 'dart:io';

import 'package:test/test.dart';

import '../../support/fences.dart' as fences;
import '../../support/support.dart';
import 'fmt.dart';

/// Whether `text` builds.
bool builds(String text) {
  try {
    build(text);
    return true;
  } on Exception {
    return false;
  }
}

void main() {
  test('every unit that builds formats to a fixed point', () {
    var formatted = 0;
    for (final f in fences.all().where((f) => !f.notation)) {
      if (builds(f.text)) {
        try {
          fmt(f.text);
        } on TestFailure catch (e) {
          fail('fence at ${f.at}:\n${f.text}\n$e');
        }
        formatted++;
      }
    }
    // 23 at step L1.13; later steps build more.
    expect(formatted, greaterThanOrEqualTo(23));
  });

  test('every corpus program that builds formats to a fixed point', () {
    final formatted = <String>[];
    final files = Directory('${packageDir.parent.path}/zed/corpus').listSync().whereType<File>();
    for (final file in files.where((f) => f.path.endsWith('.zed'))) {
      final text = file.readAsStringSync();
      if (builds(text)) {
        // The corpus is written in the formatter's layout.
        expect(fmt(text), text, reason: file.path);
        formatted.add(file.path);
      }
    }
    // One at step L1.13; later steps build more.
    expect(formatted, isNotEmpty, reason: 'no corpus program builds');
  });
}
