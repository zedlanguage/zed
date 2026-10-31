/// Step M0.1: repository scaffolding.
///
/// The step folders are the index the user documentation is built from, so their names are
/// checked here, and the folders are checked against the step index in `expected/`: every
/// folder is a step of the index, and once every step is built the two are the same.
library;

import 'dart:io';

import 'package:test/test.dart';

import '../../support/support.dart';

List<String> folders(String path) =>
    (Directory(path)
        .listSync()
        .whereType<Directory>()
        .map((d) => d.uri.pathSegments.reversed.skip(1).first)
        .toList()
      ..sort());

void main() {
  final index = expectedOutput('m0_01_scaffolding', 'step_index').split('\n');

  test('every step folder is well named', () {
    for (final name in folders(stepsDir.path)) {
      expect(isStepName(name), isTrue, reason: 'badly named step folder: test/steps/$name');
    }
  });

  test('every step folder is in the step index, which is sorted and has no repeats', () {
    expect(index.toSet().containsAll(folders(stepsDir.path)), isTrue);
    expect(index, [...index]..sort());
    expect(index.toSet().length, index.length);
  });
}
