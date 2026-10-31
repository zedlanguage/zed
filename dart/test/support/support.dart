/// Shared helpers for the step tests in `test/steps/`.
///
/// Each step of DESIGN.md Part G has one folder, `test/steps/<step>/`, holding that step's
/// tests and, in `expected/`, the expected outputs those tests compare against.
library;

import 'dart:io';

import 'package:test/test.dart';

/// The root of the Dart package: the nearest folder above the working one with a
/// `pubspec.yaml`.
final Directory packageDir = () {
  var d = Directory.current.absolute;
  while (!File('${d.path}/pubspec.yaml').existsSync()) {
    d = d.parent;
  }
  return d;
}();

/// The folder that holds every step folder.
final Directory stepsDir = Directory('${packageDir.path}/test/steps');

final _stage = RegExp(r'^(m0|s|l(0[1-9]|1[0-9]|2[0-9]))$');
final _desc = RegExp(r'^[a-z0-9]([a-z0-9_]*[a-z0-9])?$');

/// Whether `name` is a well-formed step-folder name: a stage (`m0`, `l01`…`l29`, or `s` for
/// the self-hosting row), the two-digit step number within the stage, and a short lowercase
/// description, joined by underscores (`l01_07_fences`).
bool isStepName(String name) {
  final parts = name.split('_');
  if (parts.length < 3) return false;
  final step = parts[1];
  final desc = parts.sublist(2).join('_');
  return _stage.hasMatch(parts[0]) &&
      RegExp(r'^\d\d$').hasMatch(step) &&
      int.parse(step) >= 1 &&
      _desc.hasMatch(desc);
}

/// The expected output `test/steps/<step>/expected/<name>.txt`, without its final newline.
String expectedOutput(String step, String name) =>
    File('${stepsDir.path}/$step/expected/$name.txt')
        .readAsStringSync()
        .replaceFirst(RegExp(r'\n$'), '');

/// Checks `actual` against the expected output `name` of `step`.
void expectOutput(String step, String name, String actual) {
  expect(actual, expectedOutput(step, name), reason: 'expected output $step/$name');
}
