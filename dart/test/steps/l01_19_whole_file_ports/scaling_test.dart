/// Whole-file ports at the rule of low complexity (DESIGN.md Part G).
library;

import 'dart:collection';
import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/run.dart';

import '../../support/scaling.dart' as scaling;

/// A `Files` port whose every path holds its own name.
final class Echo implements Lookup {
  @override
  Value get(Value key) => key;
}

void main() {
  test('a long `Lines` input is split and joined in linear time', () {
    final inputs = <int, List<int>>{};
    List<int> input(int n) =>
        inputs[n] ??= utf8.encode([for (var i = 0; i < n; i++) 'line $i\r\n'].join());
    scaling.check('n lines split and joined', 20000, (n) {
      expect(joinLines('stdout', splitLines(input(n))).length, input(n).length - n);
    });
  });

  test('a wave reading the last of many lines scales', () {
    final programs = <int, Program>{};
    Program last(int n) => programs[n] ??= load(
      'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin[$n] else "";\n}\n'.codeUnits,
    );
    final inputs = <int, List<int>>{};
    List<int> input(int n) =>
        inputs[n] ??= utf8.encode([for (var i = 0; i < n; i++) 'line $i\r\n'].join());
    for (final n in [20000, scaling.factor * 20000]) {
      last(n);
      input(n);
    }
    scaling.check('a wave of n lines', 20000, (n) {
      final wave = last(n).run({'stdin': input(n)}, (_) => Echo());
      expect(utf8.decode(wave.writes.single.$2), 'line ${n - 1}\n');
    });
  });

  test('a record of many reads is written and read back in linear time', () {
    final records = <int, Record>{};
    Record record(int n) => records[n] ??= Record()
      ..files['fs'] = SplayTreeMap.of({
        for (var i = 0; i < n; i++) Str('dir/file$i.txt'): Str('contents $i\n'),
      });
    scaling.check('a record of n reads', 20000, (n) {
      final bytes = record(n).toBytes();
      expect(Record.fromBytes(bytes).files['fs']!.length, n);
    });
  });

  test('a wave reading many distinct paths scales', () {
    String src(int n) => [
      'main(fs: Files) -> (stdout: Lines) {\n',
      for (var i = 0; i < n; i++) '  a$i = fs["p$i"];\n',
      '  stdout <- a0 else "";\n}\n',
    ].join();
    final programs = <int, Program>{};
    scaling.check('a wave reading n paths', 2000, (n) {
      final wave = (programs[n] ??= load(src(n).codeUnits)).run({}, (_) => Echo());
      expect(wave.record.files['fs']!.length, n);
    });
  });
}
