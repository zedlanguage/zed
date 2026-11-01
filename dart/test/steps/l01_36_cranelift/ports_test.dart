/// The port runtime splits and joins lines exactly as the interpreter does, on every byte
/// string of a small alphabet that holds each case: an empty line, `\r\n`, a bare `\r`, a
/// missing last `\n`, a multibyte character and a byte that is not UTF-8.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/native.dart' as native;
import 'package:zed/run.dart' show joinLines, splitLines;

/// Every string over [alphabet] up to length [n], as bytes.
List<List<int>> strings(List<List<int>> alphabet, int n) {
  final out = <List<int>>[[]];
  var last = <List<int>>[[]];
  for (var i = 0; i < n; i++) {
    last = [
      for (final s in last)
        for (final a in alphabet) [...s, ...a],
    ];
    out.addAll(last);
  }
  return out;
}

void main() {
  test('lines split as the interpreter splits them', () {
    final alphabet = [
      [0x61],
      [0x0a],
      [0x0d],
      [0xff],
      utf8.encode('é'),
    ];
    final all = strings(alphabet, 6);
    expect(all.length, 19531);
    for (final s in all) {
      expect(native.lines(s), splitLines(s), reason: '$s');
    }
  });

  test('a push writes the bytes the interpreter writes', () {
    final pushes = <Value>[
      Str('x'),
      Str(''),
      Family.of([(Int(2), Str('b')), (Int(1), Str('a'))]),
      Family.of(const []),
      Int(1),
      Family.of([(Int(1), Int(7))]),
    ];
    for (final v in pushes) {
      Object out(List<int> Function() f) {
        try {
          return f();
        } catch (e) {
          return '$e';
        }
      }

      expect(out(() => native.write('out', v)), out(() => joinLines('out', v)), reason: '$v');
    }
  });
}
