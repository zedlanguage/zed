/// The line and column of an offset, from the line starts found once ([Lines]), agree with
/// decoding the text from its first byte up to the offset.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/source.dart';

import '../../support/instances.dart';

/// The line and column of `offset` by decoding the bytes before it: the definition.
(int, int) decoded(List<int> bytes, int offset) {
  var (line, col) = (1, 1);
  final cs = utf8.decode(bytes.sublist(0, offset)).runes.toList();
  for (var i = 0; i < cs.length; i++) {
    switch (cs[i]) {
      case 0x0d when i + 1 < cs.length && cs[i + 1] == 0x0a:
        break;
      case 0x0d || 0x0a:
        (line, col) = (line + 1, 1);
      default:
        col++;
    }
  }
  return (line, col);
}

void main() {
  test('every offset is placed as decoding places it', () {
    final rng = Rng(0x11c0);
    const pieces = ['a', 'é', '€', '\n', '\r', '\r\n', '\n\r', '\r\r\n', '𝄞'];
    for (var t = 0; t < 200; t++) {
      final text = [for (var i = rng.below(30); i > 0; i--) rng.pick(pieces)].join();
      final bytes = utf8.encode(text);
      final lines = Lines(bytes);
      for (var offset = 0; offset <= bytes.length; offset++) {
        if (offset < bytes.length && bytes[offset] & 0xc0 == 0x80) continue;
        final want = decoded(bytes, offset);
        expect(lines.lineCol(bytes, offset), want, reason: '${jsonEncode(text)} at $offset');
        expect(lineCol(bytes, offset), want, reason: '${jsonEncode(text)} at $offset');
      }
    }
  });
}
