/// The text the lexer reads: the UTF-8 bytes of a loaded source text, read a code point at a
/// time, so that every position and span is a byte offset, as `source.dart` gives them.
library;

import 'dart:convert';
import 'dart:typed_data';

/// UTF-8 bytes known to be valid.
final class Text {
  final Uint8List bytes;

  Text(String text) : bytes = utf8.encode(text);

  Text._(this.bytes);

  /// The text up to byte `end`, sharing these bytes.
  Text prefix(int end) => Text._(Uint8List.sublistView(bytes, 0, end));

  int get length => bytes.length;

  /// The code point starting at byte `pos`, or -1 at the end.
  int charAt(int pos) {
    if (pos >= bytes.length) return -1;
    final b = bytes[pos];
    if (b < 0x80) return b;
    final n = charLength(pos);
    var c = b & (0x7f >> n);
    for (var i = 1; i < n; i++) {
      c = c << 6 | bytes[pos + i] & 0x3f;
    }
    return c;
  }

  /// The length in bytes of the code point starting at byte `pos`.
  int charLength(int pos) => switch (bytes[pos]) {
    < 0x80 => 1,
    < 0xe0 => 2,
    < 0xf0 => 3,
    _ => 4,
  };

  /// Whether `ascii`, ASCII text, starts at byte `pos`.
  bool startsWith(String ascii, int pos) {
    if (pos + ascii.length > bytes.length) return false;
    for (var i = 0; i < ascii.length; i++) {
      if (bytes[pos + i] != ascii.codeUnitAt(i)) return false;
    }
    return true;
  }

  /// The first position at or after `from` of the ASCII character `c`, or -1.
  int indexOf(String c, int from) => bytes.indexOf(c.codeUnitAt(0), from);

  /// The text from byte `start` to byte `end`.
  String slice(int start, int end) => utf8.decode(Uint8List.sublistView(bytes, start, end));
}
