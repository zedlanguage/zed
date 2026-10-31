/// Source loading (DESIGN.md sec:lexical; step L1.1): a file's bytes become the text the lexer
/// reads, or are rejected with a span.
///
/// The file must be UTF-8 in Normalization Form C. A file that is not NFC is rejected rather
/// than normalized, since two spellings that look the same must not hash differently. A
/// leading byte order mark is rejected for the same reason. Line endings normalize to `\n`:
/// `\r\n` and a lone `\r` are each one line break.
///
/// A span is a byte range of the file as read. Every rejection happens before the line endings
/// are normalized, so its span indexes the bytes the author has.
library;

import 'src/unicode.dart';

/// A byte range of the file as read: `start` up to `end`, which is one past the last byte.
typedef Span = ({int start, int end});

/// Why a file was rejected.
sealed class Reject implements Exception {
  /// The span of the rejection.
  final Span span;

  const Reject(this.span);

  /// The rejection as `line:column: message`, with the position of its span's start in
  /// `bytes`, the file it was found in; a UTF-8 rejection shows the bytes in hexadecimal.
  String render(List<int> bytes) {
    final (line, col) = lineCol(bytes, span.start);
    return switch (this) {
      NotUtf8() =>
        '$line:$col: $this: '
            '${[for (final b in bytes.sublist(span.start, span.end)) _hex(b, 2)].join(' ')}',
      _ => '$line:$col: $this',
    };
  }
}

/// The bytes at `span` are not UTF-8: an invalid or overlong sequence, an encoded surrogate, or
/// a sequence cut off by the end of the file. The span is the first invalid sequence.
final class NotUtf8 extends Reject {
  const NotUtf8(super.span);

  @override
  String toString() => 'not UTF-8';
}

/// The file starts with a byte order mark; the span is its three bytes.
final class ByteOrderMark extends Reject {
  const ByteOrderMark(super.span);

  @override
  String toString() => 'the file starts with a byte order mark';
}

/// The characters at `span`, the first sequence that NFC changes, are not in NFC; `nfc` is
/// their NFC spelling.
final class NotNfc extends Reject {
  final String nfc;

  const NotNfc(super.span, this.nfc);

  @override
  String toString() =>
      'not in Unicode Normalization Form C; '
      'write ${nfc.runes.map((c) => 'U+${_hex(c, 4)}').join(' ')}';
}

String _hex(int n, int width) => n.toRadixString(16).toUpperCase().padLeft(width, '0');

/// The text of a file: its bytes checked and its line endings normalized. Throws a [Reject].
String load(List<int> bytes) {
  final (cps, at) = _decode(bytes);
  if (cps.isNotEmpty && cps[0] == 0xfeff) throw const ByteOrderMark((start: 0, end: 3));
  if (!isNfc(cps)) {
    final (i, j) = _firstNotNfc(cps);
    throw NotNfc((start: at[i], end: at[j]), String.fromCharCodes(nfc(cps.sublist(i, j))));
  }
  return String.fromCharCodes(cps).replaceAll('\r\n', '\n').replaceAll('\r', '\n');
}

/// The code points of `bytes`, with the offset of each and, last, the length; or a [NotUtf8]
/// naming the first invalid sequence: its valid prefix and the next byte, or the rest of the
/// file when the end cuts a valid prefix off.
(List<int>, List<int>) _decode(List<int> bytes) {
  final cps = <int>[], at = <int>[];
  for (var i = 0; i < bytes.length;) {
    final b = bytes[i];
    // The number of bytes, the bits of the lead byte, and the range of the second byte.
    final (n, bits, lo, hi) = switch (b) {
      < 0x80 => (1, b, 0, 0),
      >= 0xc2 && < 0xe0 => (2, b & 0x1f, 0x80, 0xbf),
      0xe0 => (3, b & 0x0f, 0xa0, 0xbf),
      0xed => (3, b & 0x0f, 0x80, 0x9f),
      >= 0xe1 && < 0xf0 => (3, b & 0x0f, 0x80, 0xbf),
      0xf0 => (4, b & 0x07, 0x90, 0xbf),
      >= 0xf1 && < 0xf4 => (4, b & 0x07, 0x80, 0xbf),
      0xf4 => (4, b & 0x07, 0x80, 0x8f),
      _ => (0, 0, 0, 0),
    };
    if (n == 0) throw NotUtf8((start: i, end: i + 1));
    var c = bits;
    for (var k = 1; k < n; k++) {
      if (i + k == bytes.length) throw NotUtf8((start: i, end: bytes.length));
      final (l, h) = k == 1 ? (lo, hi) : (0x80, 0xbf);
      final x = bytes[i + k];
      if (x < l || x > h) throw NotUtf8((start: i, end: i + k));
      c = c << 6 | x & 0x3f;
    }
    cps.add(c);
    at.add(i);
    i += n;
  }
  at.add(bytes.length);
  return (cps, at);
}

/// The first sequence of `cps` that NFC changes, for code points that are not NFC, as a range
/// of indexes. The text is cut before each code point of combining class 0. NFC changes text
/// only within one piece or across the boundary of two adjacent pieces (two such code points
/// that compose, as Hangul jamo do), so the span is the first piece that is not NFC, or the
/// first pair of pieces that is not, whichever ends first.
(int, int) _firstNotNfc(List<int> cps) {
  final cuts = [
    for (var i = 0; i < cps.length; i++)
      if (i == 0 || combiningClass(cps[i]) == 0) i,
    cps.length,
  ];
  for (var i = 0; i < cuts.length - 1; i++) {
    if (!isNfc(cps.sublist(cuts[i], cuts[i + 1]))) return (cuts[i], cuts[i + 1]);
    if (i > 0 && !isNfc(cps.sublist(cuts[i - 1], cuts[i + 1]))) return (cuts[i - 1], cuts[i + 1]);
  }
  throw StateError('text that is not NFC has a piece or a pair of pieces that is not');
}

/// The 1-based line and column of byte `offset` of `bytes`, the column counted in Unicode
/// scalars. `\r\n`, `\r` and `\n` each end a line. The bytes before `offset` must be UTF-8, as
/// they are for the start of every rejection's span. For many offsets in one text, make its
/// [Lines] once.
(int, int) lineCol(List<int> bytes, int offset) =>
    Lines(bytes.sublist(0, offset)).lineCol(bytes, offset);

/// Where the lines of a text start, found once, so that the line and column of an offset cost
/// a binary search and a count of the scalars before it on its line, not a decoding of the
/// text up to it.
final class Lines {
  /// The byte offsets after a line break, each with the 1-based number of the line it starts,
  /// in increasing order, beginning with `(0, 1)`. Inside a `\r\n` both the offset after `\r`
  /// and the one after `\n` start the next line.
  final List<(int, int)> _starts = [(0, 1)];

  /// The line starts of `bytes`.
  Lines(List<int> bytes) {
    for (var i = 0; i < bytes.length; i++) {
      final line = _starts.last.$2;
      switch (bytes[i]) {
        case 0x0a when i > 0 && bytes[i - 1] == 0x0d:
          _starts.add((i + 1, line));
        case 0x0a || 0x0d:
          _starts.add((i + 1, line + 1));
      }
    }
  }

  /// The start of the line holding byte `offset`, and that line's number.
  (int, int) lineStart(int offset) {
    var (lo, hi) = (0, _starts.length);
    while (lo < hi) {
      final mid = (lo + hi) >> 1;
      if (_starts[mid].$1 <= offset) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return _starts[lo - 1];
  }

  /// The 1-based line and column of byte `offset` of `bytes`, the text these are the lines of;
  /// the bytes of its line before `offset` must be UTF-8.
  (int, int) lineCol(List<int> bytes, int offset) {
    final (start, line) = lineStart(offset);
    // A scalar is a byte that is not a continuation byte.
    var col = 1;
    for (var i = start; i < offset; i++) {
      if (bytes[i] & 0xc0 != 0x80) col++;
    }
    return (line, col);
  }
}
