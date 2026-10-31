/// The text of a string value. A string joined by `++` is kept as the node of its two parts,
/// made in `O(1)`, and is written out once, when it is first read as text; a string is still
/// compared, ordered and printed by its text alone (DESIGN.md: "ropes are a representation and
/// never enter identity"). Joining `n` pieces one at a time, as a `foldl` of `++` does, so
/// costs `O(n)` and keeps `O(n)` memory for all its accumulators, where copying both parts at
/// each join cost `O(n²)` for both.
library;

/// A join shorter than this, in UTF-16 code units, is written out at once.
const _short = 64;

/// A string's text: written out, or the join of two parts not yet written out.
final class Text implements Comparable<Text> {
  /// The length in UTF-16 code units.
  final int length;
  String? _flat;
  Text? _a, _b;

  Text(String s) : length = s.length, _flat = s;

  Text._join(Text a, Text b) : length = a.length + b.length, _a = a, _b = b;

  /// `a` followed by `b`.
  static Text join(Text a, Text b) {
    if (a.length == 0) return b;
    if (b.length == 0) return a;
    if (a.length + b.length <= _short) return Text(a.text + b.text);
    return Text._join(a, b);
  }

  /// The text, written out on first use; the parts are then let go.
  String get text => _flat ??= _writeOut();

  String _writeOut() {
    final out = StringBuffer();
    final todo = <Text>[this];
    while (todo.isNotEmpty) {
      final t = todo.removeLast();
      final flat = t._flat;
      if (flat != null) {
        out.write(flat);
      } else {
        todo
          ..add(t._b!)
          ..add(t._a!);
      }
    }
    _a = _b = null;
    return out.toString();
  }

  @override
  bool operator ==(Object other) =>
      identical(this, other) || other is Text && length == other.length && text == other.text;

  @override
  int get hashCode => text.hashCode;

  @override
  int compareTo(Text other) => identical(this, other) ? 0 : compareUtf8(text, other.text);

  @override
  String toString() => text;

  /// The text quoted and escaped as a string literal is written.
  String get quoted => quote(text);
}

/// Orders two strings by their UTF-8 bytes, which is the order of their code points. UTF-16
/// code units order differently only where a surrogate meets a unit at or above `0xE000`.
int compareUtf8(String a, String b) {
  final n = a.length < b.length ? a.length : b.length;
  for (var i = 0; i < n; i++) {
    final x = a.codeUnitAt(i), y = b.codeUnitAt(i);
    if (x != y) return _rank(x) - _rank(y);
  }
  return a.length - b.length;
}

int _rank(int u) => u >= 0xE000 ? u - 0x800 : (u >= 0xD800 ? u + 0x2000 : u);

/// `s` in double quotes, with `"`, `\`, the common control characters escaped by letter and
/// the other control characters as `\u{…}`.
String quote(String s) {
  final out = StringBuffer('"');
  for (final r in s.runes) {
    switch (r) {
      case 0x22:
        out.write(r'\"');
      case 0x5C:
        out.write(r'\\');
      case 0x0A:
        out.write(r'\n');
      case 0x0D:
        out.write(r'\r');
      case 0x09:
        out.write(r'\t');
      case 0x00:
        out.write(r'\0');
      case < 0x20 || 0x7F || (>= 0x80 && < 0xA0):
        out.write('\\u{${r.toRadixString(16)}}');
      default:
        out.writeCharCode(r);
    }
  }
  out.write('"');
  return out.toString();
}
