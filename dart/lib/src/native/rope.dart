/// A rope (step L1.36): concatenation shares both sides and copies nothing, and a rope is
/// flattened to one string, once, when a primitive needs its text. Lengths are counted as
/// the language counts them: bytes of UTF-8, and characters (code points).
library;

/// An immutable string as a tree of shared pieces.
sealed class Rope {
  const Rope();

  /// The rope of one piece.
  factory Rope.leaf(String s) = _Leaf;

  /// [a] followed by [b], in constant time: neither side is copied.
  factory Rope.cat(Rope a, Rope b) {
    if (a.bytes == 0) return b;
    if (b.bytes == 0) return a;
    return _Cat(a, b);
  }

  /// The length in bytes of UTF-8.
  int get bytes;

  /// The length in characters, what `len` gives.
  int get chars;

  /// The text as one string. A piece is returned as it is; a concatenation is written out
  /// the first time it is asked for, its length in bytes added to the count [copied] keeps,
  /// and kept.
  String flat(void Function(int bytes) copied);
}

final class _Leaf extends Rope {
  final String text;
  @override
  final int bytes, chars;

  _Leaf._(this.text, this.bytes, this.chars);

  factory _Leaf(String s) {
    var (bytes, chars) = (0, 0);
    for (final c in s.runes) {
      chars++;
      bytes += c < 0x80
          ? 1
          : c < 0x800
          ? 2
          : c < 0x10000
          ? 3
          : 4;
    }
    return _Leaf._(s, bytes, chars);
  }

  @override
  String flat(void Function(int bytes) copied) => text;
}

final class _Cat extends Rope {
  final Rope left, right;
  @override
  final int bytes, chars;
  String? _flat;

  _Cat(this.left, this.right) : bytes = left.bytes + right.bytes, chars = left.chars + right.chars;

  @override
  String flat(void Function(int bytes) copied) {
    if (_flat case final s?) return s;
    // A list of pieces, not recursion, so a long chain of concatenations is no deeper on the
    // stack than a short one; a piece already written out is copied whole.
    final out = StringBuffer();
    final todo = <Rope>[this];
    while (todo.isNotEmpty) {
      switch (todo.removeLast()) {
        case _Leaf(:final text):
          out.write(text);
        case _Cat(_flat: final s?):
          out.write(s);
        case _Cat(:final left, :final right):
          todo
            ..add(right)
            ..add(left);
      }
    }
    copied(bytes);
    return _flat = out.toString();
  }
}
