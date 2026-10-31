/// String literals (step L1.5):
///
/// ```peg
/// String   = '"""' (!'"""' Char)* '"""' | '"' (!'"' !'\n' Char)* '"'
/// Char     = Escape | Hole | !('\\' | '${') ANY
/// Escape   = '\\' ([ntr0\\"$] | 'u{' Hex+ '}')
/// Hole     = '${' HoleText '}'
/// HoleText = (String | Comment | '{' HoleText '}' | !'}' ANY)*
/// ```
///
/// A string is its parts: decoded text, and holes, each lexed into the tokens of its
/// expression. A `"` string has no line break, its holes included, so a `//` comment in a hole
/// of a one-line string is an error rather than a comment that swallows the `}`.
///
/// A `"""` string whose opening `"""` ends its line and whose closing `"""` begins its line
/// after spaces and tabs only is stripped of that indentation: the line breaks after the
/// opening and before the closing delimiter are dropped, each line loses the indentation, a line
/// of only spaces and tabs becomes empty, and a line indented less is an error. A line that
/// begins inside a hole is not a line of the string. Escapes are decoded after stripping, so
/// `\n` and `\t` are never stripped. Any other `"""` string is kept as written.
library;

import '../../lex.dart';
import 'comment.dart';
import 'text.dart';

/// What is known of the holes of one text, so that a hole nested in others is scanned once,
/// not once for each hole around it: the end of each hole found, by the position of its `${`,
/// and the positions of the text's line breaks.
final class Holes {
  final _ends = <int, int>{};
  final List<int> _breaks;

  Holes(Text text)
    : _breaks = [
        for (var i = 0; i < text.length; i++)
          if (text.bytes[i] == 0x0a) i,
      ];

  /// Whether the text from `from` to `to` holds a line break.
  bool _breaksIn(int from, int to) {
    final k = _firstAtLeast(_breaks, from);
    return k < _breaks.length && _breaks[k] < to;
  }
}

/// The first index of `sorted` whose value is at least `v`.
int _firstAtLeast(List<int> sorted, int v) {
  var (lo, hi) = (0, sorted.length);
  while (lo < hi) {
    final mid = (lo + hi) >> 1;
    if (sorted[mid] < v) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return lo;
}

/// A range of literal source text, before decoding.
typedef _Lit = (int, int);

/// The string starting at byte `pos` of a text, scanned up to each of its holes in turn, so
/// that whoever lexes the hole's tokens hands them back with [fill] and the scan goes on. The
/// lexer keeps the strings and holes it is inside on a stack, so that their depth is bounded by
/// memory alone. Throws a [LexError] for a malformed string.
final class StringScan {
  final Text text;
  final int pos;
  final Holes _holes;
  final String _close;

  /// The literal ranges, and the holes in their places.
  final _raw = <Object>[];
  int _i, _lit;

  /// The `${` and `}` of the hole whose tokens [fill] gives.
  (int, int)? _hole;

  /// The end and token of the string, once [next] has returned null.
  late final int end;
  late final Tok tok;

  StringScan(this.text, this.pos, this._holes)
    : _close = text.startsWith('"""', pos) ? '"""' : '"',
      _i = 0,
      _lit = 0 {
    _i = _lit = pos + _close.length;
  }

  /// Scans to the next hole, returning the range of its text, whose tokens go to [fill]; or to
  /// the end of the string, returning null and setting [end] and [tok].
  (int, int)? next() {
    final triple = _close.length == 3;
    while (!text.startsWith(_close, _i)) {
      if (text.startsWith(r'${', _i)) {
        _raw.add((_lit, _i));
        final close = _holeEnd(text, _i, !triple, _holes);
        _hole = (_i, close);
        return (_i + 2, close);
      }
      _i = _stringStep(text, pos, _i, triple);
    }
    _raw.add((_lit, _i));
    final content = pos + _close.length;
    final cuts = triple ? _strip(text, content, [..._raw.whereType<_Lit>()]) : <_Lit>[];
    end = _i + _close.length;
    tok = Str([
      for (final r in _raw)
        if (r is Hole)
          r
        else if (_decode(text, r as _Lit, cuts) case final s when s.isNotEmpty)
          TextPart(s),
    ]);
    return null;
  }

  /// Gives the tokens of the hole [next] returned.
  void fill(List<Token> tokens) {
    final (open, close) = _hole!;
    _raw.add(Hole(tokens, (start: open, end: close + 1)));
    _i = _lit = close + 1;
  }
}

/// The position after the character at `i` of the string starting at `pos`, a character that
/// neither closes the string nor opens a hole.
int _stringStep(Text text, int pos, int i, bool triple) => switch (text.charAt(i)) {
  -1 => throw _bad(pos, i, 'the string is not closed'),
  0x0a when !triple => throw _bad(
    pos,
    i,
    'a `"` string ends on its line; a string over several lines is written `"""`',
  ),
  0x5c => _escape(text, i),
  _ => i + text.charLength(i),
};

/// The end of the escape at `i`, a `\`.
int _escape(Text text, int i) {
  final next = text.charAt(i + 1);
  if (r'ntr0\"$'.codeUnits.contains(next)) return i + 2;
  if (next == 0x75) {
    var close = i + 3;
    if (text.startsWith('{', i + 2)) {
      while (close < text.length && _hex(text.bytes[close])) {
        close++;
      }
    }
    if (close > i + 3 && text.startsWith('}', close)) {
      final value = int.tryParse(text.slice(i + 3, close), radix: 16);
      if (value != null && value <= 0x10ffff && (value < 0xd800 || value > 0xdfff)) {
        return close + 1;
      }
      throw _bad(
        i,
        close + 1,
        'this is no Unicode scalar value: a code point is at most 10FFFF and not a surrogate '
        '(D800 to DFFF)',
      );
    }
    throw _bad(i, i + 2, r'a code point is written `\u{1F600}`');
  }
  throw _bad(
    i,
    i + 1 + (next < 0 ? 0 : text.charLength(i + 1)),
    r'no such escape; the escapes are \n \t \r \0 \\ \" \$ \u{…}',
  );
}

bool _hex(int b) => b >= 0x30 && b <= 0x39 || b >= 0x61 && b <= 0x66 || b >= 0x41 && b <= 0x46;

/// A hole the scan for a hole's end is inside: its `${`, whether its string is a `"` string,
/// and how many `{` in it are open.
final class _InHole {
  final int open;
  final bool oneLine;
  var depth = 0;
  _InHole(this.open, this.oneLine);
}

/// The position of the `}` closing the hole whose `${` is at `open`. The holes and strings
/// inside it are kept on a stack, so that their depth is bounded by memory alone, and the end of
/// each inner hole is kept in `holes`.
int _holeEnd(Text text, int open, bool oneLine, Holes holes) {
  if (holes._ends[open] case final end?) return end;
  // Each an [_InHole], or a string as its start and closing delimiter.
  final stack = <Object>[_InHole(open, oneLine)];
  for (var i = open + 2; ;) {
    switch (stack.last) {
      case final _InHole h:
        final int next;
        switch (text.charAt(i)) {
          case -1:
            throw _bad(h.open, i, r'the `${` hole is not closed');
          case 0x7d when h.depth == 0:
            holes._ends[h.open] = i;
            stack.removeLast();
            if (stack.isEmpty) return i;
            next = i + 1;
          case 0x7d:
            h.depth--;
            next = i + 1;
          case 0x7b:
            h.depth++;
            next = i + 1;
          case 0x22:
            final close = text.startsWith('"""', i) ? '"""' : '"';
            stack.add((i, close));
            i += close.length;
            continue;
          case 0x2f when h.oneLine && text.startsWith('//', i):
            final k = text.indexOf('\n', i);
            throw _bad(
              i,
              k < 0 ? text.length : k,
              'a `//` comment in a hole of a `"` string runs to the end of the line, past the '
              '`}`; write `/* … */`',
            );
          case 0x2f when comment(text, i) != null:
            next = comment(text, i)!;
          default:
            next = i + text.charLength(i);
        }
        if (h.oneLine && holes._breaksIn(i, next)) {
          throw _bad(h.open, i, 'a hole in a `"` string closes on its line');
        }
        i = next;
      case (final int pos, final String close):
        if (text.startsWith(close, i)) {
          // The string is one step of the hole around it.
          stack.removeLast();
          final h = stack.last as _InHole;
          final next = i + close.length;
          if (h.oneLine && holes._breaksIn(pos, next)) {
            throw _bad(h.open, pos, 'a hole in a `"` string closes on its line');
          }
          i = next;
        } else if (text.startsWith(r'${', i)) {
          if (holes._ends[i] case final end?) {
            i = end + 1;
          } else {
            stack.add(_InHole(i, close.length == 1));
            i += 2;
          }
        } else {
          i = _stringStep(text, pos, i, close.length == 3);
        }
    }
  }
}

/// Whether the bytes from `from` to `to` are all spaces and tabs.
bool _blank(Text text, int from, int to) {
  for (var k = from; k < to; k++) {
    if (text.bytes[k] != 0x20 && text.bytes[k] != 0x09) return false;
  }
  return true;
}

/// The ranges stripped from the literal text `lits` of a `"""` string whose text starts at
/// `content`, as the library comment describes, sorted.
List<_Lit> _strip(Text text, int content, List<_Lit> lits) {
  final (first, last) = (lits.first, lits.last);
  if (first.$1 != content || !text.startsWith('\n', content)) return [];
  var nl = last.$2 - 1;
  while (nl >= last.$1 && text.bytes[nl] != 0x0a) {
    nl--;
  }
  if (nl < last.$1 || !_blank(text, nl + 1, last.$2)) return [];
  final indent = last.$2 - (nl + 1);
  final cuts = <_Lit>[(content, content + 1), (nl, last.$2)];
  for (final (start, end) in lits) {
    for (var k = start; k < end && k < nl; k++) {
      if (text.bytes[k] != 0x0a) continue;
      // The line starting at `p`, in the literal text ending at `end`.
      final p = k + 1;
      var stop = text.indexOf('\n', p);
      if (stop < 0 || stop > end) stop = end;
      if (stop - p >= indent && _sameBytes(text, p, nl + 1, indent)) {
        cuts.add((p, p + indent));
      } else if (_blank(text, p, stop) && stop < end) {
        cuts.add((p, stop));
      } else {
        var ws = p;
        while (ws < stop && (text.bytes[ws] == 0x20 || text.bytes[ws] == 0x09)) {
          ws++;
        }
        throw _bad(p, ws, 'this line is indented less than the closing `"""`');
      }
    }
  }
  // The cuts do not overlap; in order, `_decode` passes each once.
  return cuts..sort((a, b) => a.$1 != b.$1 ? a.$1 - b.$1 : a.$2 - b.$2);
}

/// Whether the `n` bytes at `a` and at `b` are equal.
bool _sameBytes(Text text, int a, int b, int n) {
  for (var k = 0; k < n; k++) {
    if (text.bytes[a + k] != text.bytes[b + k]) return false;
  }
  return true;
}

/// The literal text `lit`, less the `cuts`, which are sorted and do not overlap, with its
/// escapes decoded.
String _decode(Text text, _Lit lit, List<_Lit> cuts) {
  final (start, end) = lit;
  // The first cut not ending at or before each character, found by search and then advanced.
  var next = 0;
  for (var (lo, hi) = (0, cuts.length); lo < hi;) {
    final mid = (lo + hi) >> 1;
    if (cuts[mid].$2 <= start) {
      lo = next = mid + 1;
    } else {
      hi = mid;
    }
  }
  final chars = <int>[];
  for (var p = start; p < end; p += text.charLength(p)) {
    while (next < cuts.length && cuts[next].$2 <= p) {
      next++;
    }
    if (!(next < cuts.length && cuts[next].$1 <= p)) chars.add(text.charAt(p));
  }
  final out = StringBuffer();
  for (var k = 0; k < chars.length; k++) {
    if (chars[k] != 0x5c) {
      out.writeCharCode(chars[k]);
      continue;
    }
    final c = chars[++k];
    switch (c) {
      case 0x6e:
        out.writeCharCode(0x0a);
      case 0x74:
        out.writeCharCode(0x09);
      case 0x72:
        out.writeCharCode(0x0d);
      case 0x30:
        out.writeCharCode(0);
      case 0x75:
        // `u{`, the digits, and `}`.
        var v = 0;
        for (k += 2; chars[k] != 0x7d; k++) {
          v = v * 16 + int.parse(String.fromCharCode(chars[k]), radix: 16);
        }
        out.writeCharCode(v);
      default:
        out.writeCharCode(c);
    }
  }
  return out.toString();
}

LexError _bad(int start, int end, String why) => LexError(BadString(why), (start: start, end: end));
