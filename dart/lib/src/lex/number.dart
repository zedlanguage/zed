/// Number literals (steps L1.3 and L1.4):
///
/// ```peg
/// Number   = (Rational | Float | Integer) !XID_CONTINUE
/// Rational = (Float | Decimal) 'r'
/// Float    = Decimal '.' Decimal Exponent? | Decimal Exponent
/// Exponent = [eE] [+\-]? Decimal
/// Integer  = '0x' Hex ('_'? Hex)* | '0o' [0-7] ('_'? [0-7])* | '0b' [01] ('_'? [01])* | Decimal
/// Decimal  = [0-9] ('_'? [0-9])*
/// ```
///
/// A literal keeps its digits, with the `_` removed, and its base: its width is chosen later
/// from its use (sec:domains), so the lexer never rounds or overflows. A float or a rational
/// keeps its decimal text, and a rational is exact (`0.1r` is one tenth). A digit must follow
/// the `.`, so `5.double` and `1..10` begin with the integer. A number that runs into a
/// character that continues a name is one error over the number and that run, since no other
/// rule reads a token starting with a digit: `200ms`, `1__000`, `1_000_`, `0b102`, `0x`.
library;

import '../../lex.dart';
import '../unicode.dart';
import 'text.dart';

/// The end and token of the number starting at byte `pos` of `text`, if one starts there;
/// throws a [LexError] for a malformed number.
(int, Tok)? number(Text text, int pos) {
  final b = text.bytes;
  int at(int i) => i < b.length ? b[i] : -1;
  if (!_digit(at(pos), 10)) return null;
  var radix = 10;
  for (final (p, r) in [(0x78, 16), (0x6f, 8), (0x62, 2)]) {
    if (at(pos) == 0x30 && at(pos + 1) == p && _digit(at(pos + 2), r)) radix = r;
  }
  final start = radix == 10 ? pos : pos + 2;
  var end = _digits(at, start, radix);
  final intEnd = end;
  if (radix == 10) {
    if (at(end) == 0x2e && _digit(at(end + 1), 10)) end = _digits(at, end + 1, 10);
    if (at(end) == 0x65 || at(end) == 0x45) {
      final sign = at(end + 1) == 0x2b || at(end + 1) == 0x2d ? 1 : 0;
      if (_digit(at(end + 1 + sign), 10)) end = _digits(at, end + 1 + sign, 10);
    }
  }
  final rational = radix == 10 && at(end) == 0x72;
  final after = end + (rational ? 1 : 0);
  if (after < text.length && isXidContinue(text.charAt(after))) {
    throw _runOn(text, pos, after, radix);
  }
  final digits = text.slice(start, end).replaceAll('_', '');
  final Tok tok = rational
      ? Rat(digits)
      : end > intEnd
      ? Float(digits)
      : Int(radix, digits);
  return (after, tok);
}

/// Whether the byte `d` is a digit of base `radix`.
bool _digit(int d, int radix) => switch (d) {
  >= 0x30 && <= 0x39 => d - 0x30 < radix,
  >= 0x61 && <= 0x66 || >= 0x41 && <= 0x46 => radix == 16,
  _ => false,
};

/// The end of the digits of base `radix` starting at `pos`, a digit, with single `_` between.
int _digits(int Function(int) at, int pos, int radix) {
  var end = pos + 1;
  while (true) {
    if (_digit(at(end), radix)) {
      end++;
    } else if (at(end) == 0x5f && _digit(at(end + 1), radix)) {
      end += 2;
    } else {
      return end;
    }
  }
}

/// The error for a number from `pos` to `end` followed by a character continuing a name.
LexError _runOn(Text text, int pos, int end, int radix) {
  var run = end;
  while (run < text.length && isXidContinue(text.charAt(run))) {
    run += text.charLength(run);
  }
  final next = String.fromCharCode(text.charAt(end));
  final number = text.slice(pos, end);
  final base = radix == 2 ? 'a binary' : 'an octal';
  final String why;
  if ((next == 'e' || next == 'E') &&
      radix == 10 &&
      !number.contains('e') &&
      !number.contains('E')) {
    why = 'an exponent needs digits: `1e3`, `1e-3`';
  } else if (next == 'r' && radix != 10) {
    why = 'a rational is written in decimal: `16r`, not `0x10r`';
  } else if (next == '_') {
    why = '`_` goes only between two digits';
  } else if (radix == 10 && end == pos + 1 && number == '0' && 'xob'.contains(next)) {
    why = '`0$next` must be followed by a digit';
  } else if (radix < 10 && _digit(next.codeUnitAt(0), 10)) {
    why = '$next is not $base digit';
  } else {
    why = 'a number must not run into a name: `${text.slice(end, run)}`';
  }
  return LexError(BadNumber(why), (start: pos, end: run));
}
