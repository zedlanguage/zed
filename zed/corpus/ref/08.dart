/// 08 percent-decoding fused with UTF-8 decoding: the two recurrences of the program, run in
/// order. hexVal of a character that is not a hex digit is 0 (indexOf gives #none, `else 0`).
/// A byte sequence cut short by a #char or by the end of the line is dropped; a stray
/// continuation byte is dropped; a byte expected as a continuation is taken as one whatever
/// its high bits are. Characters are code points. A decoded value above U+10FFFF, or a
/// surrogate, is not a character: the line fails.
library;

import 'dart:math' as math;

import 'zedrt.dart';

/// The value of hex digit [c] (either case), else 0, also for no character (null).
int hexVal(int? c) => switch (c) {
  final c? when c >= 0x30 && c <= 0x39 => c - 0x30,
  final c? when c >= 0x41 && c <= 0x46 => c - 0x41 + 10,
  final c? when c >= 0x61 && c <= 0x66 => c - 0x61 + 10,
  _ => 0,
};

sealed class Token {}

final class Byte extends Token {
  Byte(this.value);
  final int value;
}

final class Char extends Token {
  Char(this.code);
  final int code;
}

String decode(String line) {
  final s = line.runes.toList();
  final skip = <int>[];
  var prev = 0;
  for (final c in s) {
    final cur = c == 0x25 && prev == 0 ? 2 : math.max(prev - 1, 0);
    skip.add(cur);
    prev = cur;
  }
  int? at(int k) => k < s.length ? s[k] : null;
  final toks = <Token>[
    for (final (i, c) in s.indexed)
      if ((i > 0 ? skip[i - 1] : 0) == 0)
        c == 0x25 ? Byte(hexVal(at(i + 1)) * 16 + hexVal(at(i + 2))) : Char(c),
  ];
  final out = StringBuffer();
  void emit(int c) {
    if (c > 0x10FFFF || (c >= 0xD800 && c < 0xE000)) {
      throw RangeError('not a printable character: U+${c.toRadixString(16)}');
    }
    out.writeCharCode(c);
  }

  var (need, cp) = (0, 0);
  for (final tok in toks) {
    switch (tok) {
      case Char(:final code):
        (need, cp) = (0, 0);
        emit(code);
      case Byte(value: final b) when need == 0:
        if (b < 128) {
          emit(b);
        } else if (b < 192) {
          // a stray continuation byte
        } else if (b < 224) {
          (need, cp) = (1, b % 32);
        } else if (b < 240) {
          (need, cp) = (2, b % 16);
        } else {
          (need, cp) = (3, b % 8);
        }
      case Byte(value: final v):
        cp = cp * 64 + v % 64;
        if (need == 1) {
          emit(cp);
          (need, cp) = (0, 0);
        } else {
          need -= 1;
        }
    }
  }
  return out.toString();
}

void main(List<String> args) {
  for (final line in readLines(args[0])) {
    print(decode(line));
  }
}
