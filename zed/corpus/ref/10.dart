/// 10 HH:MM matcher. The output is the language of ([01][0-9]|2[0-3]):[0-5][0-9] from a
/// regular expression (Dart's RegExp, anchored at both ends); the script also runs the
/// program's own algorithm (Brzozowski derivatives, transcribed from
/// 10-regex-matcher/regex.zed) and stops if the two disagree on any line.
library;

import 'zedrt.dart';

sealed class Re {
  const Re();
}

final class Void extends Re {
  const Void();
}

final class Eps extends Re {
  const Eps();
}

final class Lit extends Re {
  const Lit(this.c);
  final int c;
}

final class Range extends Re {
  const Range(this.lo, this.hi);
  final int lo, hi;
}

final class Seq extends Re {
  const Seq(this.a, this.b);
  final Re a, b;
}

final class Alt extends Re {
  const Alt(this.a, this.b);
  final Re a, b;
}

final class Star extends Re {
  const Star(this.a);
  final Re a;
}

bool nullable(Re r) => switch (r) {
  Void() || Lit() || Range() => false,
  Eps() || Star() => true,
  Seq(:final a, :final b) => nullable(a) && nullable(b),
  Alt(:final a, :final b) => nullable(a) || nullable(b),
};

Re deriv(Re r, int ch) => switch (r) {
  Void() || Eps() => const Void(),
  Lit(:final c) => c == ch ? const Eps() : const Void(),
  Range(:final lo, :final hi) => lo <= ch && ch <= hi ? const Eps() : const Void(),
  Seq(:final a, :final b) when nullable(a) => Alt(Seq(deriv(a, ch), b), deriv(b, ch)),
  Seq(:final a, :final b) => Seq(deriv(a, ch), b),
  Alt(:final a, :final b) => Alt(deriv(a, ch), deriv(b, ch)),
  Star(:final a) => Seq(deriv(a, ch), r),
};

bool matches(Re r, String s) => nullable(s.runes.fold(r, deriv));

Range rng(String a, String b) => Range(a.codeUnitAt(0), b.codeUnitAt(0));

void main(List<String> args) {
  final hhmm = Seq(
    Alt(Seq(rng('0', '1'), rng('0', '9')), Seq(Lit('2'.codeUnitAt(0)), rng('0', '3'))),
    Seq(Lit(':'.codeUnitAt(0)), Seq(rng('0', '5'), rng('0', '9'))),
  );
  final pat = RegExp(r'^(?:[01][0-9]|2[0-3]):[0-5][0-9]$');
  for (final line in readLines(args[0])) {
    final ok = pat.hasMatch(line);
    if (ok != matches(hhmm, line)) throw StateError('regex and derivatives disagree: $line');
    print('${ok ? 'yes ' : 'no '}$line');
  }
}
