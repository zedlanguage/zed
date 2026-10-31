/// 31 tiny typechecker, written independently of the Zed program's structure: a classic
/// recursive-descent-free RPN parser, a map symbol table with duplicate detection, and Kleene
/// iteration of the type equations from all-unknown. Diagnostics per declaration line, in the
/// check-name order cyclic, duplicate, malformed, type, unbound (code-point order of the
/// names); typings in name order (code-point).
library;

import 'zedrt.dart';

sealed class Expr {
  const Expr();
}

/// A missing operand, or a whole declaration that is malformed.
final class Bad extends Expr {
  const Bad();
}

final class Num extends Expr {
  const Num();
}

final class BoolLit extends Expr {
  const BoolLit();
}

final class Var extends Expr {
  const Var(this.name);
  final String name;
}

final class Add extends Expr {
  const Add(this.a, this.b);
  final Expr a, b;
}

final class Eq extends Expr {
  const Eq(this.a, this.b);
  final Expr a, b;
}

final class Cond extends Expr {
  const Cond(this.c, this.t, this.e);
  final Expr c, t, e;
}

enum Ty {
  integer('int'),
  boolean('bool'),
  error('error'),
  unknown('unknown');

  const Ty(this.label);
  final String label;
}

(String, Expr) parse(String l) {
  final w = l.split(' ');
  final st = <Expr>[];
  Expr pop() => st.isNotEmpty ? st.removeLast() : const Bad();
  for (final tok in w.skip(2)) {
    switch (tok) {
      case '+' || '==':
        final b = pop(), a = pop();
        st.add(tok == '+' ? Add(a, b) : Eq(a, b));
      case '?':
        final e = pop(), t = pop(), c = pop();
        st.add(Cond(c, t, e));
      case 'true' || 'false':
        st.add(const BoolLit());
      case _ when tryParseInt(tok) != null:
        st.add(const Num());
      case _:
        st.add(Var(tok));
    }
  }
  final ok = w.length > 1 && w[1] == '=' && st.length == 1;
  return (w[0], ok ? st[0] : const Bad());
}

/// The free variables of [e], left to right, with repeats.
List<String> fv(Expr e) => switch (e) {
  Var(:final name) => [name],
  Add(:final a, :final b) || Eq(:final a, :final b) => [...fv(a), ...fv(b)],
  Cond(:final c, :final t, :final e) => [...fv(c), ...fv(t), ...fv(e)],
  Bad() || Num() || BoolLit() => [],
};

Ty lift(Ty a, Ty b, Ty ok) => a == Ty.error || b == Ty.error
    ? Ty.error
    : a == Ty.unknown || b == Ty.unknown
    ? Ty.unknown
    : ok;

Ty infer(Expr e, Map<String, Ty> ty) => switch (e) {
  Num() => Ty.integer,
  BoolLit() => Ty.boolean,
  Var(:final name) => ty[name] ?? Ty.error,
  Bad() => Ty.error,
  Add(:final a, :final b) => switch ((infer(a, ty), infer(b, ty))) {
    (final x, final y) => lift(x, y, x == Ty.integer && y == Ty.integer ? Ty.integer : Ty.error),
  },
  Eq(:final a, :final b) => switch ((infer(a, ty), infer(b, ty))) {
    (final x, final y) => lift(x, y, x == y ? Ty.boolean : Ty.error),
  },
  Cond(:final c, :final t, :final e) => switch ((infer(c, ty), infer(t, ty), infer(e, ty))) {
    (final c, final a, final b) => lift(c, lift(a, b, a), c == Ty.boolean && a == b ? a : Ty.error),
  },
};

bool sameTypes(Map<String, Ty> x, Map<String, Ty> y) =>
    x.length == y.length && x.entries.every((e) => y[e.key] == e.value);

void main(List<String> args) {
  final decls = [
    for (final (i, l) in readLines(args[0]).indexed)
      switch (parse(l)) {
        (final name, final e) => (line: i + 1, name: name, e: e),
      },
  ];
  final lines = <String, List<int>>{};
  for (final d in decls) {
    lines.putIfAbsent(d.name, () => []).add(d.line);
  }
  final defn = {for (final d in decls) d.line: d.e};
  var ty = {for (final n in lines.keys) n: Ty.unknown};
  while (true) {
    final next = {
      for (final MapEntry(key: n, value: ls) in lines.entries)
        n: ls.length == 1 ? infer(defn[ls[0]]!, ty) : Ty.error,
    };
    if (sameTypes(next, ty)) break;
    ty = next;
  }
  for (final n in sortedByCodePoint(ty.keys)) {
    print('$n : ${ty[n]!.label}');
  }
  bool clean(String x) => lines[x]?.length == 1 && ty[x] != Ty.error;
  for (final (:line, :name, :e) in decls) {
    final ls = lines[name]!;
    final mine = ls.length == 1;
    final names = fv(e);
    final ub = names.where((x) => !lines.containsKey(x)).toList();
    if (mine && ty[name] == Ty.unknown) print('line $line: $name is cyclic');
    if (!mine && line != ls[0]) print('line $line: duplicate $name (first at line ${ls[0]})');
    if (e is Bad) print('line $line: malformed $name');
    if (mine && e is! Bad && ty[name] == Ty.error && names.every(clean)) {
      print('line $line: type error in $name');
    }
    if (ub.isNotEmpty) print('line $line: unbound ${ub.join(', ')}');
  }
}
