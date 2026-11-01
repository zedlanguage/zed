/// The binders of a unit, shared by the checker and elaboration.
library;

import 'dart:collection';

import '../ast.dart';
import '../resolve.dart';
import '../source.dart';

final class Tables {
  final Resolution res;

  /// Each binder, by its span and name.
  final ids = <(Span, String), Binder>{};

  /// Each function binder's declaration, at any depth.
  final funcs = <Binder, FunctionDef>{};

  /// The spans of each binder's uses, in text order.
  final usesOf = <Binder, List<Span>>{};

  Tables(List<Stmt> unit, this.res) {
    for (final b in res.binders) {
      ids[(b.span, b.name)] = b;
    }
    for (final (span, value) in res.uses.entries) {
      if (value case Bound(:final binders)) {
        for (final b in binders) {
          (usesOf[b] ??= []).add(span);
        }
      }
    }
    _collect(unit);
  }

  /// Records every function declaration of `unit` and of the blocks inside it. The walk keeps
  /// its own stack, since blocks nest as deep as the program.
  void _collect(List<Stmt> unit) {
    final todo = <Object>[...unit];
    while (todo.isNotEmpty) {
      switch (todo.removeLast()) {
        case FunctionDef f:
          if (ids[(f.span, f.name)] case final b?) funcs[b] = f;
          todo
            ..addAll([for (final p in f.params) ?p.fallback])
            ..add(f.body);
        case Bind(:final value) || Push(:final value):
          todo.add(value);
        case Return(:final values):
          todo.addAll(values);
        case Block(:final stmts):
          todo.addAll(stmts);
        case StrLit(:final parts):
          todo.addAll([
            for (final p in parts)
              if (p case StrHole(:final e)) e,
          ]);
        case Unary(:final e) || Member(of: final e) || Is(of: final e):
          todo.add(e);
        case Binary(:final a, :final b):
          todo.addAll([a, b]);
        case Index(:final e, :final key):
          todo.addAll([e, key]);
        case Call(:final callee, :final positional, :final named):
          todo
            ..add(callee)
            ..addAll(positional)
            ..addAll([for (final (_, a) in named) a]);
        case Tuple(:final items):
          todo.addAll(items);
        case Lambda(:final body):
          todo.add(body);
        case Else(:final of, :final fallback):
          todo.addAll([of, fallback]);
        case If(:final cond, :final then, :final otherwise):
          todo.addAll([cond, then, otherwise]);
      }
    }
  }

  Binder id(Span span, String name) => ids[(span, name)]!;

  /// The binders used in `span`, outside the spans in `skip`, in text order.
  Iterable<Binder> usesIn(Span span, [List<Span> skip = const []]) sync* {
    for (final (u, ref) in res.uses.from((start: span.start, end: -1))) {
      if (u.start >= span.end) break;
      if (u.end > span.end) continue;
      if (skip.any((s) => s.start <= u.start && u.end <= s.end)) continue;
      if (ref case Bound(:final binders)) yield* binders;
    }
  }

  List<Binder> bindersOf(Stmt s) => switch (s) {
    Bind(:final targets) => [
      for (final t in targets)
        if (t != null) id(s.span, t),
    ],
    FunctionDef(:final name) => [id(s.span, name)],
    Push() || Return() => [],
  };

  /// The order the statements of one scope are bound in, each after those it uses, a
  /// function's `test` tables aside; else, as the second item, the statements of one cycle.
  /// Each use of a binder of the scope is placed in its statement by a binary search, so the
  /// order reads the uses of the scope's own binders only, not those of the scopes inside it.
  (List<int>, List<int>?) order(List<Stmt> items) {
    final deps = [for (final _ in items) SplayTreeSet<int>()];
    for (final (j, s) in items.indexed) {
      for (final b in bindersOf(s)) {
        for (final u in usesOf[b] ?? const <Span>[]) {
          final i = lastWhere(items.length, (i) => items[i].span.start <= u.start);
          if (i < 0 || u.end > items[i].span.end) continue;
          if (items[i] case FunctionDef(:final tests) when _inTests(tests, u)) continue;
          deps[i].add(j);
        }
      }
    }
    return topo([for (final d in deps) d.toList()]);
  }
}

/// Whether `u` lies in one of the `test` cases, which are in text order.
bool _inTests(List<(Expr, Expr)> tests, Span u) {
  final i = lastWhere(tests.length, (i) => tests[i].$1.span.start <= u.start);
  return i >= 0 && u.end <= tests[i].$2.span.end;
}

/// The last `i` below `n` for which `ok(i)` holds, `ok` holding on a prefix; -1 for none.
int lastWhere(int n, bool Function(int) ok) {
  var (lo, hi) = (0, n);
  while (lo < hi) {
    final mid = (lo + hi) >> 1;
    if (ok(mid)) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return lo - 1;
}

/// An order of `0..deps.length` with each item after its dependencies (each list ascending),
/// the least ready item first; else the items of one cycle, in order along it.
(List<int>, List<int>?) topo(List<List<int>> deps) {
  final n = deps.length;
  final waiting = [for (final d in deps) d.length];
  final users = [for (final _ in deps) <int>[]];
  for (final (i, d) in deps.indexed) {
    for (final j in d) {
      users[j].add(i);
    }
  }
  final ready = SplayTreeSet<int>()
    ..addAll([
      for (var i = 0; i < n; i++)
        if (waiting[i] == 0) i,
    ]);
  final order = <int>[];
  final done = List.filled(n, false);
  while (ready.isNotEmpty) {
    final i = ready.first;
    ready.remove(i);
    done[i] = true;
    order.add(i);
    for (final u in users[i]) {
      if (--waiting[u] == 0) ready.add(u);
    }
  }
  if (order.length == n) return (order, null);
  // Every item left waits on another left; walk from the least until one repeats.
  final at = <int, int>{};
  final path = <int>[];
  var i = done.indexOf(false);
  while (!at.containsKey(i)) {
    at[i] = path.length;
    path.add(i);
    i = deps[i].firstWhere((d) => !done[d]);
  }
  return (order, path.sublist(at[i]!));
}
