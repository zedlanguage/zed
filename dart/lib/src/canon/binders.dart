/// Binder normalization: each local binder is renamed to its de Bruijn level, the number of
/// binders enclosing it, so that two terms that differ only in local names become one term.
///
/// The rule renames one binder per step: the first binder in preorder that still carries its
/// written name. Every binder before it in preorder is already canonical, so the binders
/// enclosing it are too, and no binder inside its scope is: the new name cannot be captured,
/// and a written binder of the same name inside the scope shadows the old name as before.
library;

import '../kernel/term.dart';

/// The canonical name of the binder at de Bruijn level `level`. It starts with U+0000, which no
/// written name contains: the lexer rejects the character in source text.
String levelName(int level) => '\u0000$level';

final _level = RegExp(r'^\u0000([0-9]+)$');

/// The level a canonical binder name stands for, or null for a written name.
int? levelOf(String name) => switch (_level.firstMatch(name)) {
  final m? => int.tryParse(m[1]!),
  null => null,
};

/// One rewrite: the first written binder in preorder renamed to its level, with its preorder
/// index and its written name for the hint facet. Null when every binder is canonical.
(Term, int, String)? step(Term t) {
  final (renamed, name) = _renameFirst(t, 0) ?? (null, '');
  if (renamed == null) return null;
  // The canonical binders are the binders before the renamed one in preorder, and it.
  return (renamed, _count(renamed) - written(renamed) - 1, name);
}

/// The binders that still carry their written names: the rank of the rule.
int written(Term t) {
  var n = 0;
  _eachBinder(t, (name) {
    if (levelOf(name) == null) n++;
  });
  return n;
}

int _count(Term t) {
  var n = 0;
  _eachBinder(t, (_) => n++);
  return n;
}

/// Calls `f` on the name of every binder of `t`, in preorder.
void _eachBinder(Term t, void Function(String) f) {
  switch (t) {
    case Lam(:final params, :final body):
      params.forEach(f);
      _eachBinder(body, f);
    case Let(:final name, :final value, :final body):
      _eachBinder(value, f);
      f(name);
      _eachBinder(body, f);
    case Match(:final scrutinee, :final arms):
      _eachBinder(scrutinee, f);
      for (final (p, arm) in arms) {
        patternBinds(p).forEach(f);
        _eachBinder(arm, f);
      }
    case Fam(:final domain, :final variable, :final body):
      _eachBinder(domain, f);
      f(variable);
      _eachBinder(body, f);
    case Fix(:final init, :final step, :final self, :final key, kind: Definedness()):
      _eachBinder(init, f);
      f(self);
      f(key);
      _eachBinder(step, f);
    default:
      for (final c in _children(t)) {
        _eachBinder(c, f);
      }
  }
}

/// The names a pattern binds, left to right.
List<String> patternBinds(Pattern p) {
  final out = <String>[];
  void go(Pattern p) {
    switch (p) {
      case BindP(:final name):
        out.add(name);
      case AtomP(args: final ps) || TupleP(items: final ps):
        ps.forEach(go);
      case FieldsP(:final fields):
        for (final (_, p) in fields) {
          go(p);
        }
      case WildP() || LitP() || AnyAtomP():
        break;
    }
  }

  go(p);
  return out;
}

/// The subterms of a term that binds nothing, in order.
List<Term> _children(Term t) => switch (t) {
  Lit() || Var() || PrimFn() || Read() => const [],
  App(:final f, :final args) => [f, ...args],
  PrimApp(:final args) => args,
  If(:final cond, :final then, :final orElse) => [cond, then, orElse],
  Reindex(:final family, :final kf, :final vf) => [family, kf, vf],
  Discard(:final family, :final sel) => [family, sel],
  Fold(:final family, :final op, :final identity) => [family, op, ?identity],
  Fix(:final init, :final step, kind: Lattice(:final join)) => [init, step, join],
  Fix(:final init, :final step) => [init, step],
  Gen(:final init, :final step, :final guard) => [init, step, guard],
  Push(:final value) => [value],
  Lam() || Let() || Match() || Fam() => throw StateError('the caller handles binding forms'),
};

/// `t` with each child replaced by `f(child)`, for a term that binds nothing.
Term _mapChildren(Term t, Term Function(Term) f) => switch (t) {
  Lit() || Var() || PrimFn() || Read() => t,
  App(f: final g, :final args) => App(f(g), [for (final a in args) f(a)]),
  PrimApp(:final prim, :final args) => PrimApp(prim, [for (final a in args) f(a)]),
  If(:final cond, :final then, :final orElse) => If(f(cond), f(then), f(orElse)),
  Reindex(:final family, :final kf, :final vf, :final witness) => Reindex(
    f(family),
    f(kf),
    f(vf),
    witness,
  ),
  Discard(:final family, :final sel) => Discard(f(family), f(sel)),
  Fold(:final family, :final op, :final identity, :final depth, :final ev) => Fold(
    f(family),
    f(op),
    identity == null ? null : f(identity),
    depth,
    ev,
  ),
  Fix(:final init, :final step, :final self, :final key, :final kind, :final ev) => Fix(
    f(init),
    f(step),
    self,
    key,
    switch (kind) {
      Lattice(:final join) => Lattice(f(join)),
      Definedness() => kind,
    },
    ev,
  ),
  Gen(:final init, :final step, :final guard, :final pos) => Gen(f(init), f(step), f(guard), pos),
  Push(:final port, :final value) => Push(port, f(value)),
  Lam() || Let() || Match() || Fam() => throw StateError('the caller handles binding forms'),
};

/// One group of names bound together, at levels `depth`, `depth + 1`, …, with its first
/// written name renamed.
final class _Renamed {
  /// The group with the name renamed.
  final List<String> names;

  /// The position of the renamed name in the group.
  final int at;

  /// Its written name.
  final String old;

  /// Whether a later name of the group binds the same written name, so that the renamed
  /// binder's scope holds none of its occurrences.
  final bool shadowed;

  _Renamed(this.names, this.at, this.old, this.shadowed);

  static _Renamed? of(List<String> names, int depth) {
    final at = names.indexWhere((x) => levelOf(x) == null);
    if (at < 0) return null;
    final old = names[at];
    return _Renamed(
      [...names]..[at] = levelName(depth + at),
      at,
      old,
      names.skip(at + 1).contains(old),
    );
  }

  String get level => names[at];

  /// The scope `body` with the renamed binder's occurrences renamed.
  Term scope(Term body) => shadowed ? body : _rename(body, old, level);
}

/// Renames the first written binder in preorder at binder depth `depth`. Returns the new term
/// and the binder's written name.
(Term, String)? _renameFirst(Term t, int depth) {
  switch (t) {
    case Lam(:final params, :final body):
      if (_Renamed.of(params, depth) case final r?) return (Lam(r.names, r.scope(body)), r.old);
      if (_renameFirst(body, depth + params.length) case (final b, final old)) {
        return (Lam(params, b), old);
      }
      return null;
    case Let(:final name, :final value, :final body):
      if (_renameFirst(value, depth) case (final e, final old)) return (Let(name, e, body), old);
      if (levelOf(name) == null) {
        final level = levelName(depth);
        return (Let(level, value, _rename(body, name, level)), name);
      }
      if (_renameFirst(body, depth + 1) case (final b, final old)) {
        return (Let(name, value, b), old);
      }
      return null;
    case Match(:final scrutinee, :final arms):
      if (_renameFirst(scrutinee, depth) case (final e, final old)) return (Match(e, arms), old);
      for (var k = 0; k < arms.length; k++) {
        final (p, arm) = arms[k];
        final binds = patternBinds(p);
        final (Pattern, Term)? renamed;
        final String old;
        if (_Renamed.of(binds, depth) case final r?) {
          var i = r.at;
          renamed = (_renamePatternBind(p, () => i-- == 0, r.level), r.scope(arm));
          old = r.old;
        } else if (_renameFirst(arm, depth + binds.length) case (final a, final o)) {
          (renamed, old) = ((p, a), o);
        } else {
          continue;
        }
        return (Match(scrutinee, [...arms]..[k] = renamed), old);
      }
      return null;
    case Fam(:final domain, :final variable, :final body):
      if (_renameFirst(domain, depth) case (final d, final old)) {
        return (Fam(d, variable, body), old);
      }
      if (levelOf(variable) == null) {
        final level = levelName(depth);
        return (Fam(domain, level, _rename(body, variable, level)), variable);
      }
      if (_renameFirst(body, depth + 1) case (final b, final old)) {
        return (Fam(domain, variable, b), old);
      }
      return null;
    case Fix(:final init, :final step, :final self, :final key, kind: Definedness(), :final ev):
      Fix fix(Term init, String self, String key, Term step) =>
          Fix(init, step, self, key, const Definedness(), ev);
      if (_renameFirst(init, depth) case (final i, final old)) {
        return (fix(i, self, key, step), old);
      }
      if (_Renamed.of([self, key], depth) case final r?) {
        return (fix(init, r.names[0], r.names[1], r.scope(step)), r.old);
      }
      if (_renameFirst(step, depth + 2) case (final s, final old)) {
        return (fix(init, self, key, s), old);
      }
      return null;
    default:
      // The first child holding a written binder, renamed; the others kept.
      String? old;
      final renamed = _mapChildren(t, (c) {
        if (old != null) return c;
        final r = _renameFirst(c, depth);
        if (r == null) return c;
        old = r.$2;
        return r.$1;
      });
      return old == null ? null : (renamed, old!);
  }
}

/// `p` with the binder for which `hit` first answers true, counting left to right, renamed to
/// `level`.
Pattern _renamePatternBind(Pattern p, bool Function() hit, String level) {
  Pattern go(Pattern p) => switch (p) {
    BindP(:final name) => BindP(hit() ? level : name),
    AtomP(:final name, :final args) => AtomP(name, [for (final q in args) go(q)]),
    TupleP(:final items) => TupleP([for (final q in items) go(q)]),
    FieldsP(:final name, :final fields) => FieldsP(name, [for (final (f, q) in fields) (f, go(q))]),
    WildP() || LitP() || AnyAtomP() => p,
  };
  return go(p);
}

/// `t` with the free occurrences of the variable `old` renamed to `level`. A binder of `old`
/// inside `t` shadows it below.
Term _rename(Term t, String old, String level) {
  Term under(Iterable<String> names, Term body) =>
      names.contains(old) ? body : _rename(body, old, level);
  return switch (t) {
    Var(:final name) when name == old => Var(level),
    Lam(:final params, :final body) => Lam(params, under(params, body)),
    Let(:final name, :final value, :final body) => Let(
      name,
      _rename(value, old, level),
      under([name], body),
    ),
    Match(:final scrutinee, :final arms) => Match(_rename(scrutinee, old, level), [
      for (final (p, arm) in arms) (p, under(patternBinds(p), arm)),
    ]),
    Fam(:final domain, :final variable, :final body) => Fam(
      _rename(domain, old, level),
      variable,
      under([variable], body),
    ),
    Fix(:final init, :final step, :final self, :final key, kind: Definedness(), :final ev) => Fix(
      _rename(init, old, level),
      under([self, key], step),
      self,
      key,
      const Definedness(),
      ev,
    ),
    _ => _mapChildren(t, (c) => _rename(c, old, level)),
  };
}

/// `t` with every binder renamed as the rule renames them one per step, in one walk: each
/// written binder gets its level, and each variable the name of the binder it means. A binder
/// already canonical keeps its name, as the rule leaves it. Linear in the size of `t`.
Term canonical(Term t) => _Levels().term(t, 0);

/// The names in scope during the walk: each written name to the new names of the binders of
/// that name around the current subterm, innermost last.
final class _Levels {
  final _scope = <String, List<String>>{};

  /// `body` with `names`, bound together at levels `depth`, `depth + 1`, …, in scope in order,
  /// so that a later name of the group shadows an earlier one; and the new names.
  (List<String>, Term) under(List<String> names, int depth, Term body) {
    final renamed = [
      for (var i = 0; i < names.length; i++)
        levelOf(names[i]) == null ? levelName(depth + i) : names[i],
    ];
    for (var i = 0; i < names.length; i++) {
      (_scope[names[i]] ??= []).add(renamed[i]);
    }
    final b = term(body, depth + names.length);
    for (final x in names.reversed) {
      final stack = _scope[x]!..removeLast();
      if (stack.isEmpty) _scope.remove(x);
    }
    return (renamed, b);
  }

  Term term(Term t, int depth) {
    switch (t) {
      case Var(:final name):
        final stack = _scope[name];
        return stack == null ? t : Var(stack.last);
      case Lam(:final params, :final body):
        final (renamed, b) = under(params, depth, body);
        return Lam(renamed, b);
      case Let(:final name, :final value, :final body):
        final e = term(value, depth);
        final (renamed, b) = under([name], depth, body);
        return Let(renamed[0], e, b);
      case Match(:final scrutinee, :final arms):
        final e = term(scrutinee, depth);
        return Match(e, [
          for (final (p, arm) in arms)
            if (under(patternBinds(p), depth, arm) case (final renamed, final a))
              (_setBinds(p, renamed.iterator), a),
        ]);
      case Fam(:final domain, :final variable, :final body):
        final d = term(domain, depth);
        final (renamed, b) = under([variable], depth, body);
        return Fam(d, renamed[0], b);
      case Fix(:final init, :final step, :final self, :final key, kind: Definedness(), :final ev):
        final i = term(init, depth);
        final (renamed, s) = under([self, key], depth, step);
        return Fix(i, s, renamed[0], renamed[1], const Definedness(), ev);
      default:
        return _mapChildren(t, (c) => term(c, depth));
    }
  }
}

/// `p` with its binders, left to right, named by `names` in turn.
Pattern _setBinds(Pattern p, Iterator<String> names) => switch (p) {
  BindP() => BindP((names..moveNext()).current),
  AtomP(:final name, :final args) => AtomP(name, [for (final q in args) _setBinds(q, names)]),
  TupleP(:final items) => TupleP([for (final q in items) _setBinds(q, names)]),
  FieldsP(:final name, :final fields) => FieldsP(name, [
    for (final (f, q) in fields) (f, _setBinds(q, names)),
  ]),
  WildP() || LitP() || AnyAtomP() => p,
};
