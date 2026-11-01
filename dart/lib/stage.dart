/// Staging (DESIGN.md sec:staging, step L1.28): which terms the build evaluates.
///
/// Step L1.25 uses [ends], the test of whether a term's form shows that it ends
/// (docs/thresholds.md, replacement 6).
library;

import 'kernel.dart';

/// Whether `t` is shown to end by its form (docs/thresholds.md, replacement 6): it has no
/// `fix` or `gen`, and every function it calls, or hands to a family operation, is a
/// primitive, a lambda whose body ends, or a name a `let` binds to one. A `let` binds a name
/// only in its body, so such calls nest no deeper than the term; a call through a parameter
/// or a pattern variable, as in `w(w)`, is not shown to end. Free names are prelude words,
/// which are primitives. Each subterm is read once.
bool ends(Term t) => _Around().ends(t);

/// The names bound around a term, each with whether it is bound to a function that ends.
final class _Around {
  /// For each name, its bindings, innermost last.
  final _byName = <String, List<bool>>{};

  /// The names in the order bound, innermost last.
  final _order = <String>[];

  void _push(String x, bool ends) {
    _byName.putIfAbsent(x, () => []).add(ends);
    _order.add(x);
  }

  /// Unbinds all but the first `n` names bound.
  void _truncate(int n) {
    while (_order.length > n) {
      final x = _order.removeLast();
      final stack = _byName[x]!..removeLast();
      if (stack.isEmpty) _byName.remove(x);
    }
  }

  /// `f()` with `names` bound around it to values not known to be functions that end.
  bool _under(Iterable<String> names, bool Function() f) {
    final n = _order.length;
    for (final x in names) {
      _push(x, false);
    }
    final out = f();
    _truncate(n);
    return out;
  }

  bool ends(Term t) => switch (t) {
    Lit() || Var() || PrimFn() || Read() => true,
    Fix() || Gen() => false,
    Lam(:final params, :final body) => _under(params, () => ends(body)),
    App(:final f, :final args) => _callable(f) && args.every(ends),
    Let(:final name, :final value, :final body) => _let(name, value, body),
    Match(:final scrutinee, :final arms) =>
      ends(scrutinee) && arms.every((arm) => _under(_binds(arm.$1), () => ends(arm.$2))),
    Fam(:final domain, :final variable, :final body) =>
      ends(domain) && _under([variable], () => ends(body)),
    Reindex(:final family, :final kf, :final vf) => ends(family) && _callable(kf) && _callable(vf),
    Discard(:final family, :final sel) => ends(family) && _callable(sel),
    Fold(:final family, :final op, :final identity) =>
      ends(family) && _callable(op) && (identity == null || ends(identity)),
    PrimApp(:final args) => args.every(ends),
    If(:final cond, :final then, :final orElse) => ends(cond) && ends(then) && ends(orElse),
    Push(:final value) => ends(value),
  };

  bool _let(String x, Term e, Term b) {
    // A lambda bound and never called need not end; any other binding is evaluated.
    final bool c;
    if (e is Lam) {
      c = ends(e);
    } else if (ends(e)) {
      c = _callable(e);
    } else {
      return false;
    }
    final n = _order.length;
    _push(x, c);
    final out = ends(b);
    _truncate(n);
    return out;
  }

  /// Whether `f`, in the position of a function called, is one that ends: a primitive, a
  /// lambda whose body ends, or a name bound to one; a free name is a prelude word.
  bool _callable(Term f) => switch (f) {
    PrimFn() => true,
    Lam() => ends(f),
    Var(:final name) => _byName[name]?.last ?? true,
    _ => false,
  };
}

/// The names `p` binds.
Iterable<String> _binds(Pattern p) => switch (p) {
  BindP(:final name) => [name],
  AtomP(args: final ps) || TupleP(items: final ps) => ps.expand(_binds),
  FieldsP(:final fields) => fields.expand((f) => _binds(f.$2)),
  _ => const [],
};
