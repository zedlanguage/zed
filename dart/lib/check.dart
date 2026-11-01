/// The checker (step L1.26): resolution rules 1, 3 and 4 of DESIGN.md "Resolution". Each node
/// is typed bottom up; an `is` test narrows the name it tests in each branch it guards; each
/// declared function gets a signature from its body. A numeric literal adopts the carrier an
/// operator or a parameter expects, exactly or not at all (sec:domains). A lambda in a slot of
/// function type takes its parameter types and kinds from that type, and a declared function
/// passed there must have its parameter kinds.
///
/// A function's parameter with neither a type nor a closed default is inferred, with the body
/// checked once (docs/thresholds.md, replacement 1). The parameter's values form a class, a
/// node of a union-find forest, holding the carriers it may still take. A use that needs two
/// values to share a carrier, as the operands of `+` do, merges their classes; a use that
/// accepts some carriers removes the rest; a literal joins the class it meets. Each step only
/// merges classes or removes carriers, so the solution is reached by propagation with no
/// search. When the function ends, each class of its parameters takes its type: the first of
/// int, f64 and rat if it holds a literal, which then adopts it; a type variable if it may take
/// any value; its one carrier; a type variable bounded by its carriers if several; and an error
/// if none, listing every use that removed one.
///
/// A use of a value whose type is a type variable is a need of the signature, checked again at
/// each call on the type the call binds the variable to, so `first(p) = p[0]` is generic and a
/// non-tuple argument is rejected at the call. `_` is the type of every value: it passes only
/// where any value is accepted (DESIGN.md "Soundness").
///
/// Where DESIGN.md does not say: an atom passes through the operators and the prelude words, as the kernel's primitives pass it,
/// but not through a declared function, which binds it; a call matching several arrows takes
/// the first one's result.
///
/// Step L1.27: an atom of a named family is data (sec:failure). `else` strips only the loose
/// atoms, and a family atom that selects no arrow is an error, where a loose one flows on.
library;

import 'dart:collection';

import 'ast.dart';
import 'kernel.dart' as k;
import 'resolve.dart';
import 'source.dart';
import 'src/check/ty.dart';
import 'src/store/interval.dart' hide Piece;
import 'src/store/revision.dart';
import 'src/tables.dart';

export 'src/check/ty.dart';

/// How a function argument fits the function type its slot expects.
sealed class Fit {
  const Fit();
}

/// A lambda: for each parameter of the expected type, the lambda's parameter that takes it,
/// if any; and the lambda's parameters the type does not pass, each filled by its default.
final class FitLambda extends Fit {
  final List<int?> order;
  final List<int> extra;

  const FitLambda(this.order, this.extra);

  @override
  bool operator ==(Object other) =>
      other is FitLambda && listEq(other.order, order) && listEq(other.extra, extra);

  @override
  int get hashCode => Object.hash(Object.hashAll(order), Object.hashAll(extra));
}

/// A declared function whose named parameters are in another order: for each of its
/// parameters, the index of the type's parameter that fills it.
final class FitAdapter extends Fit {
  final List<int> from;

  const FitAdapter(this.from);

  @override
  bool operator ==(Object other) => other is FitAdapter && listEq(other.from, from);

  @override
  int get hashCode => Object.hashAll(from);
}

/// What the checker finds.
final class Info {
  /// The value each adopted literal takes, by its span, before any `-`.
  Map<Span, k.Value> adopt = {};

  /// The signature of the function called through a value, by the call's span.
  Map<Span, Sig> calls = {};

  /// The fit of each function argument that needs one, by its span.
  Map<Span, Fit> fits = {};

  /// Each declared function's signature, by its binder.
  Map<Binder, Sig> sigs = {};

  /// The type of each top-level name bound by `=` (step L1.37).
  Map<String, Ty> tops = {};

  /// For each call of a function, the arguments whose loose atoms its parameter does not
  /// take: an atom there selects no arrow and is the call's value (rule 6 of
  /// sec:type_resolution), by the call's span and the arguments' spans.
  Map<Span, List<Span>> passes = {};

  /// The type errors.
  List<BuildError> errors = [];
}

/// Checks a resolved unit.
Info check(List<Stmt> unit, Resolution res) => checkWith(Tables(unit, res), unit);

Info checkWith(Tables t, List<Stmt> unit) {
  k.Emptiness.forget();
  final ck = _Ck(t);
  ck
    ..run(ck.scope(unit, true))
    ..finish();
  final errors = ck.info.errors
    ..sort((a, b) {
      final c = _compareSpans(a.span, b.span);
      return c != 0 ? c : a.message.compareTo(b.message);
    });
  final out = <BuildError>[];
  for (final e in errors) {
    if (out.isNotEmpty && _sameError(out.last, e)) continue;
    out.add(e);
  }
  ck.info.errors = out;
  return ck.info;
}

int _compareSpans(Span a, Span b) => a.start != b.start ? a.start - b.start : a.end - b.end;

bool _sameError(BuildError a, BuildError b) =>
    a.span == b.span && a.message == b.message && listEq(a.notes, b.notes);

/// The type of the binary operator `op` applied to arguments of the types `args`, with the
/// errors the application reports: how an operator treats loose and family atoms.
(Ty, List<String>) operator(String op, List<Ty> args) {
  final ck = _Ck(Tables(const [], resolve(const [])));
  final (out, _) = ck.apply(
    '`$op`',
    opSig(op),
    [for (final a in args) _Arg(a)],
    true,
    (start: 0, end: 0),
  );
  return (out, [for (final e in ck.info.errors) e.message]);
}

/// A numeric literal: its span, its value, whether a `-` is applied to it, and its text.
final class Lit {
  final Span span;
  final k.Value value;
  final bool neg;
  final String text;

  Lit(this.span, this.value, this.neg, this.text);
}

/// An argument: its type, the literal it is, if it is one, and the expression it is, if any.
final class _Arg {
  Ty ty;
  final Lit? lit;
  final Span? at;

  _Arg(this.ty, [this.lit, this.at]);

  _Arg copy() => _Arg(ty, lit, at);
}

/// An argument of a call: an expression, or an argument already found, as when a use the
/// body of a generic function makes is checked again at a call of the function.
sealed class _Src {
  const _Src();
}

final class _SrcExpr extends _Src {
  final Expr e;

  const _SrcExpr(this.e);
}

final class _SrcGot extends _Src {
  final _Arg a;

  const _SrcGot(this.a);
}

/// The positional and named arguments of a call, as expressions.
(List<_Src>, List<(String, _Src)>) _srcs(List<Expr> positional, List<(String, Expr)> named) => (
  [for (final e in positional) _SrcExpr(e)],
  [for (final (n, e) in named) (n, _SrcExpr(e))],
);

/// Facts an `is` test makes: binders narrowed to a type, and the test.
typedef _Facts = List<(Binder, Ty, Span)>;

/// Each part of the unit is checked by a generator that yields the generators of the parts it
/// needs and reads each one's result from [_Ck._got], then leaves its own there. They run on
/// an explicit stack, so the depth of the unit's nesting is bounded by memory alone.
typedef _Steps = Iterable<Iterable<Object?>>;

/// An expression's type as the checker last found it, and where it comes from: a name or a
/// call of a declared function, by its binder, or else the expression, whose parts'
/// derivations continue it.
final class _Seen {
  final Ty ty;
  final Binder? name;
  final Binder? call;
  final Expr e;

  _Seen(this.ty, this.e, {this.name, this.call});
}

/// Where a binder's type comes from: the text, what it says, the expression whose derivation
/// continues it, and the origin it narrows.
final class _Origin {
  final Span span;
  final String text;
  final Span? from;
  final _Origin? then;

  _Origin(this.span, this.text, [this.from, this.then]);
}

/// A class of values that must share one carrier: a node of the union-find forest of
/// docs/thresholds.md, replacement 1. Only a root's fields other than `parent` and `rank` are
/// read.
final class _Class {
  int parent;
  int rank = 0;

  /// The carriers it may still take, and [other] if it may take other values.
  int mask = every;

  /// The depth of the function whose parameter made it; of a merged class, the least.
  int level;

  /// The literals that joined it, each with whether it follows: a follower adopts the
  /// class's carrier but does not restrict it.
  List<(Lit, bool)> lits = [];

  /// The uses that removed carriers from it.
  List<Note> reasons = [];

  /// Its type, once the function of its level ends.
  Ty? resolved;

  /// What uses of its values need of them, each numbered in the order of all needs.
  List<(int, Need)> uses = [];

  /// The tuples and functions that flowed into it, each with where: every use is checked on
  /// each.
  List<(Ty, Span)> flowed = [];

  _Class(this.parent, this.level);

  _Class copy() => _Class(parent, level)
    ..rank = rank
    ..mask = mask
    ..lits = [...lits]
    ..reasons = [...reasons]
    ..resolved = resolved
    ..uses = [...uses]
    ..flowed = [...flowed];
}

/// A need being checked at a call.
final class _Open {
  /// The need's use in the body.
  final Span span;

  /// The type of the value it is checked on, its variables read as the unknown.
  final Ty shape;

  /// What a use met again inside the check gives: nothing at first, then what the check
  /// gave.
  Ty result = Ty.empty;

  /// Whether the check met the use again and took [result].
  var used = false;

  _Open(this.span, this.shape);
}

final class _Ck {
  final Tables t;
  final env = <Binder, Ty>{};
  final info = Info();

  /// For each write to `info`'s maps, and to a class while a repair is tried, what undoes
  /// it, so that a repair is undone by what it wrote.
  final log = <void Function()>[];

  /// Each expression's type, by its span, as last found.
  final seen = <Span, _Seen>{};

  /// Where each binder's type comes from.
  final whence = <Binder, _Origin>{};

  /// Whether a repair is being tried, so its errors offer none.
  var trying = false;

  /// The output ports declared `Lines`.
  final linesOut = <String>{};

  /// The classes; class `k` is the type variable `$k`.
  final classes = <_Class>[];

  /// How many declared functions are being checked, one inside another.
  var level = 0;

  /// The classes each of those functions resolves when it ends, by its level.
  final pending = [<int>[]];

  /// The needs recorded so far.
  var needs = 0;

  /// How many checks of a generic function's needs are under way; they write nothing for
  /// elaboration.
  var replaying = 0;

  /// The needs being checked at calls, one inside another.
  final open = <_Open>[];

  /// The variables of the parameters a partial call leaves out: the next application leaves
  /// the needs on them to the function the call gives.
  var defer = SplayTreeSet<String>();

  /// What the last application of one arrow bound, and the needs it left.
  (Binds, List<Need>)? lastApplied;

  /// What the last step to finish found.
  Object? _got;

  _Ck(this.t);

  /// Runs `steps` and the steps they yield, leaving its result in [_got].
  void run(_Steps steps) {
    final stack = [steps.iterator];
    while (stack.isNotEmpty) {
      if (stack.last.moveNext()) {
        stack.add((stack.last.current as _Steps).iterator);
      } else {
        stack.removeLast();
      }
    }
  }

  /// The type the last step found.
  Ty get got => _got as Ty;

  /// The argument the last step found.
  _Arg get gotArg => _got as _Arg;

  /// The condition the last step found.
  (Ty, _Facts, _Facts) get gotCond => _got as (Ty, _Facts, _Facts);

  /// An error at `span`, with the derivation of the expression there.
  void error(Span span, String message) => errorWith(span, message, derive([span]));

  void errorWith(Span span, String message, List<Note> notes) =>
      info.errors.add(BuildError(span, message, notes));

  /// The derivation of the expressions at `spans`: for each, its type, and for a name or a
  /// call, where the binder's type comes from, followed through each definition.
  List<Note> derive(List<Span> spans) {
    final out = <Note>[];
    deriveInto(spans, out);
    return out;
  }

  /// Each expression is derived once, however many others it continues, so a derivation is
  /// at most the size of the graph of origins it walks. The walk keeps its own stack, since
  /// a chain of definitions can be as long as the program. An item of the stack is a span to
  /// derive or a note to show.
  void deriveInto(List<Span> spans, List<Note> out) {
    final shown = {...out};
    final visited = <Span>{};
    final stack = <Object>[...spans.reversed];
    while (stack.isNotEmpty) {
      final w = stack.removeLast();
      if (w is Note) {
        if (shown.add(w)) out.add(w);
        continue;
      }
      final span = w as Span;
      if (!visited.add(span)) continue;
      final s = seen[span];
      if (s == null) continue;
      final ty = show(s.ty);
      // What this expression shows, in order; pushed reversed so it pops in order.
      final next = <Object>[];
      final Binder id;
      if (s.name case final b?) {
        next.add((span: span, text: '`${b.name}` is $ty here'));
        id = b;
      } else if (s.call case final b?) {
        next.add((span: span, text: 'this call of `${b.name}` gives $ty'));
        id = b;
      } else {
        final e = s.e;
        final parts = switch (e) {
          Unary(:final e) => [e],
          Binary(:final a, :final b) => [a, b],
          Else(:final of, :final fallback) => [of, fallback],
          If(:final cond, :final then, :final otherwise) => [cond, then, otherwise],
          Call(:final positional, :final named) => [...positional, for (final (_, a) in named) a],
          Tuple(:final items) => items,
          Index(:final e) => [e],
          _ => const <Expr>[],
        };
        final what = switch (e) {
          Unary(:final op) || Binary(:final op) => 'this `$op`',
          Else() => 'this `else`',
          If() => 'this `if`',
          Call(callee: NameRef(:final name)) => 'this call of `$name`',
          Call() => 'this call',
          _ => 'this expression',
        };
        final verb = parts.isEmpty ? 'is' : 'gives';
        next.add((span: span, text: '$what $verb $ty'));
        for (final p in parts) {
          next.add(switch (literal(p)) {
            final l? => (
              span: p.span,
              text: 'this literal, ${l.text}, is ${litTy(l.value, l.neg)}',
            ),
            null => p.span,
          });
        }
        stack.addAll(next.reversed);
        continue;
      }
      var o = whence[id];
      if (o == null) next.add((span: id.span, text: '`${id.name}` is bound here'));
      while (o != null) {
        next.add((span: o.span, text: o.text));
        if (o.from case final f?) next.add(f);
        o = o.then;
      }
      stack.addAll(next.reversed);
    }
  }

  /// Records where binder `id` gets its type.
  void origin(Binder id, Span span, String text, [Span? from]) =>
      whence[id] = _Origin(span, text, from);

  Binder id(Span span, String name) => t.id(span, name);

  /// The statements of one scope, in the order elaboration binds them; the export's type.
  _Steps scope(List<Stmt> stmts, bool top) sync* {
    List<Expr>? export;
    final items = <Stmt>[];
    for (final s in stmts) {
      if (s case Return(:final values)) {
        export = values;
      } else {
        items.add(s);
      }
    }
    final (order, cycle) = t.order(items);
    if (cycle != null) {
      _got = Ty.dynamic;
      return;
    }
    for (final i in order) {
      yield stmt(items[i]);
    }
    if (top) {
      for (final s in items) {
        if (s case Bind(targets: [final n?])) {
          if (env[id(s.span, n)] case final ty?) _put(info.tops, n, ty);
        }
      }
      for (final s in items) {
        if (s case FunctionDef f) yield tests(f, id(s.span, f.name));
      }
    }
    switch (export) {
      case null:
        _got = Ty.tuple(const []);
      case [final e]:
        yield expr(e);
      case final es:
        final tys = <Ty>[];
        for (final e in es) {
          yield expr(e);
          tys.add(got);
        }
        _got = Ty.tuple(tys);
    }
  }

  _Steps stmt(Stmt s) sync* {
    switch (s) {
      case Bind(:final targets, :final value):
        yield expr(value);
        final v = got;
        switch (targets) {
          case [final n?]:
            final b = id(s.span, n);
            origin(b, value.span, '`$n` is defined as this expression, $v', value.span);
            env[b] = v;
          case [null]:
            break;
          default:
            for (final (i, n) in targets.indexed) {
              final c = component(v, i, targets.length, value.span);
              if (n != null) {
                final b = id(s.span, n);
                origin(b, value.span, '`$n` is component $i of this, $c', value.span);
                env[b] = c;
              }
            }
        }
      case FunctionDef f:
        final b = id(s.span, f.name);
        yield infer(f, s.span);
        final sig = _got as Sig;
        origin(b, s.span, '`${f.name}` is declared here, `$sig`');
        env[b] = Ty.func(sig);
        _put(info.sigs, b, sig);
      case Push(:final port, :final value):
        yield expr(value);
        if (linesOut.contains(port)) pushed(got, value.span);
      case Return():
        throw StateError('an export is not a binding');
    }
  }

  /// Component `i` of `v`, destructured into `n` names: of each tuple shape, with `v`'s
  /// atoms, which `TupleGet` passes.
  Ty component(Ty v, int i, int n, Span span) {
    var out = passing(v, 'a tuple', span);
    for (final p in v.pieces) {
      switch (p) {
        case PTuple(:final cs) when cs.length == n:
          out = out.union(cs[i]);
        case PDyn():
          if (i == 0) any('destructuring', span);
        case PVar():
          out = out.union(Ty.dynamic);
        case _ when p.isAtoms:
          break;
        default:
          if (i == 0) error(span, 'this value is ${p.ty}, not a tuple of $n');
      }
    }
    return out;
  }

  /// The signature of a declared function. A parameter with neither a type nor a closed
  /// default gets a class, which its uses narrow, the body checked once. When the function
  /// ends, each class of its level takes its type; a class merged with one of a function
  /// around it waits for that function.
  _Steps infer(FunctionDef f, Span span) sync* {
    final params = [
      for (final (i, p) in f.params.indexed)
        SParam(
          p.name,
          p.positional,
          p.fallback == null
              ? null
              : (fn: id(span, f.name), index: i, closed: t.usesIn(p.fallback!.span).isEmpty),
        ),
    ];
    final ids = [for (final p in f.params) id(p.span, p.name)];
    final given = <Ty?>[];
    for (final p in f.params) {
      yield paramType(p);
      given.add(_got as Ty?);
    }
    for (final p in f.ports ?? const <Port>[]) {
      final b = id(p.span, p.name);
      origin(b, p.span, '`${p.name}` is an output port');
      if (p.type case TypeName(name: 'Lines')) linesOut.add(p.name);
      env[b] = Ty.dynamic;
    }
    final level = ++this.level;
    if (pending.length <= level) pending.add([]);
    final tys = <Ty>[];
    for (final (i, p) in f.params.indexed) {
      final (Ty ty, String text) = switch ((p.type, given[i])) {
        (final a?, final g?) when g == Ty.dynamic => (
          g,
          '`${p.name}` is declared `$a`, whose values the checker does not track: '
              'it takes `${p.name}` as unknown, _',
        ),
        (final a?, final g?) => (g, '`${p.name}` is declared `$a`'),
        (null, final g?) => (g, '`${p.name}` is $g, the carrier of its default'),
        (_, null) => switch (newClass()) {
          final c => (
            Ty.variable('\$$c'),
            '`${p.name}` has no declared type; its uses give it \$$c',
          ),
        },
      };
      origin(ids[i], p.span, text);
      env[ids[i]] = ty;
      tys.add(ty);
    }
    // A default that reads the other parameters, at its parameter's type.
    for (final (i, p) in f.params.indexed) {
      final d = p.fallback;
      if (d == null || t.usesIn(d.span).isEmpty) continue;
      final ty = tys[i];
      final what = 'the default of `${p.name}`';
      if (classOfTy(ty) case final c?) {
        yield expr(d);
        final dt = got;
        if (!flow(c, dt, what, d.span)) {
          final shown = show(ty);
          errorWith(d.span, '$what is $dt, not $shown', [
            ...derive([d.span]),
            ...reasons(ty),
          ]);
        }
      } else {
        yield exprAt(d, ty);
        final dt = got;
        if (!dt.subtype(ty)) error(d.span, '$what is $dt, not $ty');
      }
    }
    if (f.body case Block(:final stmts) when !f.equation) {
      yield scope(stmts, false);
    } else {
      yield expr(f.body);
    }
    _got = generalize(level, Sig.one(params, tys, got));
  }

  /// The signature `sig` of the function of `level`, which ends: each class of the level
  /// takes its type, a type variable of the signature named in order of appearance. The uses
  /// of a class that is a type variable join the signature as its needs; those of a class of
  /// one type are checked on it now.
  Sig generalize(int level, Sig sig) {
    final own = <int>[];
    final mine = pending[level];
    pending[level] = [];
    for (final c in mine) {
      final r = find(c);
      if (classes[r].resolved != null) continue;
      final at = classes[r].level;
      if (at < level) {
        pending[at].add(r);
        continue;
      }
      resolveClass(r);
      own.add(r);
    }
    final needs = <(int, Need)>[];
    final now = <(Need, Ty)>[];
    for (final r in own) {
      final uses = classes[r].uses;
      classes[r].uses = [];
      final t = classes[r].resolved!;
      if (t == Ty.variable('\$$r')) {
        needs.addAll(uses);
      } else {
        now.addAll([for (final (_, n) in uses) (n, t)]);
      }
    }
    for (final (n, t) in now) {
      checkOn(n, t, n.span);
    }
    needs.sort((a, b) => a.$1 - b.$1);
    // The classes of this level that are type variables, named in order of appearance.
    sig = solvedSig(sig.copy(needs: [for (final (_, n) in needs) n]));
    final vars = sigVars(sig);
    final taken = {
      for (final v in vars)
        if (classId(v) == null) v,
    };
    final ownSet = own.toSet();
    final names = Binds();
    final bounds = SplayTreeMap<String, int>();
    var n = 0;
    for (final v in vars) {
      final r = classId(v);
      if (r == null || !ownSet.contains(r)) continue;
      var name = varName(n++);
      while (taken.contains(name)) {
        name = varName(n++);
      }
      if (classes[r].mask != every) bounds[name] = classes[r].mask;
      classes[r].resolved = Ty.variable(name);
      names[v] = Ty.variable(name);
    }
    // A type variable that does not reach the signature means nothing outside it.
    for (final r in own) {
      if (classes[r].resolved case final ty? when ty.vars.any((v) => classId(v) != null)) {
        classes[r].resolved = Ty.dynamic;
      }
    }
    final out = sig.replace(names);
    out.bounds.addAll(bounds);
    this.level--;
    return out.copy(own: SplayTreeSet.of(names.values.expand((t) => t.vars)));
  }

  /// A new class, of every value, at the current level.
  int newClass() {
    final c = classes.length;
    classes.add(_Class(c, level));
    pending[level].add(c);
    return c;
  }

  /// The root of class `c`'s tree.
  int find(int c) {
    while (classes[c].parent != c) {
      c = classes[c].parent;
    }
    return c;
  }

  /// Logs class `r` before a change, while a repair is tried.
  void touch(int r) {
    if (!trying) return;
    final saved = classes[r].copy();
    log.add(() => classes[r] = saved);
  }

  /// Removes from class `c` the carriers `mask` lacks, as `what` at `span` requires; false,
  /// changing nothing, if none would be left.
  bool restrict(int c, int mask, String what, Span span) {
    final r = find(c);
    final m = classes[r].mask & mask;
    if (m == classes[r].mask) return true;
    if (m == 0) return false;
    touch(r);
    classes[r]
      ..mask = m
      ..reasons.add((span: span, text: '$what takes ${maskText(mask)}'));
    return true;
  }

  /// Merges classes `a` and `b`, as `what` at `span` requires; false, changing nothing, if
  /// they share no carrier. The shorter lists move into the longer, so that each item moves
  /// `O(log n)` times.
  bool merge(int a, int b, String what, Span span) {
    (a, b) = (find(a), find(b));
    if (a == b) return true;
    final m = classes[a].mask & classes[b].mask;
    if (m == 0) return false;
    touch(a);
    touch(b);
    final (root, child) = classes[a].rank < classes[b].rank ? (b, a) : (a, b);
    if (classes[a].rank == classes[b].rank) classes[root].rank++;
    // Each use of one class is checked on what flowed into the other.
    final cross = [
      for (final (x, y) in [(a, b), (b, a)])
        for (final (_, n) in classes[x].uses)
          for (final (t, at) in classes[y].flowed) (n, t, at),
    ];
    final lowered = classes[a].level != classes[b].level;
    final ch = classes[child];
    var (lits, reasons, uses, flowed) = (ch.lits, ch.reasons, ch.uses, ch.flowed);
    ch
      ..lits = []
      ..reasons = []
      ..uses = []
      ..flowed = []
      ..parent = root;
    final c = classes[root];
    if (c.uses.length < uses.length) {
      final u = c.uses;
      c.uses = uses;
      uses = u;
    }
    c.uses.addAll(uses);
    if (c.flowed.length < flowed.length) {
      final f = c.flowed;
      c.flowed = flowed;
      flowed = f;
    }
    c.flowed.addAll(flowed);
    if (c.lits.length < lits.length) {
      final l = c.lits;
      c.lits = lits;
      lits = l;
    }
    c.lits.addAll(lits);
    if (c.reasons.length < reasons.length) {
      final r = c.reasons;
      c.reasons = reasons;
      reasons = r;
    }
    c.reasons
      ..addAll(reasons)
      ..add((span: span, text: '$what gives these values one carrier'));
    c
      ..mask = m
      ..level = c.level < ch.level ? c.level : ch.level;
    if (lowered) {
      final vars = Vars();
      for (final (_, n) in c.uses) {
        n.varsIn(vars);
      }
      lower(vars.order, c.level);
    }
    for (final (n, t, at) in cross) {
      checkOn(n, t, at);
    }
    return true;
  }

  /// Lowers to `level` the classes of `vars` above it, and those of their uses' variables.
  void lower(List<String> vars, int level) {
    final stack = [...vars];
    while (stack.isNotEmpty) {
      final k = classId(stack.removeLast());
      if (k == null || k >= classes.length) continue;
      final r = find(k);
      if (classes[r].level <= level || classes[r].resolved != null) continue;
      touch(r);
      classes[r].level = level;
      final more = Vars();
      for (final (_, n) in classes[r].uses) {
        n.varsIn(more);
      }
      stack.addAll(more.order);
    }
  }

  /// A use of a value of class `k`: recorded on the class, checked on each tuple and function
  /// that flowed into it, and, when it `gives` a value, a new class for that value.
  Ty need(int k, NeedKind kind, bool gives, Span span) {
    final r = find(k);
    if (kind is NData && classes[r].uses.any((u) => u.$2.kind is NData)) return Ty.empty;
    for (final (_, n) in classes[r].uses) {
      if (n.kind == kind && (n.result != null) == gives) return n.result ?? Ty.empty;
    }
    final level = classes[r].level;
    Ty? result;
    if (gives) {
      final j = newClass();
      classes[j].level = level;
      result = Ty.variable('\$$j');
    }
    final need = Need(Ty.variable('\$$r'), kind, result, span);
    final vars = Vars();
    need.varsIn(vars);
    lower(vars.order, level);
    final flowed = [...classes[r].flowed];
    touch(r);
    needs++;
    classes[r].uses.add((needs, need));
    for (final (t, at) in flowed) {
      checkOn(need, t, at);
    }
    return result ?? Ty.empty;
  }

  /// The use `n` checked on a value of type `t`.
  void checkOn(Need n, Ty t, Span span) {
    final from = info.errors.length;
    final got = meet(n, t, Binds(), span);
    if (n.result case final r? when classOfTy(r) != null) {
      if (!flow(classOfTy(r)!, got, 'this use', n.span)) {
        error(n.span, 'this use gives $got, not ${show(r)}');
      }
    }
    also(from, (span: n.span, text: 'this use needs it here'));
  }

  /// What the use `n` gives on a value of type `on`, its variables bound by `binds`.
  Ty meet(Need n, Ty on, Binds binds, Span span) {
    Ty b(Ty t) => bound(t, binds);
    on = b(on);
    replaying++;
    final Ty out;
    switch (n.kind) {
      case NComponent(:final i, :final key):
        out = atIndex(on, i, _Arg(key), span);
      case NIndex(:final key):
        out = atKey(on, _Arg(b(key)), span);
      case NCall(:final what, :final positional, :final named, :final curry):
        run(
          callValue(
            on,
            what,
            null,
            [for (final t in positional) _SrcGot(_Arg(b(t)))],
            [for (final (m, t) in named) (m, _SrcGot(_Arg(b(t))))],
            curry,
            span,
          ),
        );
        out = got;
      case NData(:final what):
        data(on, what, span);
        out = Ty.empty;
      case NInto(:final what, :final ty):
        into(on, ty, what, span);
        out = Ty.empty;
      case NPayload(:final atom, :final slot):
        out = payload(on, atom, slot, span);
    }
    replaying--;
    return out;
  }

  /// The needs of a signature, `what`, checked at a call with its variables bound by `binds`;
  /// gives those on the variables of `defer`, and of the needs that share one with them,
  /// which the function the call gives keeps.
  List<Need> replay(String what, List<Need> needs, Binds binds, Set<String> defer, Span span) {
    defer = {...defer};
    final left = <Need>[];
    for (final n in needs) {
      if (defer.isNotEmpty) {
        final vars = Vars();
        n.varsIn(vars);
        if (vars.order.any(defer.contains)) {
          defer.addAll(vars.order);
          left.add(n);
          continue;
        }
      }
      final from = info.errors.length;
      final on = bound(n.on, binds);
      final shape = bound(on, Binds());
      final o = open.where((o) => o.span == n.span).firstOrNull;
      Ty got;
      if (on.isDynamic) {
        any('$what, which needs this of its argument,', span);
        got = Ty.empty;
      } else if (o != null && o.shape == shape) {
        o.used = true;
        got = o.result;
      } else if (o != null) {
        error(
          span,
          '$what needs this of its argument again inside its own check, on $on where it was '
          '${o.shape}: the checker does not follow a call at a type that may grow without end',
        );
        got = Ty.empty;
      } else {
        final before = Binds.of(binds);
        final errors = info.errors.length;
        final mine = _Open(n.span, shape);
        open.add(mine);
        got = meet(n, on, binds, span);
        if (mine.used && !got.isEmpty) {
          binds
            ..clear()
            ..addAll(before);
          info.errors.length = errors;
          mine.result = got;
          final first = got;
          got = meet(n, on, binds, span);
          if (!got.subtype(first)) {
            error(
              span,
              '$what needs this of its argument again inside its own check, and the result is '
              'not settled: it gives $got where the use inside gave $first',
            );
          }
        }
        open.removeLast();
      }
      // What the use gives is within its result: a variable there joins it, as for an
      // argument, and one it leaves unbound gives nothing.
      if (n.result case final r?) {
        if (!got.sub(r, binds)) error(span, '$what gives $got here, which is not $r');
        for (final v in r.vars) {
          binds.putIfAbsent(v, () => Ty.empty);
        }
      }
      also(from, (span: n.span, text: '$what needs this of its argument here'));
    }
    return left;
  }

  /// Each value of `on` passed, as an argument of `what`, at a parameter of the closed type
  /// `ty`.
  void into(Ty on, Ty ty, String what, Span span) {
    for (final piece in on.pieces) {
      final c = classOf(piece);
      final bool ok;
      if (piece is PDyn) {
        ok = ty.isDynamic;
      } else if (piece is PVar && c == null) {
        ok = true;
      } else if (c != null) {
        ok = restrict(c, maskOf(ty), what, span);
        need(c, NInto(what, ty), false, span);
      } else if (piece case PFn(:final s) when s.needs.isNotEmpty) {
        ok = fitNeeds(s, ty, Binds(), what, span);
      } else {
        ok = piece.ty.sub(ty, Binds());
      }
      if (!ok) error(span, '$what does not take ${show(piece.ty)}, which is not $ty');
    }
  }

  /// Whether the generic function `s` fits the one function type `p`: its signature without
  /// its needs does, and its needs hold on `p`'s parameters. An error the needs make is
  /// reported, and the fit then holds.
  bool fitNeeds(Sig s, Ty p, Binds binds, String what, Span span) {
    final bare = s.copy(needs: const []);
    if (p.fns.length != 1) return false;
    if (!Ty.func(bare).sub(p, binds)) return false;
    final q = p.fns[0].replace(binds);
    final from = info.errors.length;
    var ok = true;
    for (final a in q.arrows) {
      final (r, _) = apply(what, s, [for (final t in a.params) _Arg(t)], false, span);
      ok &= r.subtype(a.result);
    }
    return ok || info.errors.length > from;
  }

  /// A value of type `t` used by `what`, which takes data: it holds no function.
  void data(Ty t, String what, Span span) {
    if (t.heldFunction case final s?) {
      error(span, '$what takes data, and this value may hold a function, `$s`');
    }
    // A class, at any depth, needs data of each of its values.
    final stack = [t];
    while (stack.isNotEmpty) {
      for (final p in stack.removeLast().pieces) {
        switch (p) {
          case PDyn():
            any(what, span);
          case PTuple(:final cs):
            stack.addAll(cs);
          case PVar():
            if (classOf(p) case final k?) need(k, NData(what), false, span);
          default:
            break;
        }
      }
    }
  }

  /// `what` given a value of type `_`.
  void any(String what, Span span) => error(
    span,
    '$what does not take every value, and this value is `_`, which may be any: test it with '
    '`is` first',
  );

  /// A value of type `t` pushed to a `Lines` port: a string, or a family of strings.
  void pushed(Ty t, Span span) {
    bool strings(k.Type s) => s.subtype(k.Type.string);
    bool plain(Ty t) => t.tuples.isEmpty && t.vars.isEmpty;
    final notFound = k.Type.atom('notFound');
    final ok =
        strings(t.set) &&
        plain(t) &&
        t.fns.every(
          (s) =>
              s.data &&
              s.arrows.every((a) => plain(a.result) && strings(a.result.set - notFound)),
        );
    if (!ok && !t.isDynamic && t.vars.isEmpty) {
      error(span, 'a `Lines` port takes a `String` or a family of strings, not ${show(t)}');
    }
  }

  /// `x ** n` on ints: the exponent, the expression `e`, is at least 0.
  void exponent(_Arg x, _Arg n, Expr e, Span span) {
    final ns = n.ty.set & k.Type.integer;
    if ((x.ty.set & k.Type.integer).isEmpty || ns.isEmpty) return;
    const zero = k.Int(0);
    final listed = ns.listed;
    final atLeastZero =
        interval(e).isSubset(IntervalSet.range(const Fin(0), posInf)) ||
        (listed != null && listed.every((v) => (v.surfaceCmp(zero) ?? -1) >= 0));
    if (!atLeastZero) {
      errorWith(
        span,
        '`**` on an int needs an exponent of at least 0, and this one is ${show(Ty.of(ns))}',
        derive([n.at ?? span]),
      );
    }
  }

  /// The names the pattern `p` binds, from the `next`th of `ids`, each the payload of a
  /// value of type `v` at its place; gives the index after the last.
  int bindPattern(AtomPattern p, Ty v, List<Binder> ids, int next) {
    final slots = <(Slot, Pattern?)>[
      for (final (f, sub) in p.fields) (SField(f), sub),
      for (final (i, sub) in p.items.indexed) (SItem(i), sub),
    ];
    for (final (slot, sub) in slots) {
      final t = payload(v, p.name, slot, p.span);
      if (sub is AtomPattern) {
        next = bindPattern(sub, t, ids, next);
      } else {
        env[ids[next++]] = t;
      }
    }
    return next;
  }

  /// What a value of type `v` holds at `slot` when it is an atom named `atom`.
  Ty payload(Ty v, String atom, Slot slot, Span span) {
    var out = switch (v.withoutVars.shapes(atom)) {
      final ss? => Ty.unionAll(ss.map((s) => s.at(slot)).nonNulls),
      null => Ty.dynamic,
    };
    if (v.isDynamic) out = out.union(Ty.dynamic);
    for (final x in v.vars) {
      final t = switch (classOf(PVar(x))) {
        final k? => need(k, NPayload(atom, slot), true, span),
        null => Ty.dynamic,
      };
      out = out.union(t);
    }
    return out;
  }

  /// The literal `l` joins class `c`; unless it follows, the class keeps only the carriers it
  /// may adopt, and false if none would be left.
  bool join(int c, Lit l, bool follower) {
    if (!follower) {
      final m = Carrier.values.where((x) => adoptable(l, x)).fold(0, (m, x) => m | x.bit);
      if (!restrict(c, m, 'the literal ${l.text}', l.span)) return false;
    }
    final r = find(c);
    touch(r);
    classes[r].lits.add((l, follower));
    return true;
  }

  /// The values of `ty` flow into class `c`: a class merges with it, a carrier restricts it to
  /// that carrier, and a tuple or a function to other values; atoms and the unknown change
  /// nothing.
  bool flow(int c, Ty ty, String what, Span span) {
    for (final p in ty.pieces) {
      final ok = switch ((classOf(p), p.carrier)) {
        (final j?, _) => merge(c, j, what, span),
        _ when p is PDyn => false,
        _ when p is PVar || p.isAtoms => true,
        (null, final x?) => restrict(c, x.bit, what, span),
        (null, null) => restrict(c, other, what, span),
      };
      if (!ok) return false;
      if (p is PTuple || p is PFn) {
        final r = find(c);
        final t = p.ty;
        final uses = [for (final (_, n) in classes[r].uses) n];
        touch(r);
        classes[r].flowed.add((t, span));
        for (final n in uses) {
          checkOn(n, t, span);
        }
      }
    }
    return true;
  }

  /// Gives class `r` its type: the first of int, f64 and rat it may take if a literal that
  /// does not follow joined it, every literal adopting it; a type variable if it may take
  /// any value; its carrier if one; a type variable bounded by its carriers if several; else
  /// the unknown.
  void resolveClass(int r) {
    final (mask, lits) = (classes[r].mask, [...classes[r].lits]);
    final numeric = lits.any((l) => !l.$2)
        ? const [
            Carrier.integer,
            Carrier.f64,
            Carrier.rational,
          ].where((c) => mask & c.bit != 0).firstOrNull
        : null;
    final ty = switch (numeric) {
      final c? => Ty.carrier(c),
      null when mask == every => Ty.variable('\$$r'),
      null when mask & other == 0 && _bits(mask) == 1 => Ty.carrier(Carrier.ofMask(mask).first),
      null => Ty.variable('\$$r'),
    };
    if (ty.numericCarrier case final c?) {
      for (final (l, _) in lits) {
        adoptTo(l, c);
      }
    }
    classes[r].resolved = ty;
  }

  /// The class `p` is, if it is a class not yet resolved: its root.
  int? classOf(Piece p) {
    if (p is! PVar) return null;
    final c = classId(p.v);
    if (c == null) return null;
    final r = find(c);
    return classes[r].resolved == null ? r : null;
  }

  /// The class `ty` is, if it is one and nothing else.
  int? classOfTy(Ty ty) => switch (ty.pieces) {
    [final p] => classOf(p),
    _ => null,
  };

  /// `ty` shown with each class narrowed to some carriers shown as their union.
  String show(Ty ty) {
    final removed = <String, Ty>{};
    final parts = <String>[];
    for (final v in ty.vars) {
      if (classOf(PVar(v)) case final r?) {
        final m = classes[r].mask;
        if (m != every && m & other == 0) {
          parts.add(maskText(m));
          removed[v] = Ty.empty;
        }
      }
    }
    if (parts.isEmpty) return '$ty';
    final rest = ty.subst(removed);
    if (!rest.isEmpty) parts.add('$rest');
    return parts.join(' | ');
  }

  /// The uses that narrowed the classes in `ty`.
  List<Note> reasons(Ty ty) {
    final out = <Note>[];
    final seen = <Note>{};
    for (final p in ty.pieces) {
      if (classOf(p) case final c?) {
        out.addAll(classes[c].reasons.where(seen.add));
      }
    }
    return out;
  }

  /// For each class variable in `vars`, its root's type: the one it was given, else the
  /// root's variable.
  Binds solving(List<String> vars) {
    final b = Binds();
    for (final v in vars) {
      final c = classId(v);
      if (c == null || c >= classes.length) continue;
      final r = find(c);
      final ty = classes[r].resolved ?? Ty.variable('\$$r');
      if (ty != Ty.variable(v)) b[v] = ty;
    }
    return b;
  }

  /// `ty` with each class variable replaced by its root's type.
  Ty solved(Ty ty) {
    final vars = Vars();
    ty.varsIn(vars);
    return ty.replace(solving(vars.order));
  }

  /// `s` with each class variable replaced by its root's type.
  Sig solvedSig(Sig s) => s.replace(solving(sigVars(s)));

  /// `s` with each class variable replaced by its type, as [finish] puts it: a type variable
  /// of the function around named as one of `s`'s own takes the next name `s` does not use.
  Sig finished(Sig s) {
    final vars = sigVars(s);
    final b = solving(vars);
    final own = {
      for (final v in vars)
        if (classId(v) == null) v,
    };
    final used = {...own, for (final ty in b.values) ...ty.vars};
    final renamed = <String, String>{};
    var n = 0;
    for (final key in b.keys.toList()) {
      final ty = b[key]!;
      final v = ty.vars.where(own.contains).firstOrNull;
      if (v == null) continue;
      final to = renamed.putIfAbsent(v, () {
        var name = varName(n++);
        while (!used.add(name)) {
          name = varName(n++);
        }
        return name;
      });
      b[key] = ty.subst({v: Ty.variable(to)});
    }
    return s.replace(b);
  }

  /// Puts each class's type in place of its variable in what the checker found.
  void finish() {
    info
      ..sigs = {for (final MapEntry(:key, :value) in info.sigs.entries) key: finished(value)}
      ..calls = {for (final MapEntry(:key, :value) in info.calls.entries) key: finished(value)}
      ..tops = {for (final MapEntry(:key, :value) in info.tops.entries) key: solved(value)}
      ..errors = [
        for (final e in info.errors)
          BuildError(e.span, named(e.message), [
            for (final n in e.notes) (span: n.span, text: named(n.text)),
          ]),
      ];
  }

  /// `text` with each class variable `$k` replaced by its type.
  String named(String text) {
    final out = StringBuffer();
    var rest = text;
    while (true) {
      final i = rest.indexOf('\$');
      if (i < 0) break;
      out.write(rest.substring(0, i));
      final tail = rest.substring(i + 1);
      var n = 0;
      while (n < tail.length && tail.codeUnitAt(n) ^ 0x30 <= 9) {
        n++;
      }
      final c = int.tryParse(tail.substring(0, n));
      if (c != null && c < classes.length) {
        out.write(solved(Ty.variable('\$$c')));
      } else {
        out.write('\$${tail.substring(0, n)}');
      }
      rest = tail.substring(n);
    }
    out.write(rest);
    return out.toString();
  }

  /// A parameter's declared type: its annotation, or its closed default's type with each
  /// carrier widened to the whole carrier.
  _Steps paramType(Param p) sync* {
    if (p.type case final ty?) {
      _got = tyOf(ty);
      return;
    }
    final d = p.fallback;
    if (d == null || t.usesIn(d.span).isNotEmpty) {
      _got = null;
      return;
    }
    yield expr(d);
    _got = Ty.unionAll([
      Ty.empty,
      for (final piece in got.pieces)
        if (piece.carrier case final c?) Ty.carrier(c) else piece.ty,
    ]);
  }

  /// The cases of `f`'s `test` tables, each checked as a call, its expected value adopting as
  /// the right side of `==` does.
  _Steps tests(FunctionDef f, Binder b) sync* {
    final sig = info.sigs[b];
    if (sig == null || f.ports != null) return;
    for (final (input, expected) in f.tests) {
      final List<Expr> args;
      if (f.params.length == 1) {
        args = [input];
      } else if (input case Tuple(:final items) when items.length == f.params.length) {
        args = items;
      } else {
        continue;
      }
      final given = <_Arg>[];
      for (final a in args) {
        yield arg(a);
        given.add(gotArg);
      }
      final (result, _) = apply('`${f.name}`', sig, given, false, input.span);
      yield arg(expected);
      equal(_Arg(result), gotArg);
    }
  }

  /// An argument: a numeric literal kept unadopted, a function in a slot of function type
  /// fitted to it, else the expression's type.
  _Steps arg(Expr e, [Ty? expected]) sync* {
    if (literal(e) case final l?) {
      _got = _Arg(litTy(l.value, l.neg), l, e.span);
      return;
    }
    yield exprAt(e, expected);
    _got = _Arg(got, null, e.span);
  }

  /// `e`'s type where `expected` is wanted: a lambda or a declared function in a slot of one
  /// function type is fitted to it, and a numeric literal adopts its one carrier.
  _Steps exprAt(Expr e, Ty? expected) sync* {
    if (expected != null) {
      if (onlyFn(expected) case final sig?) {
        if (e case Lambda(:final params, :final body)) {
          yield fitLambda(params, body, sig, e.span);
          return;
        }
        if (declared(e) case final b?) {
          _got = fitDeclared(b, sig, e.span);
          return;
        }
      }
      if ((literal(e), expected.numericCarrier) case (final l?, final c?)) {
        _got = adoptTo(l, c);
        return;
      }
    }
    yield expr(e);
  }

  /// The literal `l` adopting `c`, recorded; an error when it is not exactly a `c`.
  Ty adoptTo(Lit l, Carrier c) {
    final (v, m) = adopt(l, c);
    if (v != null) {
      _put(info.adopt, l.span, v);
      return litTy(v, l.neg);
    }
    if (m != null) error(l.span, m);
    return litTy(l.value, l.neg);
  }

  /// `e`'s type, recorded for derivations.
  _Steps expr(Expr e) sync* {
    yield exprOf(e);
    final ty = got;
    seen[e.span] = switch (e) {
      NameRef() => switch (t.res.uses[e.span]) {
        Bound(binders: [final b]) => _Seen(ty, e, name: b),
        _ => _Seen(ty, e),
      },
      Call(:final callee) => _Seen(ty, e, call: declared(callee)),
      _ => _Seen(ty, e),
    };
    _got = ty;
  }

  _Steps exprOf(Expr e) sync* {
    if (literal(e) case final l?) {
      _got = litTy(info.adopt[l.span] ?? l.value, l.neg);
      return;
    }
    switch (e) {
      // A `rat` literal is decorated and keeps its carrier; a literal past the size limit is
      // elaboration's error.
      case RatLit(:final text):
        _got = switch (k.Rat.decimal(text)) {
          final r? => Ty.lit(r),
          null => Ty.empty,
        };
      case IntLit() || FloatLit():
        _got = Ty.empty;
      case BoolLit(:final value):
        _got = Ty.lit(k.Bool(value));
      case AtomLit(:final name):
        _got = Ty.of(k.Type.atom(name));
      case StrLit(:final parts):
        final holes = <Ty>[];
        final text = StringBuffer();
        for (final p in parts) {
          switch (p) {
            case StrText(text: final s):
              text.write(s);
            case StrHole(:final e):
              yield expr(e);
              data(got, 'interpolation', e.span);
              holes.add(got);
          }
        }
        _got = holes.isEmpty
            ? Ty.lit(k.Str(text.toString()))
            : passed(Ty.carrier(Carrier.string), holes);
      case NameRef():
        _got = name(e.span);
      case Unary(:final op, e: final a):
        yield arg(a);
        _got = apply('`$op`', opSig(op), [gotArg], true, e.span).$1;
      case Binary(:final op, :final a, :final b):
        yield binary(op, a, b, e.span);
      case Call(:final callee, :final positional, :final named, :final curry):
        yield call(callee, positional, named, curry, e.span);
      case Index(e: final of, :final key):
        yield index(of, key, e.span);
      case Tuple(:final items):
        final tys = <Ty>[];
        for (final i in items) {
          yield expr(i);
          data(got, 'a tuple', i.span);
          tys.add(got);
        }
        _got = Ty.tuple(tys);
      case Lambda(:final params, :final body):
        yield lambda(params, body);
      case Is(:final of, :final type):
        yield expr(of);
        tyOf(type);
        _got = Ty.carrier(Carrier.boolean);
      case Else(:final of, :final pattern, :final fallback):
        yield expr(of);
        final v = got;
        if ((t.res.patterns[e.span], pattern) case (final ids?, final AtomPattern p)) {
          bindPattern(p, v, ids, 0);
        }
        yield expr(fallback);
        final d = got;
        _got = switch (pattern) {
          null => v.withoutLoose.union(d),
          AtomPattern(:final name, fields: [], items: []) =>
            v.diff(Ty.of(k.Type.atom(name))).union(d),
          _ => v.union(d),
        };
      case Block(:final stmts):
        yield scope(stmts, false);
      case If(:final cond, :final then, :final otherwise):
        yield this.cond(cond);
        final (c, yes, no) = gotCond;
        final out = passing(c, 'the condition of `if`', cond.span);
        const what = 'the condition of `if`';
        for (final p in c.pieces) {
          final ok = switch (classOf(p)) {
            final x? => restrict(x, Carrier.boolean.bit, what, cond.span),
            null => p.isAtoms || p.carrier == Carrier.boolean,
          };
          if (!ok) {
            errorWith(cond.span, '$what is ${show(c)}, not bool', [
              ...derive([cond.span]),
              ...reasons(c),
            ]);
            break;
          }
        }
        yield under(yes, then);
        final a = got;
        yield under(no, otherwise);
        _got = out.union(a).union(got);
      case Member(:final of, :final name, :final safe):
        yield member(of, name, safe, e.span, const [], const [], false, e.span);
    }
  }

  /// The loose atoms of `ty`, which flow through `what` unchanged: an atom of a named family
  /// is data, and data that selects no arrow is an error (sec:failure).
  Ty passing(Ty ty, String what, Span span) {
    if (!ty.family.isEmpty) error(span, '$what does not take ${Ty.of(ty.family)}');
    return Ty.of(ty.loose);
  }

  /// `e` checked with the binders of `facts` narrowed.
  _Steps under(_Facts facts, Expr e) sync* {
    final saved = narrow(facts);
    yield expr(e);
    widen(saved);
  }

  /// Narrows the binders of `facts`, each origin now the test; gives what to restore.
  List<(Binder, Ty?, _Origin?)> narrow(_Facts facts) => [
    for (final (b, ty, test) in facts)
      () {
        final old = whence[b];
        whence[b] = _Origin(
          test,
          '`${b.name}` is narrowed to $ty where this test decides',
          null,
          old,
        );
        final was = env[b];
        env[b] = ty;
        return (b, was, old);
      }(),
  ];

  /// Restores what [narrow] changed.
  void widen(List<(Binder, Ty?, _Origin?)> saved) {
    for (final (b, old, o) in saved.reversed) {
      if (old == null) {
        env.remove(b);
      } else {
        env[b] = old;
      }
      if (o == null) {
        whence.remove(b);
      } else {
        whence[b] = o;
      }
    }
  }

  /// A condition's type and the facts it makes when it holds and when it does not.
  _Steps cond(Expr e) sync* {
    const _Facts none = [];
    switch (e) {
      case Is(:final of, :final type, :final negated):
        yield expr(of);
        final v = got;
        final ty = tyOf(type);
        final bool_ = Ty.carrier(Carrier.boolean);
        final b = switch ((of, t.res.uses[of.span])) {
          (NameRef(), Bound(binders: [final b])) => b,
          _ => null,
        };
        if (b == null) {
          _got = (bool_, none, none);
          return;
        }
        final _Facts yes = [(b, v.meet(ty), e.span)], no = [(b, v.diff(ty), e.span)];
        _got = negated ? (bool_, no, yes) : (bool_, yes, no);
      case Unary(op: '!', e: final a):
        yield cond(a);
        final (ty, yes, no) = gotCond;
        _got = (apply('`!`', opSig('!'), [_Arg(ty)], true, e.span).$1, no, yes);
      case Binary(op: final op && ('&&' || '||'), :final a, :final b):
        yield cond(a);
        final (ta, ya, na) = gotCond;
        final saved = narrow(op == '&&' ? ya : na);
        yield cond(b);
        final (tb, yb, nb) = gotCond;
        widen(saved);
        final ty = apply('`$op`', opSig('&&'), [_Arg(ta), _Arg(tb)], true, e.span).$1;
        _got = op == '&&' ? (ty, [...ya, ...yb], none) : (ty, none, [...na, ...nb]);
      default:
        yield expr(e);
        _got = (got, none, none);
    }
  }

  _Steps binary(String op, Expr a, Expr b, Span span) sync* {
    switch (op) {
      case '&&' || '||':
        yield cond(a);
        final (ta, ya, na) = gotCond;
        yield under(op == '&&' ? ya : na, b);
        _got = apply('`$op`', opSig('&&'), [_Arg(ta), _Arg(got)], true, span).$1;
      case '==' || '!=':
        yield arg(a);
        final x = gotArg;
        yield arg(b);
        final y = gotArg;
        data(x.ty, '`$op`', span);
        data(y.ty, '`$op`', span);
        equal(x, y);
        _got = Ty.carrier(Carrier.boolean);
      case '<' || '<=' || '>' || '>=':
        yield arg(a);
        final x = gotArg;
        yield arg(b);
        _got = compare(op, x, gotArg, span);
      default:
        yield arg(a);
        final x = gotArg;
        yield arg(b);
        final y = gotArg;
        // A divisor whose type holds no zero cannot fail with `#divByZero`.
        final nonzero =
            (op == '/' || op == 'div' || op == 'mod') &&
            !y.ty.contains(const k.Int(0)) &&
            !y.ty.contains(k.Rat.integer(BigInt.zero));
        final carried = [x.ty, y.ty].any((t) => t.atomSet.contains(divByZero));
        if (op == '**') exponent(x, y, b, span);
        final r = apply('`$op`', opSig(op), [x, y], true, span).$1;
        _got = nonzero && !carried ? r.diff(Ty.of(k.Type.atom('divByZero'))) : r;
    }
  }

  /// `==` and `!=`: any two values; a literal adopts the other side's one numeric carrier,
  /// and of two literals the integer adopts the other's.
  void equal(_Arg x, _Arg y) {
    switch ((x.lit, y.lit)) {
      case (final l?, final m?):
        final (lc, mc) = (litCarrier(l.value), litCarrier(m.value));
        if (rank(lc) < rank(mc)) {
          adoptTo(l, mc);
        } else if (rank(mc) < rank(lc)) {
          adoptTo(m, lc);
        }
      case (final l?, null):
        follow(l, y.ty);
      case (null, final m?):
        follow(m, x.ty);
      case (null, null):
        break;
    }
  }

  /// The literal `l` compared with a value of `ty`: it adopts `ty`'s one numeric carrier, or
  /// follows its class.
  void follow(Lit l, Ty ty) {
    if (classOfTy(ty) case final c?) {
      join(c, l, true);
    } else if (ty.numericCarrier case final c?) {
      adoptTo(l, c);
    }
  }

  /// An ordering: two values of one carrier, or two tuples of one length; atoms pass.
  Ty compare(String op, _Arg x, _Arg y, Span span) {
    final what = '`$op`';
    if (x.ty.tuples.isEmpty && y.ty.tuples.isEmpty) {
      return apply(what, opSig('<'), [x, y], true, span).$1;
    }
    final out = passing(x.ty, what, span).union(passing(y.ty, what, span));
    components(what, x.ty.withoutLoose, y.ty.withoutLoose, span);
    return out.union(Ty.carrier(Carrier.boolean));
  }

  /// Checks that each value of `a` compares with each of `b` (sec:keys): two numbers of one
  /// carrier or two values of one other kind, the atoms as data, and two tuples component by
  /// component as far as the shorter goes, since a proper prefix comes first.
  void components(String what, Ty a, Ty b, Span span) {
    for (final (s, t) in [(a, b), (b, a)]) {
      final atoms = !s.atomSet.isEmpty;
      for (final p in t.pieces) {
        final ok = switch (classOf(p)) {
          final k? when s.tuples.isNotEmpty => restrict(k, other, what, span),
          _? => true,
          null => switch (p) {
            PDyn() => false,
            PVar() || PTuple() => true,
            _ when s.tuples.isNotEmpty => false,
            _ => !atoms || p.isAtoms || p.carrier == null,
          },
        };
        if (!ok) {
          final q = s.tuples.isEmpty ? 'an atom' : 'a tuple';
          error(span, '$what does not compare ${p.ty} with $q');
          return;
        }
      }
    }
    for (final s in a.tuples) {
      for (final t in b.tuples) {
        for (var i = 0; i < s.length && i < t.length; i++) {
          components(what, s[i], t[i], span);
        }
      }
    }
    final (x, y) = (a.withoutAtoms.withoutTuples, b.withoutAtoms.withoutTuples);
    if (!x.isEmpty && !y.isEmpty) apply(what, opSig('<'), [_Arg(x), _Arg(y)], true, span);
  }

  Ty name(Span span) => switch (t.res.uses[span]) {
    Bound(binders: [final b]) => env[b] ?? Ty.dynamic,
    Prelude(:final word) when word != 'sum' => Ty.func(wordSig(word)),
    // Elaboration rejects a use of an overloaded name.
    Bound() => Ty.empty,
    _ => Ty.dynamic,
  };

  /// The declared function that `e` names, if it names exactly one.
  Binder? declared(Expr e) => switch ((e, t.res.uses[e.span])) {
    (NameRef(), Bound(binders: [final b])) when t.funcs.containsKey(b) => b,
    _ => null,
  };

  _Steps call(
    Expr callee,
    List<Expr> positional,
    List<(String, Expr)> named,
    bool curry,
    Span span,
  ) sync* {
    if (callee case Member(:final of, :final name, :final safe)) {
      yield member(of, name, safe, callee.span, positional, named, curry, span);
      return;
    }
    if (callee case AtomLit(:final name)) {
      final items = <Ty>[];
      for (final a in positional) {
        yield expr(a);
        items.add(got);
      }
      final fields = SplayTreeMap<String, Ty>();
      for (final (n, a) in named) {
        yield expr(a);
        fields[n] = got;
      }
      _got = Ty.of(k.Type.atomWith(name, k.Type.top)).withPayloads({
        name: [Shape(items, fields)],
      });
      return;
    }
    if (declared(callee) case final b?) {
      final sig = switch (env[b]) {
        final ty? => onlyFn(ty),
        null => null,
      };
      final from = info.errors.length;
      final fname = t.funcs[b]!.name;
      if (sig == null) {
        _got = Ty.dynamic;
      } else {
        final (p, n) = _srcs(positional, named);
        yield callSig(sig, true, null, p, n, curry, span, fname);
      }
      if ((whence[b], sig) case (final o?, final sig?)) {
        also(from, (span: o.span, text: '`$fname` is declared here, `$sig`'));
      }
      return;
    }
    yield expr(callee);
    final f = got;
    final what = switch (callee) {
      NameRef(:final name) => name,
      _ => 'this value',
    };
    if ((callee, t.res.uses[callee.span]) case (NameRef(name: final w), Prelude())) {
      if (named.isEmpty && !curry && positional.length == 1) {
        yield word(w, positional, null, span);
        return;
      }
      for (final a in [...positional, for (final (_, a) in named) a]) {
        yield expr(a);
      }
      // Elaboration reports named arguments and `...`.
      if (named.isEmpty && !curry) error(span, '`$w` takes one argument');
      _got = Ty.empty;
      return;
    }
    final (p, n) = _srcs(positional, named);
    yield callValue(f, what, null, p, n, curry, span);
  }

  /// A prelude word applied to one argument, the receiver or the only positional one.
  _Steps word(String w, List<Expr> positional, _Arg? receiver, Span span) sync* {
    var x = receiver;
    if (x == null) {
      yield arg(positional[0]);
      x = gotArg;
    }
    if (w == 'String') data(x.ty, '`String`', span);
    _got = w == 'sum' ? sum(x.ty, span) : apply('`$w`', wordSig(w), [x], true, span).$1;
  }

  /// `sum` of a tuple: its components added in turn, `0` for the empty tuple; atoms pass.
  Ty sum(Ty ty, Span span) {
    var out = passing(ty, '`sum`', span);
    final add = opSig('+');
    for (final p in ty.pieces) {
      switch (p) {
        case PTuple(:final cs):
          if (cs.isEmpty) {
            out = out.union(Ty.lit(const k.Int(0)));
            continue;
          }
          var acc = cs[0];
          for (final c in cs.skip(1)) {
            acc = apply('`sum`', add, [_Arg(acc), _Arg(c)], true, span).$1;
          }
          final bad = acc.pieces
              .where(
                (p) => p is! PVar && !p.isAtoms && !(p.carrier?.numeric ?? false),
              )
              .firstOrNull;
          if (bad != null) error(span, '`sum` does not take (${bad.ty})');
          out = out.union(acc);
        case PDyn():
          any('`sum`', span);
        case PVar():
          out = out.union(Ty.dynamic);
        case _ when p.isAtoms:
          break;
        default:
          error(span, '`sum` does not take (${p.ty})');
      }
    }
    return out;
  }

  /// A call through a value: each function its type holds, applied; an atom passes.
  _Steps callValue(
    Ty f,
    String what,
    _Arg? receiver,
    List<_Src> positional,
    List<(String, _Src)> named,
    bool curry,
    Span span,
  ) sync* {
    var out = passing(f, 'a call', span);
    var checked = false;
    // A class's calls are recorded with the arguments' types, found once.
    if (f.pieces.any((p) => classOf(p) != null)) {
      final p = <_Src>[];
      for (final a in positional) {
        if (a case _SrcExpr(:final e)) {
          yield arg(e);
          p.add(_SrcGot(gotArg));
        } else {
          p.add(a);
        }
      }
      final n = <(String, _Src)>[];
      for (final (m, a) in named) {
        if (a case _SrcExpr(:final e)) {
          yield arg(e);
          n.add((m, _SrcGot(gotArg)));
        } else {
          n.add((m, a));
        }
      }
      (positional, named) = (p, n);
    }
    Ty tyOfSrc(_Src a) => (a as _SrcGot).a.ty;
    if (f.fns.firstOrNull case final s? when f.fns.every((g) => g.sameKinds(s))) {
      _put(info.calls, span, s);
    }
    for (final p in f.pieces) {
      switch (p) {
        case PFn(:final s):
          checked = true;
          yield callSig(s, false, receiver?.copy(), positional, named, curry, span, what);
          out = out.union(got);
        case PVar() when classOf(p) != null:
          checked = true;
          final kind = NCall(
            what,
            [if (receiver != null) receiver.ty, for (final a in positional) tyOfSrc(a)],
            [for (final (m, a) in named) (m, tyOfSrc(a))],
            curry,
          );
          out = out.union(need(classOf(p)!, kind, true, span));
        case PDyn():
          any('a call of `$what`', span);
        case PVar():
          out = out.union(Ty.dynamic);
        case _ when p.isAtoms:
          break;
        default:
          error(span, '`$what` is ${p.ty}, not a function');
      }
    }
    if (!checked) {
      for (final a in [...positional, for (final (_, a) in named) a]) {
        if (a case _SrcExpr(:final e)) yield expr(e);
      }
    }
    _got = out;
  }

  /// A call of a function of signature `sig`; `isDeclared` when it is the declared function
  /// itself, whose defaults every call can fill, and not a value of its type, which fills
  /// only closed ones. A call whose arguments do not fit gives the unknown; elaboration
  /// reports it when the call is of the declared function or of one recorded signature, and
  /// this check otherwise.
  _Steps callSig(
    Sig sig,
    bool isDeclared,
    _Arg? receiver,
    List<_Src> positional,
    List<(String, _Src)> named,
    bool curry,
    Span span,
    String what,
  ) sync* {
    Iterable<Iterable<Object?>> unfitted() => unfit(sig, isDeclared, positional, named, span, what);
    final n = sig.params.length;
    final slots = List<_Src?>.filled(n, null);
    var next = 0;
    final hasReceiver = receiver != null;
    if (hasReceiver) {
      if (n == 0) {
        yield unfitted();
        return;
      }
      next = 1;
    }
    for (final a in positional) {
      if (next >= n ||
          !(sig.params[next].positional ||
              !isDeclared && sig.params.every((p) => p.positional))) {
        yield unfitted();
        return;
      }
      slots[next++] = a;
    }
    // Each parameter's index by name, the first where a name repeats.
    final at = <String, int>{};
    for (final (j, p) in sig.params.indexed) {
      at.putIfAbsent(p.name, () => j);
    }
    for (final (name, a) in named) {
      final j = at[name];
      if (j == null || sig.params[j].positional || slots[j] != null || hasReceiver && j == 0) {
        yield unfitted();
        return;
      }
      slots[j] = a;
    }
    final missing = [
      for (var j = 0; j < n; j++)
        if (slots[j] == null && !(hasReceiver && j == 0)) j,
    ];
    if (curry
        ? missing.isEmpty || missing.any((j) => sig.params[j].positional)
        : missing.any((j) {
            final d = sig.params[j].fallback;
            return d == null || !(isDeclared || d.closed);
          })) {
      yield unfitted();
      return;
    }
    final args = <_Arg?>[];
    for (final (j, s) in slots.indexed) {
      switch (s) {
        case _ when hasReceiver && j == 0:
          args.add(receiver);
        case _SrcExpr(:final e):
          yield arg(e, Ty.unionAll([for (final ar in sig.arrows) ar.params[j]]));
          args.add(gotArg);
        case _SrcGot(:final a):
          args.add(a.copy());
        case null:
          args.add(null);
      }
    }
    _got = curry
        ? partial(sig, args, missing, false, what, span)
        : apply('`$what`', sig, args, false, span).$1;
  }

  /// [callSig] of a call whose arguments do not fit `sig`: the unknown. Elaboration reports a
  /// call of the declared function or of one recorded signature; this check reports the rest.
  _Steps unfit(
    Sig sig,
    bool isDeclared,
    List<_Src> positional,
    List<(String, _Src)> named,
    Span span,
    String what,
  ) sync* {
    final all = [...positional, for (final (_, a) in named) a];
    if (!isDeclared && (all.any((a) => a is _SrcGot) || !info.calls.containsKey(span))) {
      for (final a in all) {
        if (a case _SrcExpr(:final e)) yield expr(e);
      }
      error(span, '`$what` does not take these arguments: it is `$sig`');
    }
    _got = Ty.empty;
  }

  /// A partial application of `sig`: the arguments `args`, those at `missing` left out, gives
  /// a function of the missing parameters, positional ones with no default for a `section`.
  /// The needs on the variables only those parameters hold are the new function's.
  Ty partial(
    Sig sig,
    List<_Arg?> args,
    List<int> missing,
    bool section,
    String what,
    Span span,
  ) {
    final out = List.filled(sig.params.length, false);
    for (final j in missing) {
      out[j] = true;
    }
    final (given, left) = (Vars(), Vars());
    for (final a in sig.arrows) {
      for (final (j, p) in a.params.indexed) {
        p.varsIn(out[j] ? left : given);
      }
    }
    final g = given.order.toSet();
    defer = SplayTreeSet.of(left.order.where((v) => !g.contains(v)));
    final (result, kept) = apply('`$what`', sig, args, false, span);
    final applied = lastApplied;
    lastApplied = null;
    if (applied == null || missing.isEmpty) return result;
    final (binds, needs) = applied;
    final params = [
      for (final j in missing)
        section
            ? SParam(sig.params[j].name, true)
            : sig.params[j],
    ];
    final arrows = [
      for (final c in kept)
        Arrow([for (final j in missing) sig.arrows[c].params[j]], sig.arrows[c].result),
    ];
    final rest = Sig(
      params,
      arrows,
      bounds: SplayTreeMap.of(sig.bounds),
      needs: needs,
      own: SplayTreeSet.of(sig.own),
    );
    return Ty.func(rest.replace(binds));
  }

  /// `x.f(args)` and `x?.f(args)`: the call `f(x, args)`; `?.` passes `x`'s atoms around it.
  _Steps member(
    Expr of,
    String name,
    bool safe,
    Span member,
    List<Expr> positional,
    List<(String, Expr)> named,
    bool curry,
    Span span,
  ) sync* {
    yield arg(of);
    var x = gotArg;
    final atoms = x.ty.loose;
    if (safe) x = _Arg(x.ty.withoutLoose);
    _got = Ty.dynamic;
    final (p, n) = _srcs(positional, named);
    switch (t.res.uses[member]) {
      case Bound(binders: [final b]) when t.funcs.containsKey(b):
        if (onlyFn(env[b] ?? Ty.dynamic) case final sig?) {
          yield callSig(sig, true, x, p, n, curry, span, name);
        }
      case Bound(binders: [final b]):
        yield callValue(env[b] ?? Ty.dynamic, name, x, p, n, curry, span);
      case Bound():
        _got = Ty.empty;
      case _ when preludeLayer(name) == 1 && positional.isEmpty && named.isEmpty && !curry:
        yield word(name, const [], x, span);
      default:
        break;
    }
    if (safe) _got = got.union(Ty.of(atoms));
  }

  /// `f[k]` on a declared function is a section; `t[i]` with a literal `i` the tuple's
  /// component; else an application.
  _Steps index(Expr of, Expr key, Span span) sync* {
    if (declared(of) case final b?) {
      final sig = switch (env[b]) {
        final ty? => onlyFn(ty),
        null => null,
      };
      if (sig == null) {
        yield expr(key);
        _got = Ty.dynamic;
        return;
      }
      // Elaboration rejects a section of a function of no parameters.
      final n = sig.params.length;
      if (n == 0) {
        yield expr(key);
        _got = Ty.empty;
        return;
      }
      yield arg(key, Ty.unionAll([for (final a in sig.arrows) a.params[0]]));
      final args = List<_Arg?>.filled(n, null)..[0] = gotArg;
      _got = partial(sig, args, [for (var j = 1; j < n; j++) j], true, t.funcs[b]!.name, span);
      return;
    }
    yield expr(of);
    final v = got;
    if (key is! IntLit) {
      yield arg(key);
      _got = atKey(v, gotArg, span);
      return;
    }
    final i = switch (literal(key)?.value) {
      k.Int(:final value) => value,
      _ => null,
    };
    if (i == null) {
      _got = Ty.dynamic;
      return;
    }
    yield arg(key);
    _got = atIndex(v, i >= 0 ? i : null, gotArg, span);
  }

  /// `v[x]` with `x` no literal: an application of each function `v` may be.
  Ty atKey(Ty v, _Arg x, Span span) {
    var out = passing(v, 'a call', span);
    for (final p in v.pieces) {
      switch (p) {
        case PFn(:final s):
          out = out.union(apply('this function', s, [x.copy()], false, span).$1);
        case PVar() when classOf(p) != null:
          out = out.union(need(classOf(p)!, NIndex(x.ty), true, span));
        case PDyn():
          any('an application', span);
        case PVar():
          out = out.union(Ty.dynamic);
        case _ when p.isAtoms:
          break;
        default:
          error(span, 'this value is ${p.ty}, not a function');
      }
    }
    return out;
  }

  /// `v[i]` with the literal `x`, `i` if it is a component number: a tuple's component, or
  /// a family's entry.
  Ty atIndex(Ty v, int? i, _Arg x, Span span) {
    var out = passing(v, 'an index', span);
    final shown = '${x.ty}';
    for (final p in v.pieces) {
      switch (p) {
        case PFn(:final s) when s.data:
          out = out.union(apply('this family', s, [x.copy()], true, span).$1);
        case PTuple(:final cs):
          if (i != null && i < cs.length) {
            out = out.union(cs[i]);
          } else {
            error(span, '${Ty.tuple(cs)} has no component $shown');
          }
        case PVar() when classOf(p) != null:
          out = out.union(need(classOf(p)!, NComponent(i, x.ty), true, span));
        case PDyn():
          any('`[$shown]`', span);
        case PVar():
          out = out.union(Ty.dynamic);
        case _ when p.isAtoms:
          break;
        default:
          error(span, '`[$shown]` takes a tuple, not ${p.ty}');
      }
    }
    return out;
  }

  /// A lambda with no expected type: its parameters positional, typed by their
  /// annotations; one without is generic, as a declared function's.
  _Steps lambda(List<Param> params, Expr body) sync* {
    final level = ++this.level;
    if (pending.length <= level) pending.add([]);
    final tys = <Ty>[];
    for (final p in params) {
      final ty = p.type == null ? Ty.variable('\$${newClass()}') : tyOf(p.type!);
      env[id(p.span, p.name)] = ty;
      tys.add(ty);
    }
    yield this.body(body, null);
    _got = Ty.func(
      generalize(level, Sig.one([for (final p in params) SParam(p.name, true)], tys, got)),
    );
  }

  _Steps body(Expr body, Ty? want) => switch (body) {
    Block(:final stmts) => scope(stmts, false),
    _ => exprAt(body, want),
  };

  /// A lambda in a slot of the function type `e`: its first parameters take `e`'s positional
  /// ones, in order, and the rest `e`'s named ones by name; a parameter `e` does not pass
  /// needs a default.
  _Steps fitLambda(List<Param> params, Expr body, Sig e, Span span) sync* {
    final pos = [
      for (final (j, p) in e.params.indexed)
        if (p.positional) j,
    ];
    final order = List<int?>.filled(e.params.length, null);
    final extra = <int>[];
    if (params.length < pos.length) {
      error(
        span,
        'the lambda takes ${params.length} parameter${params.length == 1 ? '' : 's'}, '
        'and `$e` passes ${pos.length} by position',
      );
      _got = Ty.func(e);
      return;
    }
    for (final (i, p) in params.indexed) {
      if (i < pos.length) {
        order[pos[i]] = i;
        continue;
      }
      final j = e.params.indexWhere((q) => !q.positional && q.name == p.name);
      if (j >= 0 && order[j] == null) {
        order[j] = i;
      } else if (p.fallback != null) {
        extra.add(i);
      } else {
        final free = [
          for (final (j, q) in e.params.indexed)
            if (!q.positional && order[j] == null) '`${q.name}`',
        ];
        final fix = free.isEmpty ? '' : ': rename it ${free[0]}';
        error(p.span, "the lambda's parameter `${p.name}` is not a parameter of `$e`$fix");
        _got = Ty.func(e);
        return;
      }
    }
    for (final arrow in e.arrows) {
      for (final (j, o) in order.indexed) {
        if (o == null) continue;
        final p = params[o];
        var ty = arrow.params[j];
        if (p.type case final declared?) {
          final a = tyOf(declared);
          if (!ty.subtype(a)) {
            error(p.span, "the lambda's parameter `${p.name}` is $a, and `$e` passes $ty");
          }
          ty = a;
        }
        env[id(p.span, p.name)] = ty;
      }
      for (final i in extra) {
        final p = params[i];
        yield expr(p.fallback!);
        env[id(p.span, p.name)] = got;
      }
      yield this.body(body, arrow.result);
      final r = got;
      if (!r.subtype(arrow.result)) {
        error(body.span, 'the lambda returns $r, and `$e` returns ${arrow.result}');
      }
    }
    final identity = extra.isEmpty && order.indexed.every((x) => x.$2 == x.$1);
    if (!identity) _put(info.fits, span, FitLambda(order, extra));
    _got = Ty.func(e);
  }

  /// A declared function in a slot of the function type `e`: the same number of positional
  /// parameters and the same named ones, in any order, and types that fit.
  Ty fitDeclared(Binder b, Sig e, Span span) {
    final f = t.funcs[b]!;
    final own = env[b] ?? Ty.dynamic;
    final s = onlyFn(own);
    if (s == null) return own;
    int pos(Sig s) => s.params.where((p) => p.positional).length;
    final from = <int>[];
    var c = 0;
    var ok = pos(s) == pos(e) && s.params.length == e.params.length;
    final epos = [
      for (final (j, p) in e.params.indexed)
        if (p.positional) j,
    ];
    for (final p in s.params) {
      if (!ok) break;
      if (p.positional) {
        from.add(epos[c++]);
      } else {
        final j = e.params.indexWhere((q) => !q.positional && q.name == p.name);
        if (j >= 0) {
          from.add(j);
        } else {
          ok = false;
        }
      }
    }
    if (!ok) {
      final names = [for (final p in f.params) p.name];
      final kinds = [for (final p in s.params) p.positional ? 'positional ${p.name}' : p.name];
      error(
        span,
        'the parameters of `${f.name}` (${kinds.join(', ')}) do not fit `$e`: declare them as '
        'it passes them, with `positional` where it passes by position, or pass a lambda, '
        '(${names.join(', ')}) -> ${f.name}(${[for (final n in names) '$n: $n'].join(', ')})',
      );
      return Ty.func(e);
    }
    // `s` with its parameters in `e`'s order.
    final inv = List.filled(from.length, 0);
    for (final (i, j) in from.indexed) {
      inv[j] = i;
    }
    final permuted = Sig(
      e.params,
      [for (final a in s.arrows) Arrow([for (final i in inv) a.params[i]], a.result)],
      bounds: SplayTreeMap.of(s.bounds),
      data: s.data,
      needs: s.needs,
      own: s.own,
    );
    final fits = permuted.needs.isEmpty
        ? fitsSig(permuted, e)
        : fitNeeds(permuted, Ty.func(e), Binds(), '`${f.name}`', span);
    if (!fits) error(span, '`${f.name}` is `$s`, not `$e`');
    if (from.indexed.any((x) => x.$1 != x.$2)) _put(info.fits, span, FitAdapter(from));
    return Ty.func(e);
  }

  /// The type a type expression denotes; a name it does not know is elaboration's error.
  Ty tyOf(TypeExpr ty) => switch (ty) {
    TypeName(:final name) => switch (name) {
      'int' => Ty.carrier(Carrier.integer),
      'rat' => Ty.carrier(Carrier.rational),
      'f64' => Ty.carrier(Carrier.f64),
      'bool' => Ty.carrier(Carrier.boolean),
      'String' => Ty.carrier(Carrier.string),
      'Lines' => port(true),
      'Files' => port(false),
      _ => Ty.empty,
    },
    AtomType(:final name) => Ty.of(k.Type.atom(name)),
    TupleType(:final items) => Ty.tuple([for (final i in items) tyOf(i)]),
    UnionType(:final items) => Ty.unionAll([Ty.empty, for (final i in items) tyOf(i)]),
    AndType(:final items) => switch ([for (final i in items) tyOf(i)]) {
      [] => Ty.dynamic,
      [final first, ...final rest] => rest.fold(first, (a, b) => a.meet(b)),
    },
    DiffType(:final a, :final b) => tyOf(a).diff(tyOf(b)),
    ArrowType(:final params, :final result) => () {
      final tys = [for (final p in params) tyOf(p.type)];
      return Ty.func(
        Sig.one(
          [for (final p in params) SParam(p.name ?? '', p.positional || p.name == null)],
          tys,
          tyOf(result),
        ),
      );
    }(),
  };

  /// The derivation of an application `apply` rejects: each argument's, in order, then each
  /// arrow of `sig`, the constraints it failed.
  List<Note> applied(String what, Sig sig, List<_Arg?> args, Span span) {
    final out = <Note>[];
    for (final a in args.nonNulls) {
      switch ((a.lit, a.at)) {
        case (final l?, final at?):
          out.add((span: at, text: 'this literal, ${l.text}, is ${a.ty}'));
        case (null, final at?):
          deriveInto([at], out);
        default:
          break;
      }
    }
    for (final arrow in sig.arrows) {
      final one = Sig(sig.params, [arrow], bounds: sig.bounds, data: sig.data, own: sig.own);
      out.add((span: span, text: '$what takes $one'));
    }
    return out;
  }

  /// The repairs of a rejected application the checker discharges: each argument wrapped in
  /// a prelude word, when the application then checks, tried with the checker's state
  /// restored after.
  List<Note> repairs(String what, Sig sig, List<_Arg?> args, bool pass, Span span) {
    final out = <Note>[];
    if (trying) return out;
    for (final (i, a) in args.indexed) {
      if (a == null || a.lit != null || a.at == null) continue;
      for (final w in const ['String', 'int', 'rat', 'f64']) {
        final r = converted(wordSig(w), a.ty);
        if (r == null) continue;
        final withR = [...args]..[i] = _Arg(r);
        final saved = mark();
        trying = true;
        apply(what, sig, withR, pass, span);
        final ok = info.errors.length == saved.errors;
        trying = false;
        undo(saved);
        if (ok) {
          out.add((span: a.at!, text: 'repair: wrap this in `$w(…)`; the checker accepts that'));
        }
      }
    }
    return out;
  }

  /// Adds `note` to each error from the `from`th on that lacks it.
  void also(int from, Note note) {
    for (var i = from; i < info.errors.length; i++) {
      final e = info.errors[i];
      if (!e.notes.contains(note)) {
        info.errors[i] = BuildError(e.span, e.message, [...e.notes, note]);
      }
    }
  }

  /// Applies `sig` to `args`, a missing one filled by its default. When `pass` holds, as for
  /// an operator or a prelude word, an argument's atoms pass through, two arguments' merged
  /// into `#errs`. Gives the result and the arrows kept.
  (Ty, List<int>) apply(String what, Sig sig, List<_Arg?> given, bool pass, Span span) {
    final args = [for (final a in given) a?.copy()];
    var out = Ty.empty;
    if (pass) {
      out = passed(out, [
        for (final a in args.nonNulls)
          if (a.lit == null) Ty.of(a.ty.loose),
      ]);
      for (final a in args.nonNulls) {
        a.ty = a.ty.withoutLoose;
      }
    } else {
      final atoms = <Ty>[];
      for (final (i, a) in args.indexed) {
        if (a == null) continue;
        final loose = a.ty.loose;
        final at = a.at;
        if (at == null || loose.isEmpty || !refuses(sig, i, loose)) continue;
        atoms.add(Ty.of(loose));
        a.ty = a.ty.withoutLoose;
        final v = info.passes[span] ?? const <Span>[];
        if (!v.contains(at)) _put(info.passes, span, [...v, at]);
      }
      out = passed(out, atoms);
    }
    final taken = defer;
    defer = SplayTreeSet();
    final (ty, kept, message) = sig.arrows.length == 1
        ? applyOne(what, sig, args, taken, span)
        : applyMany(what, sig, args, span);
    if (sig.arrows.length != 1) lastApplied = null;
    if (message == null) return (out.union(ty), kept);
    lastApplied = null;
    final notes = applied(what, sig, args, span);
    final seen = {...notes};
    for (final a in args.nonNulls) {
      notes.addAll(reasons(a.ty).where(seen.add));
    }
    notes.addAll(repairs(what, sig, args, pass, span));
    errorWith(span, message, notes);
    return (out, const []);
  }

  /// Whether no arrow of `sig` takes any of the atoms `loose` at parameter `i`, so that an
  /// argument's loose atoms pass through the call: the parameter is a variable bounded to
  /// carriers, or a type that holds none of them.
  bool refuses(Sig sig, int i, k.Type loose) => sig.arrows.every((arrow) {
    final p = arrow.params[i];
    for (final MapEntry(key: v, value: m) in sig.bounds.entries) {
      if (p == Ty.variable(v)) return m & other == 0;
    }
    return !p.isDynamic && p.vars.isEmpty && classOfTy(p) == null && (p.set & loose).isEmpty;
  });

  /// The message of an application that does not check: the arguments, each class shown as
  /// the carriers left to it.
  String rejected(String what, List<_Arg?> args, [(int, Piece)? at]) {
    final shown = [
      for (final (i, a) in args.indexed)
        if (at != null && at.$1 == i) show(at.$2.ty) else if (a != null) show(a.ty) else '_',
    ];
    return '$what does not take (${shown.join(', ')})';
  }

  /// [apply] of a signature of one arrow. The arguments at the parameters that are one
  /// bounded variable share a carrier: their classes merge, and their literals adopt it.
  /// Every other argument is checked piece by piece, a class taking the carriers its
  /// parameter allows. Gives the result, the arrows kept and, when it does not check, the
  /// message.
  (Ty, List<int>, String?) applyOne(
    String what,
    Sig sig,
    List<_Arg?> args,
    Set<String> defer,
    Span span,
  ) {
    final arrow = sig.arrows[0];
    (Ty, List<int>, String?) fail() => (Ty.empty, const [], rejected(what, args));
    final binds = Binds();
    final grouped = List.filled(args.length, false);
    for (final MapEntry(key: v, value: m) in sig.bounds.entries) {
      final at = [
        for (var i = 0; i < args.length; i++)
          if (args[i] != null && arrow.params[i] == Ty.variable(v)) i,
      ];
      final litAt = at.any((i) => args[i]!.lit != null);
      if (at.length < 2 && !litAt) continue;
      var carriers = 0;
      final classes = <int>[];
      final lits = <Lit>[];
      for (final i in at) {
        grouped[i] = true;
        final a = args[i]!;
        if (a.lit case final l?) {
          lits.add(l);
          continue;
        }
        for (final p in a.ty.pieces) {
          switch ((classOf(p), p.carrier)) {
            case (final c?, _):
              classes.add(c);
            case _ when p is PVar:
              break;
            case (null, final c?):
              carriers |= c.bit;
            case (null, null):
              return fail();
          }
        }
      }
      final Ty bound;
      if (_bits(carriers) > 1) {
        return fail();
      } else if (_bits(carriers) == 1) {
        final c = Carrier.ofMask(carriers).first;
        if (m & carriers == 0) return fail();
        for (final x in classes) {
          if (!restrict(x, c.bit, what, span)) return fail();
        }
        for (final l in lits) {
          if (litCarrier(l.value) != c && !adoptable(l, c)) return fail();
          adoptTo(l, c);
        }
        bound = Ty.carrier(c);
      } else if (classes.isNotEmpty) {
        final x = classes[0];
        for (final j in classes.skip(1)) {
          if (!merge(x, j, what, span)) return fail();
        }
        if (!restrict(x, m, what, span)) return fail();
        for (final l in lits) {
          if (!join(x, l, false)) return fail();
        }
        bound = Ty.variable('\$${find(x)}');
      } else if (lits.isNotEmpty) {
        // The carrier of the bound its literals adopt fewest times to.
        int? adoptions(Carrier c) => lits.every((l) => adoptable(l, c))
            ? lits.where((l) => litCarrier(l.value) != c).length
            : null;
        Carrier? best;
        int? fewest;
        for (final c in Carrier.ofMask(m)) {
          final n = adoptions(c);
          if (n != null && (fewest == null || n < fewest)) (best, fewest) = (c, n);
        }
        if (best == null) return fail();
        for (final l in lits) {
          adoptTo(l, best);
        }
        bound = Ty.carrier(best);
      } else {
        bound = Ty.dynamic;
      }
      binds[v] = bound;
    }
    for (final (i, a) in args.indexed) {
      if (a == null || grouped[i]) continue;
      final p = arrow.params[i];
      // A parameter that is a class of the function around: the argument flows into it.
      if (classOfTy(p) case final c?) {
        final ok = switch (a.lit) {
          final l? => join(c, l, false),
          null => flow(c, a.ty, what, span),
        };
        if (!ok) return fail();
        continue;
      }
      if (a.lit case final l?) {
        final Ty ty;
        if (p.numericCarrier case final c?) {
          // A literal that cannot adopt is its own error, and the application's none.
          if (adopt(l, c).$2 != null) {
            adoptTo(l, c);
            continue;
          }
          ty = adoptTo(l, c);
        } else {
          ty = a.ty;
        }
        if (!ty.sub(p, binds)) return fail();
        continue;
      }
      for (final piece in a.ty.pieces) {
        final c = classOf(piece);
        final bool ok;
        if (piece is PDyn) {
          ok = p.isDynamic;
        } else if (c != null && p.isDynamic) {
          ok = true;
        } else if (c != null && p.vars.isNotEmpty) {
          ok = a.ty.ofPiece(piece).sub(p, binds);
        } else if (c != null) {
          if (p.tuples.isNotEmpty || p.fns.isNotEmpty) need(c, NInto(what, p), false, span);
          ok = restrict(c, maskOf(p), what, span);
        } else if (piece case PFn(:final s) when s.needs.isNotEmpty && p.fns.isNotEmpty) {
          ok = fitNeeds(s, p, binds, what, span);
        } else {
          ok = a.ty.ofPiece(piece).sub(p, binds);
        }
        if (!ok) return (Ty.empty, const [], rejected(what, args, (i, piece)));
      }
    }
    // The variables of the parameters of a function the call gives, which only its calls
    // bind: the needs on them are its own.
    final partial = defer.isNotEmpty;
    final deferred = {...defer};
    final taken = Vars();
    for (final p in arrow.params) {
      p.varsIn(taken);
    }
    final inner = Vars();
    for (final s in arrow.result.fns) {
      for (final a in s.arrows) {
        for (final p in a.params) {
          p.varsIn(inner);
        }
      }
    }
    final takenSet = taken.order.toSet();
    deferred.addAll(inner.order.where((v) => !takenSet.contains(v)));
    var left = replay(what, sig.needs, binds, deferred, span);
    // Each bounded variable's binding is within its bound, and of one carrier, or of other
    // values only: the arrows of an operator each take one. So the classes in it merge, and
    // what else it holds flows into them.
    for (final MapEntry(key: v, value: m) in sig.bounds.entries) {
      final ty = binds[v];
      if (ty == null) continue;
      var kinds = 0;
      int? cls;
      var rest = Ty.empty;
      for (final piece in ty.pieces) {
        var ok = false;
        switch ((classOf(piece), piece.carrier)) {
          case (final c?, _):
            if (!restrict(c, m, what, span)) {
              ok = false;
            } else if (cls == null) {
              cls = c;
              ok = true;
            } else {
              ok = merge(cls, c, what, span);
            }
          case _ when piece is PDyn:
            break;
          case _ when piece is PVar:
            ok = true;
          case (null, final c?):
            kinds |= c.bit;
            rest = rest.union(piece.ty);
            ok = m & c.bit != 0;
          case (null, null):
            kinds |= other;
            rest = rest.union(piece.ty);
            ok = m & other != 0;
        }
        if (!ok || _bits(kinds) > 1) return fail();
      }
      if (cls != null && kinds != 0 && !flow(cls, rest, what, span)) return fail();
    }
    binds.removeWhere((v, _) => classId(v) != null);
    var out = Ty.empty;
    final given = args.nonNulls.toList();
    if (given.any((a) => a.ty.isDynamic)) out = out.union(Ty.dynamic);
    if (given.every((a) => a.lit != null || a.ty.pieces.any((p) => p is! PDyn))) {
      final result = close(arrow.result.replace(binds), sig);
      if (partial) {
        out = out.union(result);
      } else {
        final (held, now) = hold(result, [for (final n in left) n.replace(binds)]);
        replay(what, now, binds, const {}, span);
        left = [];
        out = out.union(held);
      }
    }
    lastApplied = (binds, left);
    return (out, const [0], null);
  }

  /// [apply] of a signature of several arrows, each over one carrier or a tuple: an
  /// operator, a prelude word, or a section of one. The classes of the arguments merge, since
  /// every arrow takes one carrier for all its parameters, and its literals join them;
  /// without a class, each literal adopts the carrier of its parameter on the arrows that
  /// adopt fewest. Then the arguments' pieces are taken in turn, each state the arrows still
  /// alive: a state per set of arrows, not per combination of pieces.
  (Ty, List<int>, String?) applyMany(String what, Sig sig, List<_Arg?> args, Span span) {
    int? cls;
    for (final a in args.nonNulls) {
      for (final p in a.ty.pieces) {
        if (classOf(p) case final c?) {
          if (cls == null) {
            cls = c;
          } else if (!merge(cls, c, what, span)) {
            return (Ty.empty, const [], rejected(what, args));
          }
        }
      }
    }
    var kept = <int>[];
    if (cls != null) {
      for (final a in args.nonNulls) {
        if (a.lit case final l? when !join(cls, l, false)) {
          return (Ty.empty, const [], rejected(what, args));
        }
      }
      kept = [for (var j = 0; j < sig.arrows.length; j++) j];
    } else {
      switch (fewest(what, sig, args)) {
        case (_, final m?):
          return (Ty.empty, const [], m);
        case (null, null):
          return (Ty.dynamic, const [], null);
        case (final ks?, null):
          kept = ks;
      }
    }
    // The states: the arrows alive, whether a piece was unknown, and the first pieces that
    // reached it, by argument.
    final n = args.length;
    var states = <(List<int>, bool, List<Piece?>)>[(kept, false, [])];
    for (final (i, a) in args.indexed) {
      final List<Piece?> pieces = switch (a) {
        null => [null],
        _ when a.lit != null && cls != null => [PVar('\$$cls')],
        _ => a.ty.pieces,
      };
      final next = <(List<int>, bool, List<Piece?>)>[];
      for (final (alive, dyn, path) in states) {
        for (final p in pieces) {
          final (List<int>, bool) state = switch (p) {
            null => (alive, dyn),
            // A class may still take any value its mask allows, so it keeps every arrow;
            // the restriction after the arguments narrows it.
            _ when classOf(p) != null => (alive, dyn),
            PVar() => (alive, true),
            _ => (
              [
                for (final c in alive)
                  if (p.ty.sub(sig.arrows[c].params[i], Binds())) c,
              ],
              dyn,
            ),
          };
          if (!next.any((s) => listEq(s.$1, state.$1) && s.$2 == state.$2)) {
            next.add((state.$1, state.$2, [...path, p]));
          }
        }
      }
      states = next;
    }
    var out = Ty.empty;
    for (final (alive, dyn, path) in states) {
      String shown() =>
          '$what does not take (${[for (final p in path) p == null ? '_' : show(p.ty)].join(', ')})';
      final at = [
        for (var i = 0; i < n; i++)
          if (path[i] case final p? when classOf(p) != null) i,
      ];
      if (cls != null && at.isNotEmpty) {
        int maskAt(Arrow a) => at.fold(every, (m, i) => m & maskOf(a.params[i]));
        final m = alive.fold(0, (m, j) => m | maskAt(sig.arrows[j]));
        if (alive.isEmpty || !restrict(cls, m, what, span)) return (Ty.empty, const [], shown());
        if (dyn) {
          out = out.union(Ty.dynamic);
          continue;
        }
        final r = find(cls);
        final km = classes[r].mask;
        final rel = [
          for (final j in alive)
            if (maskAt(sig.arrows[j]) & km != 0) sig.arrows[j],
        ];
        final follows = rel.every((a) {
          final m = maskAt(a);
          if (_bits(m) != 1) return false;
          if (Carrier.ofMask(m).firstOrNull case final c?) return Ty.carrier(c).subtype(a.result);
          return false;
        });
        if (follows) {
          out = out.union(Ty.variable('\$$r'));
          for (final a in rel) {
            out = out.union(Ty.of(a.result.atomSet));
          }
        } else {
          for (final a in rel) {
            out = out.union(close(a.result, sig));
          }
        }
      } else if (dyn) {
        out = out.union(Ty.dynamic);
      } else {
        if (alive.isEmpty) return (Ty.empty, const [], shown());
        final a = sig.arrows[alive[0]];
        final binds = Binds();
        for (final (i, p) in path.indexed) {
          p?.ty.sub(a.params[i], binds);
        }
        out = out.union(close(a.result.subst(binds), sig));
      }
    }
    return (out, kept, null);
  }

  /// The arrows of `sig` whose adoptions of the literal arguments are fewest, all the same,
  /// with those adoptions made and the arguments retyped; null when a literal adopts no
  /// arrow's carrier exactly, which is reported. Else the message of the rejection.
  (List<int>?, String?) fewest(String what, Sig sig, List<_Arg?> args) {
    List<(Span, k.Value)>? best;
    var kept = <int>[];
    (Span, String)? adoptError;
    for (final (c, arrow) in sig.arrows.indexed) {
      final need = <(Span, k.Value)>[];
      var ok = true;
      for (final (i, a) in args.indexed) {
        final p = arrow.params[i];
        if (a == null) continue;
        // An arrow no other argument can fit is no candidate.
        final l = a.lit;
        if (l == null) {
          ok &= a.ty.isEmpty || a.ty.meets(p);
          continue;
        }
        if (a.ty.subtype(p) || p.isDynamic) continue;
        final (v, m) = switch (p.numericCarrier) {
          final x? => adopt(l, x),
          null => (null, null),
        };
        if (v != null && litTy(v, l.neg).subtype(p)) {
          need.add((l.span, v));
        } else if (m != null) {
          adoptError ??= (l.span, m);
          ok = false;
        } else {
          // Kept as it is, the literal is checked as any argument is.
          ok &= a.ty.meets(p);
        }
      }
      if (!ok) continue;
      if (best != null && best.length < need.length) continue;
      if (best != null && best.length == need.length) {
        if (listEq(best, need)) kept.add(c);
        continue;
      }
      best = need;
      kept = [c];
    }
    if (best == null) {
      if (adoptError case (final s, final m)) {
        error(s, m);
        return (null, null);
      }
      return (null, rejected(what, args));
    }
    for (final (s, v) in best) {
      final neg = args.nonNulls.any((a) => a.lit?.span == s && a.lit!.neg);
      for (final a in args.nonNulls) {
        if (a.lit?.span == s) a.ty = litTy(v, neg);
      }
      _put(info.adopt, s, v);
    }
    return (kept, null);
  }

  /// Sets `m[key]` to `v`, removing it for null, and logs what undoes it.
  void _put<K, V>(Map<K, V> m, K key, V? v) {
    if (replaying > 0) return;
    final had = m.containsKey(key);
    final old = m[key];
    if (v == null) {
      m.remove(key);
    } else {
      m[key] = v;
    }
    log.add(() {
      if (had) {
        m[key] = old as V;
      } else {
        m.remove(key);
      }
    });
  }

  /// The point the checker is at: how long the log and the errors are.
  ({int log, int errors}) mark() => (log: log.length, errors: info.errors.length);

  /// Undoes every write and error since `m`, the latest first.
  void undo(({int log, int errors}) m) {
    while (log.length > m.log) {
      log.removeLast()();
    }
    info.errors.length = m.errors;
  }
}

final divByZero = const k.Atom('divByZero');

int _bits(int m) {
  var n = 0;
  for (; m != 0; m &= m - 1) {
    n++;
  }
  return n;
}

/// The type of the one-parameter word `sig` applied to `ty`, its atoms passing through; null
/// when a piece of `ty` fits no arrow, an unknown one fitting only an arrow that takes any.
Ty? converted(Sig sig, Ty ty) {
  var out = Ty.of(ty.loose);
  for (final p in ty.withoutLoose.pieces) {
    final arrow = sig.arrows
        .where(
          (a) => switch (p) {
            PDyn() || PVar() => a.params[0].isDynamic,
            _ => p.ty.sub(a.params[0], Binds()),
          },
        )
        .firstOrNull;
    if (arrow == null) return null;
    out = out.union(arrow.result);
  }
  return out;
}

/// `out` with the atoms of `ts` added: when two of them hold atoms, also `#errs`, which two
/// distinct failures merge into.
Ty passed(Ty out, Iterable<Ty> ts) {
  var n = 0;
  for (final t in ts) {
    final a = t.atomSet;
    if (!a.isEmpty) {
      n++;
      out = out.union(Ty.of(a));
    }
  }
  return n > 1 ? out.union(Ty.of(errs)) : out;
}

/// `ty` with the type variables of `sig`'s parameters that no argument bound made unknown.
Ty close(Ty ty, Sig sig) {
  final own = Vars();
  for (final a in sig.arrows) {
    for (final p in a.params) {
      p.varsIn(own);
    }
  }
  return ty.subst({
    for (final v in own.order)
      if (!v.startsWith('\$')) v: Ty.dynamic,
  });
}

/// The one function `ty` is, when it is nothing else.
Sig? onlyFn(Ty ty) =>
    ty.fns.length == 1 && ty.set.isEmpty && ty.tuples.isEmpty && ty.vars.isEmpty && !ty.isDynamic
    ? ty.fns[0]
    : null;

/// `e` as a numeric literal, perhaps under one `-`.
Lit? literal(Expr e) {
  final (inner, neg) = switch (e) {
    Unary(op: '-', :final e) => (e, true),
    _ => (e, false),
  };
  final k.Value? value = switch (inner) {
    IntLit(:final radix, :final digits) => switch (BigInt.tryParse(
      digits.replaceAll('_', ''),
      radix: radix,
    )) {
      final n? => k.Value.integer(n),
      null => null,
    },
    FloatLit(:final text) => switch (double.tryParse(text.replaceAll('_', ''))) {
      final x? => k.Float(x),
      null => null,
    },
    _ => null,
  };
  if (value == null) return null;
  return Lit(inner.span, value, neg, '$inner');
}

k.Value? _run(k.Prim p, k.Value v) {
  try {
    return k.eval(k.PrimApp(p, [k.Lit(v)]));
  } on k.KernelError {
    return null;
  }
}

/// The type of the literal `v`, under `-` when `neg`.
Ty litTy(k.Value v, bool neg) => Ty.lit(neg ? _run(k.Prim.neg, v) ?? v : v);

Carrier litCarrier(k.Value v) => switch (v) {
  k.Float() => Carrier.f64,
  k.Rat() => Carrier.rational,
  _ => Carrier.integer,
};

/// The order two literals adopt in: an integer the other's carrier.
int rank(Carrier c) => c == Carrier.integer ? 0 : 1;

/// The literal `l` as a `c`: (null, null) when it is one already, an error when it is not
/// exactly one.
(k.Value?, String?) adopt(Lit l, Carrier c) {
  if (litCarrier(l.value) == c || !adoptable(l, c)) return (null, null);
  final exact = switch (l.value) {
    k.Float() => k.Rat.decimal(l.text),
    final v => _run(k.Prim.castRat, v),
  };
  final not = (null, '`${l.text}` is not ${_article(c)} ${c.label}');
  if (exact == null) return not;
  final v = switch (c) {
    Carrier.integer => _run(k.Prim.castInt, exact),
    Carrier.rational => exact,
    Carrier.f64 => _run(k.Prim.castF64, exact),
    _ => null,
  };
  return v != null && v is! k.Atom ? (v, null) : not;
}

/// Whether `l` may adopt `c`: an integer literal any numeric carrier, a decimal one `f64` and
/// `rat`, which it denotes exactly, and not `int`.
bool adoptable(Lit l, Carrier c) => c.numeric && !(l.value is k.Float && c == Carrier.integer);

String _article(Carrier c) => c == Carrier.integer || c == Carrier.f64 ? 'an' : 'a';

/// One arrow per carrier in `cs`, of `n` parameters of that carrier, returning `result` or
/// the carrier itself.
List<Arrow> _arrows(List<Carrier> cs, int n, Ty Function(Carrier) result) => [
  for (final c in cs) Arrow(List.filled(n, Ty.carrier(c)), result(c)),
];

List<SParam> _positional(int n) => [for (var i = 0; i < n; i++) SParam('x$i', true)];

/// An operator's arrows.
Sig opSig(String op) {
  Ty same(Carrier c) => Ty.carrier(c);
  Ty bool_(Carrier _) => Ty.carrier(Carrier.boolean);
  Ty div0(Carrier c) => Ty.carrier(c).union(Ty.of(k.Type.atom('divByZero')));
  final (i, f, r, s, b) = (
    Carrier.integer,
    Carrier.f64,
    Carrier.rational,
    Carrier.string,
    Carrier.boolean,
  );
  final (n, arrows) = switch (op) {
    '+' || '-' || '*' => (2, _arrows([i, f, r], 2, same)),
    '/' => (
      2,
      [
        ..._arrows([f], 2, same),
        ..._arrows([r], 2, div0),
      ],
    ),
    'div' || 'mod' => (2, _arrows([i], 2, div0)),
    '**' => (2, _arrows([i, f], 2, same)),
    '++' => (2, _arrows([s], 2, same)),
    '<' => (2, _arrows([i, f, r, s, b], 2, bool_)),
    '&&' => (2, _arrows([b], 2, bool_)),
    '!' => (1, _arrows([b], 1, bool_)),
    _ => (1, _arrows([i, f, r], 1, same)),
  };
  return Sig(_positional(n), arrows);
}

/// A prelude word's arrows.
Sig wordSig(String w) {
  Ty atomsOf(List<String> names) =>
      Ty.unionAll([Ty.empty, for (final n in names) Ty.of(k.Type.atom(n))]);
  Arrow arrow(Carrier from, Carrier to, [List<String> fails = const []]) =>
      Arrow([Ty.carrier(from)], Ty.carrier(to).union(atomsOf(fails)));
  final (i, f, r, s) = (Carrier.integer, Carrier.f64, Carrier.rational, Carrier.string);
  final arrows = switch (w) {
    'String' => [
      Arrow([Ty.dynamic], Ty.carrier(s)),
    ],
    'int' => [
      arrow(i, i),
      arrow(f, i, ['inexact', 'invalid']),
      arrow(r, i, ['inexact']),
      arrow(s, i, ['invalid']),
    ],
    'rat' => [
      arrow(i, r),
      arrow(f, r, ['invalid']),
      arrow(r, r),
      arrow(s, r, ['invalid']),
    ],
    'f64' => [
      arrow(i, f, ['inexact']),
      arrow(f, f),
      arrow(r, f, ['inexact']),
      arrow(s, f, ['inexact', 'invalid']),
    ],
    'abs' => _arrows([i, f, r], 1, Ty.carrier),
    'len' => [arrow(s, i)],
    _ => [arrow(s, s)],
  };
  return Sig(_positional(1), arrows);
}

/// The class a type variable names: `$k` is class `k`.
int? classId(String v) => v.startsWith('\$') ? int.tryParse(v.substring(1)) : null;

/// The `n`th name of a signature's own type variables: `T`, `U`, `V`, `W`, `T5`, ….
String varName(int n) => n < 4 ? const ['T', 'U', 'V', 'W'][n] : 'T${n + 1}';

/// The variables of `s`, in order of first appearance.
List<String> sigVars(Sig s) {
  final out = Vars();
  for (final a in s.arrows) {
    for (final p in a.params) {
      p.varsIn(out);
    }
    a.result.varsIn(out);
  }
  for (final n in s.needs) {
    n.varsIn(out);
  }
  return out.order;
}

/// `t` with each of `needs` joined to the functions in it whose types share a variable with
/// it, as their own; gives it and the needs no function takes, which hold now.
(Ty, List<Need>) hold(Ty t, List<Need> needs) {
  final fns = [...t.fns];
  final vars = [
    for (final s in t.fns)
      () {
        final v = Vars();
        Ty.func(s).varsIn(v);
        return v.order.toSet();
      }(),
  ];
  final own = [for (final _ in fns) <String>[]];
  final held = [for (final _ in fns) <Need>[]];
  final now = <Need>[];
  for (final n in needs) {
    final v = Vars();
    n.varsIn(v);
    final at = [
      for (var i = 0; i < fns.length; i++)
        if (v.order.any(vars[i].contains)) i,
    ];
    if (at.isEmpty) {
      now.add(n);
      continue;
    }
    for (final i in at) {
      own[i].addAll(v.order.where((x) => classId(x) == null && !t.vars.contains(x)));
      held[i].add(n);
    }
  }
  final out = [
    for (final (i, s) in fns.indexed)
      held[i].isEmpty && own[i].isEmpty
          ? s
          : s.copy(
              needs: [...s.needs, ...held[i]],
              own: SplayTreeSet.of([...s.own, ...own[i]]),
            ),
  ];
  return (t.withFns(out), now);
}

/// The values the integer expression `e` may take, from its literals and arithmetic; every
/// int where it reads anything else.
IntervalSet interval(Expr e) {
  final nonnegative = IntervalSet.range(const Fin(0), posInf);
  Op? op(String o) => switch (o) {
    '+' => Op.add,
    '-' => Op.sub,
    '*' => Op.mul,
    'div' => Op.div,
    'mod' => Op.mod,
    _ => null,
  };
  switch (e) {
    case IntLit(:final radix, :final digits):
      final v = int.tryParse(digits.replaceAll('_', ''), radix: radix);
      return v == null ? IntervalSet.top() : IntervalSet.single(v);
    case Unary(op: '-', e: final a):
      return interval(a).neg();
    case Binary(op: '**', :final a, :final b):
      final (x, n) = (interval(a), interval(b));
      if (n.bounds case (Fin(v: final lo), Fin(v: final hi))
          when lo == hi && lo >= 0 && lo <= 0xffffffff) {
        return forward(Op.pow(lo), x, x);
      }
      return x.isSubset(nonnegative) && n.isSubset(nonnegative) ? nonnegative : IntervalSet.top();
    case Binary(op: final o, :final a, :final b):
      final f = op(o);
      return f == null ? IntervalSet.top() : forward(f, interval(a), interval(b));
    default:
      return IntervalSet.top();
  }
}

/// The type of a port: a `Lines` port maps a line number to its line, a `Files` port a path
/// to its file's text; each may fail with `#ioError` or `#notFound`.
Ty port(bool lines) => Ty.func(
  Sig(
    [SParam('_0', true)],
    [
      Arrow(
        [Ty.carrier(lines ? Carrier.integer : Carrier.string)],
        Ty.carrier(Carrier.string)
            .union(Ty.of(k.Type.atom('ioError')))
            .union(Ty.of(k.Type.atom('notFound'))),
      ),
    ],
    data: lines,
  ),
);

/// `t` with the variables `binds` binds replaced, and each other one that is no class
/// unknown.
Ty bound(Ty t, Binds binds) {
  final vars = Vars();
  t.varsIn(vars);
  final b = Binds.of(binds);
  for (final v in vars.order) {
    if (classId(v) == null) b.putIfAbsent(v, () => Ty.dynamic);
  }
  return t.replace(b);
}

/// The carriers a value of `ty` may be of, and [other] if it may be a tuple, a function or
/// another value that is no atom: every value if `ty` is unknown or has a variable.
int maskOf(Ty ty) {
  if (ty.isDynamic || ty.vars.isNotEmpty) return every;
  var m = 0;
  for (final c in Carrier.values) {
    if (!(ty.set & c.ty).isEmpty) m |= c.bit;
  }
  final carriers = Carrier.values.fold(atoms, (s, c) => s | c.ty);
  if (ty.tuples.isNotEmpty || ty.fns.isNotEmpty || !(ty.set - carriers).isEmpty) m |= other;
  return m;
}
