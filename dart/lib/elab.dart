/// Elaboration (step L1.16): a resolved L1 unit to kernel terms, by the rules of DESIGN.md
/// "Kernel desugaring".
///
/// A unit is its definitions, not a term: each top-level binding and function is a [Def], in
/// dependency order, and [Unit.close] wraps a term in them as nested lets so it can be
/// evaluated. A block is the lets of its statements in dependency order over its export; a
/// cycle among them is recursion, which arrives at L6. Every binder gets a kernel name unique
/// in the unit: its own name when no other binder shares it and it is not a prelude word, else
/// `name@k` for the `k`-th binder of that name. Temporaries are `$1`, `$2`, …. Because the
/// names are unique, a default is filled by let-binding the call's arguments under the
/// parameters' own names, with no capture.
///
/// Where DESIGN.md does not say: `++` is its own primitive `Concat`, never `Add`; `e else d`
/// matches any atom (`#_`), which is exact while every atom is loose (before L2's named atom
/// families); a call through a value other than a declared function passes its arguments by
/// position only, until types give a function value its parameter kinds (L1.26); a prelude
/// word is the free variable of its name, bound by the interpreter (L1.18); a `test` table
/// belongs to a function at the unit's top level.
library;

import 'dart:collection';

import 'ast.dart';
import 'kernel.dart' as k;
import 'resolve.dart';
import 'source.dart';

/// A top-level definition.
final class Def {
  /// Its source name, or the temporary's name for the tuple of `a, b = e;`.
  final String name;

  /// Its kernel name.
  final String kernel;
  final k.Term term;

  Def(this.name, this.kernel, this.term);
}

/// A case of a `test` table: `f(input) == expected`.
final class Test {
  /// The function's source name.
  final String function;

  /// The bool term that checks the case, over the unit's definitions.
  final k.Term check;

  /// The arguments the key gives, in declaration order.
  final List<k.Term> args;

  /// The expected value.
  final k.Term want;

  /// The case's text.
  final Span span;

  Test(this.function, this.check, this.args, this.want, this.span);
}

/// An elaborated unit.
final class Unit {
  /// The definitions, each after those it uses.
  final List<Def> defs;

  /// The test cases, in written order.
  final List<Test> tests;

  Unit(this.defs, this.tests);

  /// `body` under the definitions it reaches, each a let, in the unit's order. For many terms
  /// of one unit, make its [Cones] once.
  k.Term close(k.Term body) => Cones(this).close(body);

  /// The definition of source name `name`, closed over the others.
  k.Term? get(String name) {
    for (final d in defs) {
      if (d.name == name) return close(k.Var(d.kernel));
    }
    return null;
  }
}

/// The definitions each term of a unit reaches, from an index of the unit made once: each
/// kernel name's definition, and the names each definition reads, found when first needed. A
/// term's cone then costs the definitions in it, not a pass over the unit.
final class Cones {
  final Unit _unit;
  final Map<String, int> _byKernel;
  final List<Set<String>?> _free;

  /// The index of `unit`.
  Cones(this._unit)
    : _byKernel = {for (final (i, d) in _unit.defs.indexed) d.kernel: i},
      _free = List.filled(_unit.defs.length, null);

  /// The definitions `roots` read, and those they read in turn: their positions in the unit,
  /// in its order.
  List<int> reach(List<k.Term> roots) {
    final seen = SplayTreeSet<int>();
    final todo = [for (final t in roots) ...free(t)];
    while (todo.isNotEmpty) {
      if (_byKernel[todo.removeLast()] case final i? when seen.add(i)) {
        todo.addAll(_free[i] ??= free(_unit.defs[i].term));
      }
    }
    return seen.toList();
  }

  /// `body` under the definitions it reaches, each a let, in the unit's order: each after
  /// those it uses, as in the unit.
  k.Term close(k.Term body) {
    for (final i in reach([body]).reversed) {
      final d = _unit.defs[i];
      body = k.Let(d.kernel, d.term, body);
    }
    return body;
  }
}

/// The names `t` reads and does not bind. The walk keeps its own stack, since a term may nest
/// deeper than the call stack.
Set<String> free(k.Term t) {
  final out = SplayTreeSet<String>();
  // How many binders around the current subterm bind each name.
  final bound = <String, int>{};
  // Terms to walk, and the names to bind (true) or release (false) between them.
  final stack = <Object>[t];
  // Walks `ts` with `names` bound.
  void under(List<String> names, List<k.Term> ts) {
    stack
      ..add((false, names))
      ..addAll(ts)
      ..add((true, names));
  }

  while (stack.isNotEmpty) {
    switch (stack.removeLast()) {
      case (true, final List<String> names):
        for (final x in names) {
          bound[x] = (bound[x] ?? 0) + 1;
        }
      case (false, final List<String> names):
        for (final x in names) {
          if (bound[x] == 1) {
            bound.remove(x);
          } else {
            bound[x] = bound[x]! - 1;
          }
        }
      case k.Lit() || k.PrimFn() || k.Read():
        break;
      case k.Var(:final name):
        if (!bound.containsKey(name)) out.add(name);
      case k.Lam(:final params, :final body):
        under(params, [body]);
      case k.Let(:final name, :final value, :final body):
        under([name], [body]);
        stack.add(value);
      case k.Match(:final scrutinee, :final arms):
        for (final (p, a) in arms) {
          under(_binds(p).toList(), [a]);
        }
        stack.add(scrutinee);
      case k.Fam(:final domain, :final variable, :final body):
        under([variable], [body]);
        stack.add(domain);
      case k.Fix(:final init, :final step, :final self, :final key, :final kind):
        under([self, key], [step, if (kind case k.Lattice(:final join)) join]);
        stack.add(init);
      case k.App(:final f, :final args):
        stack
          ..add(f)
          ..addAll(args);
      case k.PrimApp(:final args):
        stack.addAll(args);
      case k.If(:final cond, :final then, :final orElse):
        stack.addAll([cond, then, orElse]);
      case k.Reindex(:final family, :final kf, :final vf):
        stack.addAll([family, kf, vf]);
      case k.Discard(:final family, :final sel):
        stack.addAll([family, sel]);
      case k.Fold(:final family, :final op, :final identity):
        stack.addAll([family, op, ?identity]);
      case k.Gen(:final init, :final step, :final guard):
        stack.addAll([init, step, guard]);
      case k.Push(:final value):
        stack.add(value);
    }
  }
  return out;
}

/// The names a pattern binds.
Iterable<String> _binds(k.Pattern p) => switch (p) {
  k.BindP(:final name) => [name],
  k.AtomP(args: final ps) || k.TupleP(items: final ps) => ps.expand(_binds),
  k.FieldsP(:final fields) => fields.expand((f) => _binds(f.$2)),
  _ => const [],
};

/// The errors of a unit that does not elaborate, in text order.
final class ElabErrors implements Exception {
  final List<BuildError> errors;

  ElabErrors(this.errors);

  @override
  String toString() => errors.join('\n');
}

/// The elaboration of `unit` under its resolution; throws [ElabErrors] with every error in it.
Unit elaborate(List<Stmt> unit, Resolution res) {
  final e = _Elab(res)..run(unit);
  if (e.errors.isEmpty) return Unit(e.result<(List<Def>, k.Term?)>().$1, e.tests);
  // The sort keeps errors of one span in the order they were met.
  final order = [for (var i = 0; i < e.errors.length; i++) i]
    ..sort((a, b) {
      final (x, y) = (e.errors[a].span, e.errors[b].span);
      if (x.start != y.start) return x.start - y.start;
      if (x.end != y.end) return x.end - y.end;
      return a - b;
    });
  throw ElabErrors([for (final i in order) e.errors[i]]);
}

/// Thrown where an error has been recorded and the term it would have built is missing; left
/// in [_Elab._got] as the result of the step it stopped.
final class _Stop {
  const _Stop();
}

/// Each part of the unit is elaborated by a generator that yields the generators of the parts
/// it needs and reads each one's result from [_Elab._got], then leaves its own there. They run
/// on an explicit stack, so the depth of the unit's nesting is bounded by memory alone.
typedef _Steps = Iterable<Iterable<Object?>>;

final class _Elab {
  final Resolution res;

  /// Each binder, by its span and name.
  final ids = <(Span, String), Binder>{};

  /// Each binder's kernel name.
  final names = <Binder, String>{};

  /// The spans of each binder's uses, in text order.
  final usesOf = <Binder, List<Span>>{};

  /// Each function binder's declaration, recorded when its scope is entered, before any use
  /// of it is elaborated.
  final funcs = <Binder, FunctionDef>{};

  /// The term of each default, or the [_Stop] it ended in, made at the first call that leaves
  /// its parameter out: it does not depend on the call, so the others share it, and a chain
  /// of defaults that each call a function with a default is elaborated once per default.
  final defaultOf = <Param, Object?>{};
  var fresh = 0;
  final tests = <Test>[];
  final errors = <BuildError>[];

  /// What the last step to finish built, or a [_Stop] when it stopped on an error.
  Object? _got;

  _Elab(this.res) {
    final count = <String, int>{}, seen = <String, int>{};
    for (final b in res.binders) {
      count.update(b.name, (c) => c + 1, ifAbsent: () => 1);
    }
    for (final b in res.binders) {
      final i = seen.update(b.name, (c) => c + 1, ifAbsent: () => 1);
      names[b] = count[b.name] == 1 && preludeLayer(b.name) == null ? b.name : '${b.name}@$i';
      ids[(b.span, b.name)] = b;
    }
    for (final MapEntry(key: span, :value) in res.uses.entries) {
      if (value case Bound(:final binders)) {
        for (final b in binders) {
          (usesOf[b] ??= []).add(span);
        }
      }
    }
  }

  /// Elaborates the unit's top level, leaving its scope in [_got].
  void run(List<Stmt> unit) {
    final stack = [scope(unit, true).iterator];
    while (stack.isNotEmpty) {
      try {
        if (stack.last.moveNext()) {
          stack.add((stack.last.current as _Steps).iterator);
        } else {
          stack.removeLast();
        }
      } on _Stop catch (s) {
        stack.removeLast();
        _got = s;
      }
    }
  }

  /// Whether the last step stopped on an error.
  bool get failed => _got is _Stop;

  /// What the last step built; stops the step reading it if that step stopped.
  T result<T>() => _got is _Stop ? throw const _Stop() : _got as T;

  /// The term the last step built, or null if it stopped.
  k.Term? get termOrNull => _got is _Stop ? null : _got as k.Term;

  k.Term get term => result<k.Term>();

  /// Records an error.
  void note(Span span, String message) => errors.add(BuildError(span, message));

  /// Records an error and stops the step.
  Never error(Span span, String message) {
    note(span, message);
    throw const _Stop();
  }

  /// The terms of `es`, each elaborated even when one before it stopped.
  _Steps each(Iterable<Expr> es) sync* {
    final ts = <k.Term?>[];
    for (final e in es) {
      yield expr(e);
      ts.add(termOrNull);
    }
    _got = [for (final t in ts) t ?? (throw const _Stop())];
  }

  /// The type `t` denotes, or null after recording its errors; every part is elaborated even
  /// when one before it fails.
  k.Type? ty(TypeExpr t) {
    List<k.Type>? all(List<TypeExpr> ts) {
      final out = [for (final t in ts) ty(t)];
      return out.contains(null) ? null : [for (final t in out) t!];
    }

    switch (t) {
      case TypeName(:final name):
        final base = switch (name) {
          'int' => k.Type.integer,
          'rat' => k.Type.rational,
          'f64' => k.Type.f64,
          'bool' => k.Type.boolean,
          'String' => k.Type.string,
          _ => null,
        };
        if (base == null) note(t.span, '`$name` is the type of a port, and no value has it');
        return base;
      case AtomType(:final name):
        return k.Type.atom(name);
      case TupleType(:final items):
        return switch (all(items)) {
          final ts? => k.Type.tuple(ts),
          null => null,
        };
      case UnionType(:final items):
        return switch (all(items)) {
          final ts? => k.Type.unionAll(ts),
          null => null,
        };
      case AndType(:final items):
        return switch (all(items)) {
          final ts? => k.Type.meetAll(ts),
          null => null,
        };
      case DiffType(:final a, :final b):
        final (x, y) = (ty(a), ty(b));
        return x == null || y == null ? null : x - y;
      case ArrowType(:final params, :final partial, :final result):
        final keys = all([for (final p in params) p.type]);
        final value = ty(result);
        if (keys == null || value == null) return null;
        final level = partial ? k.Type.partial : k.Type.exact;
        return (keys.isEmpty ? [k.Type.tuple([])] : keys).reversed.fold<k.Type>(
          value,
          (v, key) => level(key, v),
        );
    }
  }

  String temp() => '\$${++fresh}';

  String kname(Span span, String name) => names[ids[(span, name)]!]!;

  /// The statements of one scope: its bindings in dependency order, and its export. `top` is
  /// the unit's top level, where a function's `test` table is elaborated.
  _Steps scope(List<Stmt> stmts, bool top) sync* {
    List<Expr>? export;
    final items = <Stmt>[];
    for (final s in stmts) {
      if (s is Return) {
        export = s.values;
      } else {
        items.add(s);
      }
    }
    // The binders each statement makes; a function's uses are elaborated from here on.
    final owner = <Binder, int>{};
    for (final (i, s) in items.indexed) {
      for (final b in bindersOf(s)) {
        owner[b] = i;
        if (s is FunctionDef) funcs[b] = s;
      }
    }
    // The statements each one uses: each use of a binder of this scope falls in one statement
    // or the export, found by its start among the statements' (in text order), except the
    // uses in a function's `test` table.
    final deps = [for (final _ in items) SplayTreeSet<int>()];
    for (final MapEntry(key: b, value: j) in owner.entries) {
      for (final u in usesOf[b] ?? const <Span>[]) {
        final i = _last(items.length, (i) => items[i].span.start <= u.start);
        if (i < 0 || u.end > items[i].span.end) continue;
        if (items[i] case FunctionDef(:final tests) when _inTests(tests, u)) continue;
        deps[i].add(j);
      }
    }
    final (order, cycle) = _topo([for (final d in deps) d.toList()]);
    if (cycle != null) {
      final named = [for (final i in cycle) _what(items[i])];
      final message = named.length == 1
          ? '${named[0]} is defined in terms of itself'
          : '${named.join(', ')} are defined in terms of each other';
      error(items[cycle[0]].span, '$message: recursion arrives at layer L6');
    }
    final binds = <Def>[];
    var ok = true;
    for (final i in order) {
      yield stmt(items[i], top, binds);
      ok &= !failed;
    }
    k.Term? out;
    if (export != null) {
      yield each(export);
      final ts = result<List<k.Term>>();
      out = ts.length == 1 ? ts[0] : k.PrimApp(k.Prim.tuple, ts);
    }
    if (!ok) throw const _Stop();
    _got = (binds, out);
  }

  /// A block's term: the lets of its statements over its export, or `()` without one.
  _Steps block(List<Stmt> stmts) sync* {
    yield scope(stmts, false);
    final (binds, export) = result<(List<Def>, k.Term?)>();
    var body = export ?? const k.PrimApp(k.Prim.tuple, []);
    for (final d in binds.reversed) {
      body = k.Let(d.kernel, d.term, body);
    }
    _got = body;
  }

  List<Binder> bindersOf(Stmt s) => switch (s) {
    Bind(:final targets) => [
      for (final t in targets)
        if (t != null) ids[(s.span, t)]!,
    ],
    FunctionDef(:final name) => [ids[(s.span, name)]!],
    Push() || Return() => [],
  };

  /// Adds the bindings of `s` to `out`.
  _Steps stmt(Stmt s, bool top, List<Def> out) sync* {
    switch (s) {
      case Bind(:final targets, :final value):
        yield expr(value);
        final v = term;
        switch (targets) {
          case [final String n]:
            out.add(Def(n, kname(s.span, n), v));
          case [null]:
            final t = temp();
            out.add(Def(t, t, v));
          default:
            final t = temp();
            out.add(Def(t, t, v));
            for (final (i, n) in targets.indexed) {
              if (n == null) continue;
              final get = k.PrimApp(k.Prim.tupleGet, [k.Var(t), k.Lit(k.Int(i))]);
              out.add(Def(n, kname(s.span, n), get));
            }
        }
      case FunctionDef(:final name, :final params, :final body, :final equation):
        final ps = [for (final p in params) kname(p.span, p.name)];
        yield body is Block && !equation ? block(body.stmts) : expr(body);
        final b = termOrNull;
        yield testsOf(s, top);
        if (b == null || failed) throw const _Stop();
        out.add(Def(name, kname(s.span, name), k.Lam(ps, b)));
      case Push(:final port, :final value):
        yield expr(value);
        final v = term;
        final t = temp();
        out.add(Def(t, t, k.Push(port, v)));
      case Return():
        throw StateError('an export is not a binding');
    }
    _got = out;
  }

  /// The cases of `f`'s `test` tables: a key is the argument, or for a function of several
  /// parameters the tuple of its arguments in declaration order.
  _Steps testsOf(FunctionDef f, bool top) sync* {
    if (f.tests.isNotEmpty && !top) {
      error(
        f.span,
        "`${f.name}` has a test table, which belongs to a function at the unit's top level",
      );
    }
    var ok = true;
    final n = f.params.length;
    for (final (input, expected) in f.tests) {
      final args = switch (input) {
        _ when n == 1 => [input],
        Tuple(:final items) when items.length == n => items,
        _ => null,
      };
      if (args == null) {
        ok = false;
        note(input.span, 'a test key of `${f.name}` is the tuple of its $n arguments');
        continue;
      }
      // The arguments stop at the first that stops; the expected value is elaborated anyway.
      final as = <k.Term>[];
      for (final a in args) {
        yield expr(a);
        if (failed) break;
        as.add(term);
      }
      final argsOk = as.length == args.length;
      yield expr(expected);
      final want = termOrNull;
      if (!argsOk || want == null) {
        ok = false;
        continue;
      }
      final call = k.App(k.Var(kname(f.span, f.name)), as);
      tests.add(
        Test(f.name, k.PrimApp(k.Prim.eq, [call, want]), as, want, (
          start: input.span.start,
          end: expected.span.end,
        )),
      );
    }
    if (!ok) throw const _Stop();
    _got = true;
  }

  _Steps expr(Expr e) sync* {
    switch (e) {
      case IntLit(:final radix, :final digits):
        _got = k.Lit(k.Value.integer(BigInt.parse(digits.replaceAll('_', ''), radix: radix)));
      case FloatLit(:final text):
        _got = k.Lit(k.Float(double.parse(text.replaceAll('_', ''))));
      case RatLit(:final text):
        _got = k.Lit(
          k.Rat.decimal(text) ??
              error(e.span, "this rational is beyond the evaluator's size limit"),
        );
      case BoolLit(:final value):
        _got = k.Lit(k.Bool(value));
      case AtomLit(:final name):
        _got = k.Lit(k.Atom(name));
      case StrLit(:final parts):
        yield* string(parts);
      case NameRef(:final name):
        _got = this.name(name, e.span);
      case Unary(:final op, e: final a):
        yield expr(a);
        _got = k.PrimApp(op == '-' ? k.Prim.neg : k.Prim.not, [term]);
      case Binary(:final op, :final a, :final b):
        yield each([a, b]);
        final [x, y] = result<List<k.Term>>();
        _got = switch (op) {
          '||' => k.If(x, const k.Lit(k.Bool(true)), y),
          '&&' => k.If(x, y, const k.Lit(k.Bool(false))),
          _ => k.PrimApp(_binary[op] ?? error(e.span, '`$op` is not an L1 operator'), [x, y]),
        };
      case Call(:final callee, :final positional, :final named, :final curry):
        yield* call(callee, positional, named, curry, e.span);
      case Index(e: final of, :final key):
        yield* index(of, key);
      case Tuple(:final items):
        yield each(items);
        _got = k.PrimApp(k.Prim.tuple, result<List<k.Term>>());
      case Lambda(:final params, :final body):
        yield* lambda(params, body);
      case Is(:final of, :final type, :final negated):
        yield expr(of);
        final (v, t) = (termOrNull, ty(type));
        if (v == null || t == null) throw const _Stop();
        if (!t.decidable) {
          error(type.span, '`is` cannot test a value against a function type at run time');
        }
        _got = k.Match(v, [
          (k.IsP(t), k.Lit(k.Bool(!negated))),
          (const k.WildP(), k.Lit(k.Bool(negated))),
        ]);
      case Else(:final of, :final pattern, :final fallback):
        yield expr(of);
        final v = termOrNull;
        yield expr(fallback);
        final d = termOrNull;
        k.Pattern? pat = const k.AnyAtomP();
        if (pattern != null) {
          yield this.pattern(pattern);
          pat = failed ? null : _got as k.Pattern;
        }
        if (v == null || d == null || pat == null) throw const _Stop();
        final t = temp();
        _got = k.Match(v, [(pat, d), (k.BindP(t), k.Var(t))]);
      case Block(:final stmts):
        yield* block(stmts);
      case If(:final cond, :final then, :final otherwise):
        yield each([cond, then, otherwise]);
        final [c, a, b] = result<List<k.Term>>();
        _got = k.If(c, a, b);
      case Member(:final of, :final name, :final safe):
        yield* member(of, name, safe, e.span, const [], const [], false, e.span);
    }
  }

  /// Interpolation: the nonempty parts joined by `++`, each hole `String(hole)`.
  _Steps string(List<StrPart> parts) sync* {
    k.Term? out;
    for (final p in parts) {
      final k.Term t;
      switch (p) {
        case StrText(:final text) when text.isEmpty:
          continue;
        case StrText(:final text):
          t = k.Lit(k.Str(text));
        case StrHole(:final e):
          yield expr(e);
          t = k.App(const k.Var('String'), [term]);
      }
      out = out == null ? t : k.PrimApp(k.Prim.concat, [out, t]);
    }
    _got = out ?? k.Lit(k.Str(''));
  }

  k.Term name(String n, Span span) => switch (res.uses[span]) {
    Bound(:final binders) when binders.length > 1 => error(
      span,
      '`$n` names ${binders.length} overloads; choosing among them arrives at L2',
    ),
    Bound(:final binders) when binders[0].kind == Kind.port => error(
      span,
      '`$n` is an output port, written with `$n <- e`, not a value',
    ),
    Bound(:final binders) => k.Var(names[binders[0]]!),
    Prelude(:final word) => k.Var(word),
    null => throw StateError('a resolved unit records every name'),
  };

  /// The declared function that `e` names, if it names exactly one.
  Binder? declared(Expr e) => switch ((e, res.uses[e.span])) {
    (NameRef(), Bound(binders: [final b])) when funcs.containsKey(b) => b,
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
      yield* member(of, name, safe, callee.span, positional, named, curry, span);
    } else if (callee case AtomLit(:final name)) {
      yield* atom(name, positional, named, curry, span);
    } else if (declared(callee) case final b?) {
      yield* callDeclared(b, null, positional, named, curry, span);
    } else {
      yield expr(callee);
      yield* callValue(term, null, positional, named, curry, span);
    }
  }

  /// An atom with a payload, `#name(a, b)` by position or `#name(f: a)` by name.
  _Steps atom(
    String name,
    List<Expr> positional,
    List<(String, Expr)> named,
    bool curry,
    Span span,
  ) sync* {
    if (curry) error(span, "`...` curries a function's named parameters; an atom has none");
    if (positional.isNotEmpty && named.isNotEmpty) {
      error(span, "an atom's payload is all by position or all by name");
    }
    final fields = k.Tuple([for (final (f, _) in named) k.Str(f)]);
    yield each([...positional, for (final (_, a) in named) a]);
    _got = k.PrimApp(k.Prim.atom, [k.Lit(k.Str(name)), k.Lit(fields), ...result<List<k.Term>>()]);
  }

  /// A call through a value other than a declared function: by position only.
  _Steps callValue(
    k.Term f,
    k.Term? receiver,
    List<Expr> positional,
    List<(String, Expr)> named,
    bool curry,
    Span span,
  ) sync* {
    if (named.isNotEmpty || curry) {
      error(
        span,
        'named arguments and `...` need the declaration of the function called; '
        'through a value they arrive with types at step L1.26',
      );
    }
    yield each(positional);
    _got = k.App(f, [?receiver, ...result<List<k.Term>>()]);
  }

  /// A saturated or curried call of the declared function `b`; `receiver` fills its first
  /// parameter, of either kind.
  _Steps callDeclared(
    Binder b,
    k.Term? receiver,
    List<Expr> positional,
    List<(String, Expr)> named,
    bool curry,
    Span span,
  ) sync* {
    final f = funcs[b]!;
    final fname = f.name, params = f.params, n = params.length;
    final slots = List<k.Term?>.filled(n, null);
    var next = 0;
    if (receiver != null) {
      if (n == 0) error(span, '`$fname` has no parameter for a receiver');
      slots[0] = receiver;
      next = 1;
    }
    var ok = true;
    for (final a in positional) {
      if (next == n) error(a.span, 'too many arguments: `$fname` takes $n');
      final p = params[next];
      if (!p.positional) {
        error(a.span, '`${p.name}` of `$fname` is named: pass it as `${p.name}: …`');
      }
      yield expr(a);
      slots[next] = termOrNull;
      ok &= slots[next++] != null;
    }
    for (final (name, a) in named) {
      final j = params.indexWhere((p) => p.name == name);
      if (j < 0) error(a.span, '`$fname` has no parameter `$name`');
      if (params[j].positional) {
        error(a.span, '`$name` of `$fname` is positional: pass it by position');
      }
      if (slots[j] != null) error(a.span, '`$name` is already supplied');
      yield expr(a);
      slots[j] = termOrNull;
      ok &= slots[j] != null;
    }
    if (!ok) throw const _Stop();
    String pname(Param p) => kname(p.span, p.name);
    final fv = k.Var(names[b]!);
    final missing = [
      for (var j = 0; j < n; j++)
        if (slots[j] == null) j,
    ];
    final all = k.App(fv, [for (final p in params) k.Var(pname(p))]);
    // `body` under the lets of the supplied arguments, in parameter order.
    k.Term supplied(k.Term body) {
      for (var j = n - 1; j >= 0; j--) {
        if (slots[j] case final t?) body = k.Let(pname(params[j]), t, body);
      }
      return body;
    }

    if (curry) {
      for (final j in missing) {
        if (params[j].positional) {
          error(
            span,
            '`...` curries named parameters only; the positional `${params[j].name}` is left out',
          );
        }
      }
      if (missing.isEmpty) error(span, '`...` leaves no named parameter out');
      _got = k.Lam([for (final j in missing) pname(params[j])], supplied(all));
      return;
    }
    if (missing.isEmpty) {
      _got = k.App(fv, [for (final s in slots) s!]);
      return;
    }
    var filled = true;
    for (final j in missing) {
      if (params[j].fallback == null) {
        filled = false;
        note(span, 'missing argument `${params[j].name}` of `$fname`');
      }
    }
    if (!filled) throw const _Stop();
    // The defaults, each after the defaulted parameters it reads.
    final at = {for (final (i, j) in missing.indexed) ids[(params[j].span, params[j].name)]!: i};
    final deps = [
      for (final j in missing)
        (SplayTreeSet<int>()..addAll([for (final u in usesIn(params[j].fallback!.span)) ?at[u]]))
            .toList(),
    ];
    final (order, cycle) = _topo(deps);
    if (cycle != null) {
      final named = [for (final i in cycle) '`${params[missing[i]].name}`'];
      error(span, 'the defaults of ${named.join(', ')} read each other');
    }
    k.Term body = all;
    final defaults = <(String, k.Term)>[];
    for (final i in order) {
      final p = params[missing[i]];
      if (defaultOf[p] case final d?) {
        _got = d;
      } else {
        yield expr(p.fallback!);
        defaultOf[p] = _got;
      }
      defaults.add((pname(p), term));
    }
    for (final (name, d) in defaults.reversed) {
      body = k.Let(name, d, body);
    }
    _got = supplied(body);
  }

  /// The binders used in `span`, in text order.
  Iterable<Binder> usesIn(Span span) sync* {
    final uses = res.uses;
    for (
      var u = uses.firstKeyAfter((start: span.start, end: -1));
      u != null && u.start < span.end;
      u = uses.firstKeyAfter(u)
    ) {
      if (u.end > span.end) continue;
      if (uses[u] case Bound(:final binders)) yield* binders;
    }
  }

  /// `x.f(args)` and `x?.f(args)`: the uniform call `f(x, args)`, `?.` passing an atom `x`
  /// through. Without parentheses the arguments are empty.
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
    yield expr(of);
    final x = term;
    final t = safe ? temp() : null;
    final receiver = t == null ? x : k.Var(t);
    yield switch (res.uses[member]) {
      Bound(:final binders) when binders.length > 1 => error(
        member,
        '`$name` names ${binders.length} overloads; choosing among them arrives at L2',
      ),
      Bound(binders: [final b]) when funcs.containsKey(b) => callDeclared(
        b,
        receiver,
        positional,
        named,
        curry,
        span,
      ),
      Bound(binders: [final b]) => callValue(
        k.Var(names[b]!),
        receiver,
        positional,
        named,
        curry,
        span,
      ),
      _ => switch (preludeLayer(name)) {
        1 => callValue(k.Var(name), receiver, positional, named, curry, span),
        final int layer => error(member, '`$name` is a prelude word of layer L$layer'),
        null => error(member, '`$name` is not a function in scope, and fields arrive at L2'),
      },
    };
    final call = term;
    _got = t == null
        ? call
        : k.Let(t, x, k.Match(k.Var(t), [(const k.AnyAtomP(), k.Var(t)), (const k.WildP(), call)]));
  }

  /// `f[k]` on a declared function: the section filling its first parameter, no default
  /// filled; `t[i]` with a literal `i`: the tuple component; else an application.
  _Steps index(Expr of, Expr key) sync* {
    if (declared(of) case final b?) {
      final f = funcs[b]!;
      yield expr(key);
      final kt = term;
      final fv = k.Var(names[b]!);
      switch (f.params.length) {
        case 0:
          error(of.span, '`${f.name}` takes no arguments');
        case 1:
          _got = k.App(fv, [kt]);
        case final n:
          final rest = [for (var i = 1; i < n; i++) temp()];
          _got = k.Lam(rest, k.App(fv, [kt, for (final r in rest) k.Var(r)]));
      }
      return;
    }
    yield each([of, key]);
    final [v, i] = result<List<k.Term>>();
    _got = key is IntLit ? k.PrimApp(k.Prim.tupleGet, [v, i]) : k.App(v, [i]);
  }

  _Steps lambda(List<Param> params, Expr body) sync* {
    for (final p in params) {
      if (p.fallback case final d?) {
        error(d.span, "a lambda's default arrives with its expected type at step L1.26");
      }
    }
    final ps = [for (final p in params) kname(p.span, p.name)];
    yield body is Block ? block(body.stmts) : expr(body);
    _got = k.Lam(ps, term);
  }

  /// An `else` pattern: an atom, its payload matched by position or by name; a field written
  /// `f:` binds `f`.
  _Steps pattern(Pattern p) sync* {
    final AtomPattern(:name, :fields, :items, :span) = p as AtomPattern;
    if (fields.isNotEmpty) {
      if (items.isNotEmpty) error(span, "an atom's payload is all by position or all by name");
      final seen = <String>{};
      for (final (f, _) in fields) {
        if (!seen.add(f)) error(span, 'the pattern names `$f` twice');
      }
      final out = <(String, k.Pattern)>[];
      for (final (f, sub) in fields) {
        if (sub == null) {
          out.add((f, k.BindP(kname(span, f))));
        } else {
          yield pattern(sub);
          out.add((f, result<k.Pattern>()));
        }
      }
      _got = k.FieldsP(name, out);
      return;
    }
    final args = <k.Pattern>[];
    for (final i in items) {
      yield pattern(i);
      args.add(result<k.Pattern>());
    }
    _got = k.AtomP(name, args);
  }
}

/// The primitive of each binary operator but `||` and `&&`.
const _binary = {
  '==': k.Prim.eq,
  '!=': k.Prim.ne,
  '<': k.Prim.lt,
  '<=': k.Prim.le,
  '>': k.Prim.gt,
  '>=': k.Prim.ge,
  '+': k.Prim.add,
  '-': k.Prim.sub,
  '*': k.Prim.mul,
  '/': k.Prim.div,
  'div': k.Prim.intDiv,
  'mod': k.Prim.mod,
  '**': k.Prim.pow,
  '++': k.Prim.concat,
};

/// Whether `u` lies in one of the `test` cases, which are in text order.
bool _inTests(List<(Expr, Expr)> tests, Span u) {
  final i = _last(tests.length, (i) => tests[i].$1.span.start <= u.start);
  return i >= 0 && u.end <= tests[i].$2.span.end;
}

/// The last `i` below `n` for which `ok(i)` holds, `ok` holding on a prefix; -1 for none.
int _last(int n, bool Function(int) ok) {
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

/// How a statement is named in a cycle's error.
String _what(Stmt s) => switch (s) {
  Bind(:final targets) => [
    for (final t in targets)
      if (t != null) '`$t`',
  ].join(' and '),
  FunctionDef(:final name) => '`$name`',
  Push(:final port) => 'the push to `$port`',
  Return() => 'the export',
};

/// An order of `0..deps.length` with each item after its dependencies (each list ascending),
/// the least ready item first; else the items of one cycle, in order along it.
(List<int>, List<int>?) _topo(List<List<int>> deps) {
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
