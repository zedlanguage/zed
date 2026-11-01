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
/// families); a call through a value other than a declared function takes named arguments,
/// closed defaults and `...` from the signature the checker gives the value (L1.26); a prelude
/// word is the free variable of its name, bound by the interpreter (L1.18); a `test` table
/// belongs to a function at the unit's top level.
library;

import 'dart:collection';

import 'ast.dart';
import 'check.dart' show Fit, FitAdapter, FitLambda, Info, checkWith;
import 'kernel.dart' as k;
import 'resolve.dart';
import 'source.dart';
import 'src/tables.dart';

/// A top-level definition.
final class Def {
  /// Its source name, or the temporary's name for the tuple of `a, b = e;`.
  final String name;

  /// Its kernel name.
  final String kernel;
  final k.Term term;

  /// Whether it is bound by `=` to a value whose type, as the checker gives it, has no
  /// function component (step L1.37).
  final bool firstOrder;

  Def(this.name, this.kernel, this.term, [this.firstOrder = false]);
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

  /// The definitions `roots` reach, in the unit's order.
  Iterable<Def> defs(List<k.Term> roots) => [for (final i in reach(roots)) _unit.defs[i]];

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
  final t = Tables(unit, res);
  return elaborateWith(t, checkWith(t, unit), unit);
}

/// The elaboration of `unit` under its tables and what checking it found, which it only reads.
Unit elaborateWith(Tables t, Info info, List<Stmt> unit) {
  final e = _Elab(t, info)..run(unit);
  final errors = [...e.errors, ...info.errors];
  if (errors.isEmpty) {
    final (defs, _) = e.result<(List<Def>, k.Term?)>();
    return Unit([
      for (final d in defs) Def(d.name, d.kernel, d.term, info.tops[d.name]?.firstOrder ?? false),
    ], e.tests);
  }
  errors.sort((a, b) {
    final (x, y) = (a.span, b.span);
    if (x.start != y.start) return x.start - y.start;
    if (x.end != y.end) return x.end - y.end;
    return a.message.compareTo(b.message);
  });
  final out = <BuildError>[];
  for (final e in errors) {
    if (out.isEmpty || !_same(out.last, e)) out.add(e);
  }
  throw ElabErrors(out);
}

bool _same(BuildError a, BuildError b) {
  if (a.span != b.span || a.message != b.message || a.notes.length != b.notes.length) {
    return false;
  }
  for (var i = 0; i < a.notes.length; i++) {
    if (a.notes[i] != b.notes[i]) return false;
  }
  return true;
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
  final Tables t;

  /// The checker's findings.
  final Info info;

  /// Each binder's kernel name.
  final names = <Binder, String>{};

  /// The term a call leaving a parameter out binds it to, by the function's binder and the
  /// parameter's index.
  final defaults = <(Binder, int), k.Term>{};

  /// The temporary each argument of a call that passes atoms is bound to, while the call is
  /// elaborated.
  final passing = <Span, String>{};

  /// The calls being guarded.
  final guarding = <Span>{};
  var fresh = 0;
  final tests = <Test>[];
  final errors = <BuildError>[];

  /// What the last step to finish built, or a [_Stop] when it stopped on an error.
  Object? _got;

  _Elab(this.t, this.info) {
    final count = <String, int>{}, seen = <String, int>{};
    for (final b in res.binders) {
      count.update(b.name, (c) => c + 1, ifAbsent: () => 1);
    }
    for (final b in res.binders) {
      final i = seen.update(b.name, (c) => c + 1, ifAbsent: () => 1);
      names[b] = count[b.name] == 1 && preludeLayer(b.name) == null ? b.name : '${b.name}@$i';
    }
  }

  Resolution get res => t.res;

  /// Each function binder's declaration.
  Map<Binder, FunctionDef> get funcs => t.funcs;

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

  /// The call `e`, some of whose arguments, at `at`, hold loose atoms their parameter does not
  /// take (rule 6 of sec:type_resolution): the arguments are bound first, and an atom in any
  /// of them is the call's value, those of several merged as a primitive merges them.
  _Steps passes(Expr e, List<Span> at) sync* {
    final args = [
      if (e case Call(:final callee, :final positional, :final named)) ...[
        if (callee case Member(:final of)) of,
        ...positional,
        for (final (_, a) in named) a,
      ],
    ].where((a) => at.contains(a.span)).toList();
    final lets = <(String, k.Term?)>[];
    for (final a in args) {
      final t = temp();
      yield expr(a);
      lets.add((t, termOrNull));
      passing[a.span] = t;
    }
    yield expr(e);
    final call = termOrNull;
    for (final a in args) {
      passing.remove(a.span);
    }
    if (call == null || lets.any((l) => l.$2 == null)) throw const _Stop();
    final bound = [for (final (t, x) in lets) (t, x!)];
    String? fail;
    for (final (t, _) in [...bound]) {
      if (fail == null) {
        fail = t;
        continue;
      }
      final g = temp();
      final (f, v) = (k.Var(fail), k.Var(t));
      final both = k.Match(f, [
        (const k.AnyAtomP(), k.PrimApp(k.Prim.add, [f, v])),
        (const k.WildP(), v),
      ]);
      bound.add((g, k.Match(v, [(const k.AnyAtomP(), both), (const k.WildP(), f)])));
      fail = g;
    }
    var out = fail == null
        ? call
        : k.Match(k.Var(fail), [(const k.AnyAtomP(), k.Var(fail)), (const k.WildP(), call)]);
    for (final (t, x) in bound.reversed) {
      out = k.Let(t, x, out);
    }
    _got = out;
  }

  String kname(Span span, String name) => names[t.id(span, name)]!;

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
    final (order, cycle) = t.order(items);
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
        final f = t.id(s.span, name);
        final ps = [for (final p in params) kname(p.span, p.name)];
        // A default other than a literal or a name is a definition of its own, `f$x`, a
        // function of the parameters it reads, so a call leaving it out calls it rather than
        // holding a copy of it, and defaults that call functions with defaults stay linear in
        // size. A literal or a name is copied: no copy is captured, the kernel names being
        // unique in the unit.
        final at = {for (final (i, p) in params.indexed) t.id(p.span, p.name): i};
        final thunks = <Def>[];
        var ok = true;
        for (final (j, p) in params.indexed) {
          final d = p.fallback;
          if (d == null) continue;
          final read = SplayTreeSet<int>.of([for (final u in t.usesIn(d.span)) ?at[u]]);
          final reads = [for (final i in read) ps[i]];
          yield expr(d);
          final v = termOrNull;
          if (v == null) {
            ok = false;
          } else if (v is k.Lit || v is k.Var) {
            defaults[(f, j)] = v;
          } else {
            final kn = '${names[f]}\$${ps[j]}';
            thunks.add(Def(kn, kn, k.Lam(reads, v)));
            defaults[(f, j)] = k.App(k.Var(kn), [for (final r in reads) k.Var(r)]);
          }
        }
        yield body is Block && !equation ? block(body.stmts) : expr(body);
        final b = termOrNull;
        yield testsOf(s, top);
        if (b == null || failed || !ok) throw const _Stop();
        out
          ..add(Def(name, names[f]!, k.Lam(ps, b)))
          ..addAll(thunks);
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
    if (passing[e.span] case final t?) {
      _got = k.Var(t);
      return;
    }
    if (info.passes[e.span] case final at? when guarding.add(e.span)) {
      yield passes(e, at);
      guarding.remove(e.span);
      return;
    }
    if (info.fits[e.span] case final f?) {
      yield* fit(e, f);
      return;
    }
    if (info.adopt[e.span] case final v?) {
      _got = k.Lit(v);
      return;
    }
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

  /// A call through a value other than a declared function. With the signature the checker
  /// gives the value, named arguments, closed defaults and `...` work as for a declared
  /// function; without one, the arguments are positional.
  _Steps callValue(
    k.Term f,
    k.Term? receiver,
    List<Expr> positional,
    List<(String, Expr)> named,
    bool curry,
    Span span,
  ) sync* {
    final sig = info.calls[span];
    if (sig == null) {
      if (named.isNotEmpty || curry) {
        error(
          span,
          'named arguments and `...` need the parameter names of the function called, '
          'which a prelude word and a value of unknown type do not give',
        );
      }
      yield each(positional);
      _got = k.App(f, [?receiver, ...result<List<k.Term>>()]);
      return;
    }
    final params = sig.params, n = params.length;
    final slots = List<k.Term?>.filled(n, null);
    var next = 0;
    if (receiver != null) {
      if (n == 0) error(span, '`$sig` has no parameter for a receiver');
      slots[0] = receiver;
      next = 1;
    }
    var ok = true;
    for (final a in positional) {
      if (next == n) error(a.span, 'too many arguments: `$sig` takes $n');
      final p = params[next];
      if (!p.positional) {
        error(a.span, '`${p.name}` of `$sig` is named: pass it as `${p.name}: …`');
      }
      yield expr(a);
      slots[next] = termOrNull;
      ok &= slots[next++] != null;
    }
    // Each parameter's index by name, the first where a name repeats.
    final at = {for (var j = n - 1; j >= 0; j--) params[j].name: j};
    for (final (name, a) in named) {
      final j = at[name] ?? error(a.span, '`$sig` has no parameter `$name`');
      if (params[j].positional) {
        error(a.span, '`$name` of `$sig` is positional: pass it by position');
      }
      if (slots[j] != null) error(a.span, '`$name` is already supplied');
      yield expr(a);
      slots[j] = termOrNull;
      ok &= slots[j] != null;
    }
    if (!ok) throw const _Stop();
    final missing = [
      for (var j = 0; j < n; j++)
        if (slots[j] == null) j,
    ];
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
      // The function value is bound once, outside the lambda.
      final fv = temp();
      final temps = [for (final _ in missing) temp()];
      var i = 0;
      final args = [for (final s in slots) s ?? k.Var(temps[i++])];
      _got = k.Let(fv, f, k.Lam(temps, k.App(k.Var(fv), args)));
      return;
    }
    for (final j in missing) {
      final p = params[j];
      switch (p.fallback) {
        case (:final fn, :final index, closed: true):
          yield expr(funcs[fn]!.params[index].fallback!);
          slots[j] = term;
        case _?:
          error(
            span,
            "the default of `${p.name}` reads the function's other parameters, so only a call "
            'of the declared function fills it: pass `${p.name}`',
          );
        case null:
          error(span, 'missing argument `${p.name}` of `$sig`');
      }
    }
    _got = k.App(f, [for (final s in slots) s!]);
  }

  /// A function argument fitted to the function type its slot expects: a lambda whose
  /// parameters are in another order or carry defaults, or a declared function whose named
  /// parameters are in another order.
  _Steps fit(Expr e, Fit how) sync* {
    switch ((how, e)) {
      case (FitLambda(:final order, :final extra), Lambda(:final params, :final body)):
        final ps = [
          for (final o in order) o == null ? temp() : kname(params[o].span, params[o].name),
        ];
        yield body is Block ? block(body.stmts) : expr(body);
        var out = term;
        for (final i in extra.reversed) {
          final p = params[i];
          yield expr(p.fallback!);
          out = k.Let(kname(p.span, p.name), term, out);
        }
        _got = k.Lam(ps, out);
      case (FitAdapter(:final from), NameRef(:final name)):
        final f = this.name(name, e.span);
        final temps = [for (final _ in from) temp()];
        _got = k.Lam(temps, k.App(f, [for (final j in from) k.Var(temps[j])]));
      default:
        throw StateError('a lambda fit is recorded on a lambda, an adapter on a name');
    }
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
      final j = f.paramAt[name] ?? -1;
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
    final at = {for (final (i, j) in missing.indexed) t.id(params[j].span, params[j].name): i};
    final deps = [
      for (final j in missing)
        (SplayTreeSet<int>()..addAll([for (final u in t.usesIn(params[j].fallback!.span)) ?at[u]]))
            .toList(),
    ];
    final (order, cycle) = topo(deps);
    if (cycle != null) {
      final named = [for (final i in cycle) '`${params[missing[i]].name}`'];
      error(span, 'the defaults of ${named.join(', ')} read each other');
    }
    k.Term body = all;
    final defaults = <(String, k.Term)>[];
    for (final i in order) {
      final p = params[missing[i]];
      if (this.defaults[(b, missing[i])] case final d?) {
        defaults.add((pname(p), d));
      } else {
        // A call inside the function's own declaration, before its defaults are bound.
        yield expr(p.fallback!);
        defaults.add((pname(p), term));
      }
    }
    for (final (name, d) in defaults.reversed) {
      body = k.Let(name, d, body);
    }
    _got = supplied(body);
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
        error(
          d.span,
          "a lambda's parameter has a default only where an expected function type leaves it "
          'out',
        );
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
