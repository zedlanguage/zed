/// Name resolution (step L1.14): every name a unit uses, tied to the binder it names.
///
/// A bare name resolves in the order of DESIGN.md sec:units, stopping at the first hit: the
/// block scopes, innermost outward; the unit's top level; the prelude. Imports and qualified
/// names arrive at L2. Statement order has no meaning, so a name bound anywhere in a scope is
/// in scope throughout it. A scope is a block, or a function's or lambda's parameters, which
/// share one scope with the statements of a body block (so `f(x) { x = 1; }` rebinds `x`), or
/// the names an `else` pattern binds, in scope in its default. A parameter's type and default
/// see the parameters (`hi: int where lo <= hi`) but not the body's bindings; a function's
/// `test` cases are read in the scope around the function.
///
/// Binding a name twice in one scope is an error, except that functions of one name whose
/// written parameter types differ are the arrows of one overload set; a name in a nested scope
/// shadows the outer one. A name that resolves to a prelude word of a later layer is an error
/// naming the layer. A member `x.f` whose `f` is in scope may be a uniform call `f(x)`; its
/// resolution is recorded, and elaboration (step L1.16) tells a field from a function.
library;

import 'ast.dart';
import 'src/kernel/pmap.dart';
import 'source.dart';

/// What binds a name.
enum Kind {
  /// A binding `x = e;` or a target of `a, b = e;`.
  binding,

  /// A function declaration.
  function,

  /// A parameter of a function or a lambda.
  param,

  /// An output port of a function's header, `-> (stdout: Lines)`.
  port,

  /// A name an `else` pattern binds, `#a(f:)`.
  pattern,
}

/// A binder: a name, where it is bound, and what binds it.
final class Binder {
  final String name;

  /// The text that binds it: the statement, the parameter, the port or the pattern.
  final Span span;
  final Kind kind;

  Binder(this.name, this.span, this.kind);
}

/// What a use of a name names.
sealed class Ref {}

/// Binders of the unit: one, or the arrows of an overload set.
final class Bound extends Ref {
  final List<Binder> binders;

  Bound(this.binders);
}

/// A prelude word of layer L1.
final class Prelude extends Ref {
  final String word;

  Prelude(this.word);
}

int _compare(Span a, Span b) => a.start != b.start ? a.start - b.start : a.end - b.end;

/// The resolution of a unit.
final class Resolution {
  /// The unit's binders, in the order they are met.
  final List<Binder> binders = [];

  /// Each use, by its text, in text order: a name, a type name, a push's statement (whose port
  /// it names), or a member whose name is in scope.
  PMap<Span, Ref> uses = const PMap.empty(_compare);

  /// The binders of each `else` pattern, by the `else`'s text.
  final Map<Span, List<Binder>> patterns = {};
}

/// The errors of a unit that does not resolve, in text order.
final class ResolveErrors implements Exception {
  final List<BuildError> errors;

  ResolveErrors(this.errors);

  @override
  String toString() => errors.join('\n');
}

/// The value words of the prelude, each with the layer it belongs to (DESIGN.md, "Defined
/// words by layer"): at L1 the numeric casts, the `String` cast that interpolation calls, and
/// the `String` functions the documentation uses.
const _words = {
  'String': 1,
  'int': 1,
  'rat': 1,
  'f64': 1,
  'abs': 1,
  'len': 1,
  'lower': 1,
  'upper': 1,
  'trim': 1,
  'sum': 1,
  'count': 3,
  'map': 3,
  'where': 3,
  'foldl': 3,
  'foldr': 3,
  'reduce': 3,
  'allOk': 3,
  'split': 3,
  'lines': 3,
  'concat': 3,
  'fam': 3,
  'discard': 3,
  'fold': 3,
  'reindex': 3,
  'gen': 3,
  'rekey': 4,
  'group': 4,
  'flatMap': 4,
  'tag': 4,
  'sort': 5,
  'rank': 5,
  'scan': 5,
  'zip': 5,
  'patch': 5,
  'join': 5,
  'diff': 5,
  'first': 5,
  'last': 5,
  'minBy': 5,
  'maxBy': 5,
  'slice': 5,
  'take': 5,
  'drop': 5,
  'takeWhile': 5,
  'chunkBy': 5,
  'fix': 6,
};

/// The layer of the prelude value word `name`, if it is one.
int? preludeLayer(String name) => _words[name];

/// The type names of the prelude at L1; a unit declares no type before L2.
const _types = {'int', 'rat', 'f64', 'bool', 'String', 'Lines', 'Files'};

/// The resolution of `unit`; throws [ResolveErrors] with every error in it.
Resolution resolve(List<Stmt> unit) {
  final r = _Resolver()..scopes.add([]);
  _run(r.stmts(unit));
  if (r.errors.isEmpty) return r.out;
  // The sort keeps errors of one span in the order they were met.
  final order = [for (var i = 0; i < r.errors.length; i++) i]
    ..sort(
      (a, b) => switch (_compare(r.errors[a].span, r.errors[b].span)) {
        0 => a - b,
        final c => c,
      },
    );
  throw ResolveErrors([for (final i in order) r.errors[i]]);
}

/// The walk is a tree of generators, each yielding those of the parts it reads; [_run] runs
/// them on one explicit stack, so the depth of the unit's nesting is bounded by memory alone.
typedef _Steps = Iterable<Iterable<Object?>>;

void _run(_Steps steps) {
  final stack = [steps.iterator];
  while (stack.isNotEmpty) {
    if (stack.last.moveNext()) {
      stack.add((stack.last.current as _Steps).iterator);
    } else {
      stack.removeLast();
    }
  }
}

/// A name's binders in one scope.
final class _Bound {
  /// How many scopes are open around the scope, itself included.
  final int level;
  final List<Binder> binders = [];

  /// The written parameter types of each, which tell an overload's arrows apart: a set, so
  /// declaring `K` overloads costs `O(K)`, not `O(K²)`.
  final Set<String?> signatures = {};

  _Bound(this.level);
}

/// A function's written parameter types as one string: each type's text, length first, so no
/// two lists give the same string; `-` for a parameter with none.
String _signature(List<Param> params) => [
  for (final p in params)
    if (p.type?.toString() case final t?) '${t.length}:$t' else '-',
].join();

final class _Resolver {
  final out = Resolution();
  final errors = <BuildError>[];

  /// The scopes, outermost first: the names each binds.
  final scopes = <List<String>>[];

  /// The bindings of each name in the open scopes, innermost last, so a name is found in
  /// `O(1)` however deep the scopes nest.
  final visible = <String, List<_Bound>>{};

  /// Binds `name` in the innermost scope; `signature` is a function's parameter types.
  void bind(String name, Span span, Kind kind, [String? signature]) {
    final level = scopes.length;
    final b = switch (visible[name]) {
      [..., final b] when b.level == level => b,
      _ => null,
    };
    if (b != null) {
      final first = b.binders.first;
      final overload =
          kind == Kind.function && first.kind == Kind.function && !b.signatures.contains(signature);
      if (!overload) {
        final (message, note) = signature != null && first.kind == Kind.function
            ? (
                '`$name` is already declared in this scope with these parameter types',
                'the first `$name` with these parameter types',
              )
            : ('`$name` is already bound in this scope', 'the first binding of `$name`');
        errors.add(BuildError(span, message, [(span: first.span, text: note)]));
        return;
      }
    }
    final binder = Binder(name, span, kind);
    final here = b ?? _Bound(level);
    if (b == null) {
      (visible[name] ??= []).add(here);
      scopes.last.add(name);
    }
    here.binders.add(binder);
    here.signatures.add(signature);
    out.binders.add(binder);
  }

  void open() => scopes.add([]);

  /// Closes the innermost scope, so its names name what they named outside it.
  void close() {
    for (final name in scopes.removeLast()) {
      final v = visible[name]!..removeLast();
      if (v.isEmpty) visible.remove(name);
    }
  }

  /// The binders `name` names here, if any. The list is shared, not copied: a scope binds all
  /// its names before any is read, so it does not change after.
  List<Binder>? found(String name) => visible[name]?.last.binders;

  /// Records the use of `name` at `span`, or the error that it names nothing at L1.
  void name(String name, Span span) {
    if (found(name) case final binders?) {
      out.uses = out.uses.put(span, Bound(binders));
      return;
    }
    final message = switch (preludeLayer(name)) {
      1 => null,
      null => '`$name` is not defined',
      final layer => '`$name` is a prelude word of layer L$layer',
    };
    if (message == null) {
      out.uses = out.uses.put(span, Prelude(name));
    } else {
      errors.add(BuildError(span, message));
    }
  }

  /// The statements of the innermost scope: their binders first, since order has no meaning.
  _Steps stmts(List<Stmt> stmts) sync* {
    for (final s in stmts) {
      switch (s) {
        case Bind(:final targets):
          for (final t in targets) {
            if (t != null) bind(t, s.span, Kind.binding);
          }
        case FunctionDef(:final name, :final params):
          bind(name, s.span, Kind.function, _signature(params));
        case Return() || Push():
          break;
      }
    }
    for (final s in stmts) {
      switch (s) {
        case Bind(:final value):
          yield expr(value);
        case Return(:final values):
          for (final e in values) {
            yield expr(e);
          }
        case Push(:final port, :final value):
          name(port, s.span);
          yield expr(value);
        case FunctionDef(:final params, :final ports, :final body, :final tests):
          for (final p in ports ?? const <Port>[]) {
            yield type(p.type);
          }
          for (final (a, b) in tests) {
            yield expr(a);
            yield expr(b);
          }
          yield function(params, ports ?? const [], body);
      }
    }
  }

  /// A function's or lambda's parameters, ports and body: one scope, which a body block's
  /// statements share.
  _Steps function(List<Param> params, List<Port> ports, Expr body) sync* {
    open();
    for (final p in params) {
      bind(p.name, p.span, Kind.param);
    }
    for (final p in ports) {
      bind(p.name, p.span, Kind.port);
    }
    for (final p in params) {
      if (p.type case final t?) yield type(t);
      if (p.fallback case final d?) yield expr(d);
    }
    yield body is Block ? stmts(body.stmts) : expr(body);
    close();
  }

  _Steps expr(Expr e) sync* {
    switch (e) {
      case IntLit() || FloatLit() || RatLit() || BoolLit() || AtomLit():
        break;
      case StrLit(:final parts):
        for (final p in parts) {
          if (p is StrHole) yield expr(p.e);
        }
      case NameRef(:final name):
        this.name(name, e.span);
      case Unary(e: final a):
        yield expr(a);
      case Binary(:final a, :final b) || Index(e: final a, key: final b):
        yield expr(a);
        yield expr(b);
      case Call(:final callee, :final positional, :final named):
        yield expr(callee);
        for (final a in positional) {
          yield expr(a);
        }
        for (final (_, a) in named) {
          yield expr(a);
        }
      case Tuple(:final items):
        for (final i in items) {
          yield expr(i);
        }
      case Lambda(:final params, :final body):
        yield function(params, const [], body);
      case Is(:final of, :final type):
        yield expr(of);
        yield this.type(type);
      case Else(:final of, :final pattern, :final fallback):
        yield expr(of);
        open();
        if (pattern != null) {
          final start = out.binders.length;
          yield this.pattern(pattern);
          out.patterns[e.span] = out.binders.sublist(start);
        }
        yield expr(fallback);
        close();
      case Block(:final stmts):
        open();
        yield this.stmts(stmts);
        close();
      case If(:final cond, :final then, :final otherwise):
        yield expr(cond);
        yield expr(then);
        yield expr(otherwise);
      case Member(:final of, :final name):
        yield expr(of);
        if (found(name) case final binders?) out.uses = out.uses.put(e.span, Bound(binders));
    }
  }

  /// The names the pattern `p` binds: each field written `f:` binds `f`.
  _Steps pattern(Pattern p) sync* {
    switch (p) {
      case AtomPattern(:final fields, :final items):
        for (final (f, sub) in fields) {
          if (sub == null) {
            bind(f, p.span, Kind.pattern);
          } else {
            yield pattern(sub);
          }
        }
        for (final i in items) {
          yield pattern(i);
        }
    }
  }

  _Steps type(TypeExpr t) sync* {
    switch (t) {
      case TypeName(:final name) when _types.contains(name):
        out.uses = out.uses.put(t.span, Prelude(name));
      case TypeName(:final name):
        errors.add(BuildError(t.span, 'the type `$name` is not defined'));
      case AtomType():
        break;
      case TupleType(:final items) || UnionType(:final items) || AndType(:final items):
        for (final i in items) {
          yield type(i);
        }
      case DiffType(:final a, :final b):
        yield type(a);
        yield type(b);
      case ArrowType(:final params, :final result):
        for (final p in params) {
          yield type(p.type);
        }
        yield type(result);
    }
  }
}
