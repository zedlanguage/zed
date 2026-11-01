/// Recursive type definitions (step L1.23, DESIGN.md sec:type_language): a group of mutually
/// recursive definitions, checked when it is defined and instantiated at its arguments.
///
/// A group is accepted when it is
/// - *contractive*: every cycle of recursive occurrences passes through a constructor (a tuple
///   component, an atom payload, or a morphism bound or value), so a type unfolds to its
///   parts in finitely many steps;
/// - *regular*: every recursive occurrence passes the group's parameters unchanged, so a type
///   has finitely many components;
/// - *monotone in emptiness*: no recursive occurrence stands under a complement, to the right
///   of `\`, or in the guarantee of a morphism type whose value type may be empty or mentions
///   the group, since `type T = (T) -> (#a & #b)` is inhabited exactly when it is empty.
///
/// A value type that mentions a parameter may be empty when that parameter is: it counts as
/// possibly empty when it is empty with every parameter empty, or has a parameter under a
/// complement or to the right of `\`, where a larger argument shrinks it.
library;

import 'dart:math';

import 'types.dart' show Emptiness, Type;

/// A type expression in a definition's body. Each expression knows whether it mentions the
/// group, computed once, so that a part kept unevaluated is shared rather than copied.
sealed class Expr {
  /// `K -> V`, exact.
  factory Expr.exact(Expr key, Expr value) => Morphism(key, key, value);

  Expr._();

  /// The expressions directly in this one.
  List<Expr> get children;

  /// Whether this mentions the group.
  late final bool recursive = this is Ref || children.any((c) => c.recursive);
}

/// The definition's parameter of this index.
final class Param extends Expr {
  final int index;
  Param(this.index) : super._();
  @override
  List<Expr> get children => const [];
}

/// The group's definition of this index, at these arguments.
final class Ref extends Expr {
  final int def;
  final List<Expr> args;
  Ref(this.def, this.args) : super._();
  @override
  List<Expr> get children => args;
}

/// A type that does not mention the group.
final class Given extends Expr {
  final Type type;
  Given(this.type) : super._();
  @override
  List<Expr> get children => const [];
}

/// `a | b | …`.
final class Union extends Expr {
  final List<Expr> items;
  Union(this.items) : super._();
  @override
  List<Expr> get children => items;
}

/// `a & b & …`.
final class And extends Expr {
  final List<Expr> items;
  And(this.items) : super._();
  @override
  List<Expr> get children => items;
}

/// `!a`.
final class Not extends Expr {
  final Expr a;
  Not(this.a) : super._();
  @override
  List<Expr> get children => [a];
}

/// `a \ b`.
final class Diff extends Expr {
  final Expr a, b;
  Diff(this.a, this.b) : super._();
  @override
  List<Expr> get children => [a, b];
}

/// `(a, b, …)`.
final class Tuple extends Expr {
  final List<Expr> items;
  Tuple(this.items) : super._();
  @override
  List<Expr> get children => items;
}

/// `#name(a, b, …)`, whose payload is the tuple of its items.
final class Atom extends Expr {
  final String name;
  final List<Expr> items;
  Atom(this.name, this.items) : super._();
  @override
  List<Expr> get children => items;
}

/// The morphism type with this guarantee, permission and value type.
final class Morphism extends Expr {
  final Expr guarantee, permission, value;
  Morphism(this.guarantee, this.permission, this.value) : super._();
  @override
  List<Expr> get children => [guarantee, permission, value];
}

/// Whether `a` and `b` are the same expression, written alike.
bool _same(Expr a, Expr b) {
  if (identical(a, b)) return true;
  bool all(List<Expr> xs, List<Expr> ys) =>
      xs.length == ys.length &&
      [for (var i = 0; i < xs.length; i++) i].every((i) => _same(xs[i], ys[i]));
  return switch ((a, b)) {
    (Param(index: final i), Param(index: final j)) => i == j,
    (Ref(def: final i, args: final xs), Ref(def: final j, args: final ys)) => i == j && all(xs, ys),
    (Given(type: final s), Given(type: final t)) => s == t,
    (Union(items: final xs), Union(items: final ys)) ||
    (And(items: final xs), And(items: final ys)) ||
    (Tuple(items: final xs), Tuple(items: final ys)) ||
    (Not(children: final xs), Not(children: final ys)) ||
    (Diff(children: final xs), Diff(children: final ys)) ||
    (Morphism(children: final xs), Morphism(children: final ys)) => all(xs, ys),
    (Atom(name: final m, items: final xs), Atom(name: final n, items: final ys)) =>
      m == n && all(xs, ys),
    _ => false,
  };
}

/// A definition `type name(params) = body`.
final class Def {
  final String name;
  final List<String> params;
  final Expr body;
  Def(this.name, this.params, this.body);
}

/// Why a group is rejected: the definition at fault and the reason.
final class Rejection implements Exception {
  /// The index of the definition.
  final int def;

  /// The reason, naming the definition.
  final String message;

  Rejection(this.def, this.message);

  @override
  String toString() => message;
}

/// A checked group of mutually recursive definitions.
final class Group {
  final List<Def> defs;

  Group._(this.defs);

  /// The group of `defs`, if it is contractive, regular and monotone in emptiness; a
  /// [Rejection] otherwise.
  factory Group(List<Def> defs) {
    final g = Group._(defs);
    g._regular();
    g._contractive();
    g._monotone();
    return g;
  }

  Rejection _reject(int def, String why) => Rejection(def, 'the type `${defs[def].name}` $why');

  void _regular() {
    final arity = defs[0].params.length;
    for (final (i, d) in defs.indexed) {
      if (d.params.length != arity) {
        throw _reject(i, 'takes other parameters than the definitions it is recursive with');
      }
      final bad = _refs(d.body).where((e) {
        final args = e.args;
        return args.length != arity ||
            [for (var k = 0; k < arity; k++) k]
                .any((k) => args[k] is! Param || (args[k] as Param).index != k);
      }).firstOrNull;
      if (bad != null) {
        throw _reject(
          i,
          'is not regular: its recursive occurrence `${_show(defs, d.params, null, bad)}` '
          'changes the parameters, so the type has no end of components',
        );
      }
    }
  }

  void _contractive() {
    // The definitions each one names outside every constructor.
    final bare = [for (final d in defs) (_unguarded(d.body, <int>{}).toList()..sort())];
    final start = _firstOnCycle(bare);
    if (start != null) {
      throw _reject(start, 'is not contractive: it reaches itself with no constructor between');
    }
  }

  void _monotone() {
    for (final (i, d) in defs.indexed) {
      final why = _flipped(d.body);
      if (why != null) throw _reject(i, 'is not monotone in emptiness: $why');
    }
  }

  /// Where in `e` a recursive occurrence stands at a place that makes emptiness not
  /// monotone, if one does.
  String? _flipped(Expr e) => switch (e) {
    Not(:final a) when a.recursive => 'a recursive occurrence stands under a complement',
    Diff(:final b) when b.recursive => 'a recursive occurrence stands to the right of `\\`',
    Morphism(guarantee: final l, value: final v)
        when l.recursive && (v.recursive || _mayBeEmpty(v)) =>
      'a recursive occurrence stands in the guaranteed domain of a morphism type whose value '
          'type may be empty or mentions the group',
    _ => e.children.map(_flipped).nonNulls.firstOrNull,
  };

  /// Whether `v`, which mentions no recursive occurrence, is empty at some arguments.
  bool _mayBeEmpty(Expr v) =>
      _shrinks(v, false) ||
      _eval(v, _Env(null, List.filled(defs[0].params.length, Type.empty))).isEmpty;

  /// The group's types at `args`, one per definition. Each is a recursive node that unfolds
  /// to its body.
  List<Type> instance(List<Type> args) {
    if (args.length != defs[0].params.length) {
      throw ArgumentError('one argument per parameter');
    }
    final env = _Env(this, args);
    return env.members = [
      for (final (i, d) in defs.indexed)
        Type.recursive(() => env.name(i), () => _eval(d.body, env)),
    ];
  }
}

/// The recursive occurrences in `e`, outermost first.
Iterable<Ref> _refs(Expr e) sync* {
  if (e is Ref) yield e;
  for (final c in e.children) {
    yield* _refs(c);
  }
}

/// Whether a parameter in `e` stands under a complement or to the right of `\`, where a larger
/// argument shrinks `e`; `under` says whether `e` itself does.
bool _shrinks(Expr e, bool under) => switch (e) {
  Param() => under,
  Not(:final a) => _shrinks(a, true),
  Diff(:final a, :final b) => _shrinks(a, under) || _shrinks(b, true),
  _ => e.children.any((c) => _shrinks(c, under)),
};

/// The lowest vertex of `edges` on a cycle, if one is: Tarjan's strongly connected components,
/// each edge read once, with an explicit stack. A search from each vertex in turn read the
/// graph once per vertex.
int? _firstOnCycle(List<List<int>> edges) {
  final n = edges.length;
  final index = List<int?>.filled(n, null);
  final low = List.filled(n, 0);
  final on = List.filled(n, false);
  final stack = <int>[];
  var next = 0;
  int? first;
  void enter(int v) {
    index[v] = low[v] = next++;
    on[v] = true;
    stack.add(v);
  }

  for (var s = 0; s < n; s++) {
    if (index[s] != null) continue;
    // Each call is a vertex and how many of its edges are read.
    final calls = [(s, 0)];
    enter(s);
    while (calls.isNotEmpty) {
      final (v, k) = calls.last;
      if (k < edges[v].length) {
        calls.last = (v, k + 1);
        final w = edges[v][k];
        if (index[w] == null) {
          enter(w);
          calls.add((w, 0));
        } else if (on[w]) {
          low[v] = min(low[v], index[w]!);
        }
        continue;
      }
      calls.removeLast();
      if (calls.isNotEmpty) {
        final u = calls.last.$1;
        low[u] = min(low[u], low[v]);
      }
      if (low[v] == index[v]) {
        final component = <int>[];
        int w;
        do {
          w = stack.removeLast();
          on[w] = false;
          component.add(w);
        } while (w != v);
        if (component.length > 1 || edges[v].contains(v)) {
          final m = component.reduce(min);
          first = first == null ? m : min(first, m);
        }
      }
    }
  }
  return first;
}

/// The definitions `e` names outside every constructor, added to `out`.
Set<int> _unguarded(Expr e, Set<int> out) {
  switch (e) {
    case Ref(:final def):
      out.add(def);
    case Tuple() || Atom() || Morphism():
      break;
    default:
      for (final c in e.children) {
        _unguarded(c, out);
      }
  }
  return out;
}

/// What an expression is evaluated in: the arguments, and the group's types at them.
final class _Env {
  final Group? group;
  final List<Type> args;
  late final List<Type> members;

  _Env(this.group, this.args);

  /// The name of definition `i` at the arguments: `Tree(int)`.
  String name(int i) {
    final d = group!.defs[i];
    return args.isEmpty ? d.name : '${d.name}(${args.join(', ')})';
  }
}

Type _eval(Expr e, _Env env) {
  Type parts(List<Expr> xs) => Type.tuple([for (final x in xs) _component(x, env)]);
  return switch (e) {
    Param(:final index) => env.args[index],
    Ref(:final def) => env.members[def],
    Given(:final type) => type,
    Union(:final items) => Type.unionAll(items.map((x) => _eval(x, env))),
    And(:final items) => Type.meetAll(items.map((x) => _eval(x, env))),
    Not(:final a) => ~_eval(a, env),
    Diff(:final a, :final b) => _eval(a, env) - _eval(b, env),
    Tuple(:final items) => parts(items),
    Atom(:final name, :final items) => Type.atomWith(name, parts(items)),
    Morphism(guarantee: final l, permission: final u, value: final v) => Type.morphism(
      _component(l, env),
      _component(u, env),
      _component(v, env),
    ),
  };
}

/// `e` in a constructor: when it mentions the group and is more than one occurrence, it is
/// kept as a node evaluated on first use, since evaluating it now could need the parts of the
/// type being built.
Type _component(Expr e, _Env env) {
  if (e is Ref || !e.recursive) return _eval(e, env);
  return Type.recursive(() => _show(env.group!.defs, const [], env.args, e), () => _eval(e, env));
}

/// `e` in the surface syntax, its parameters by name or, with `args`, by value.
String _show(List<Def> defs, List<String> params, List<Type>? args, Expr e) {
  String show(Expr e) => _show(defs, params, args, e);
  String sub(Expr e) => switch (e) {
    Union() || And() || Diff() || Morphism() => '(${show(e)})',
    _ => show(e),
  };
  String list(List<Expr> xs, String sep) => xs.map(sub).join(sep);
  return switch (e) {
    Param(:final index) => args == null ? params[index] : '${args[index]}',
    Ref(:final def, args: []) => defs[def].name,
    Ref(:final def, args: final xs) => '${defs[def].name}(${xs.map(show).join(', ')})',
    Given(:final type) => '$type',
    Union(:final items) => list(items, ' | '),
    And(:final items) => list(items, ' & '),
    Not(:final a) => '!${sub(a)}',
    Diff(:final a, :final b) => '${sub(a)} \\ ${sub(b)}',
    Tuple(:final items) => '(${list(items, ', ')})',
    Atom(:final name, :final items) => '#$name(${list(items, ', ')})',
    Morphism(guarantee: final l, permission: final u, value: final v) when _same(l, u) =>
      '(${sub(l)}) -> ${sub(v)}',
    Morphism(guarantee: Given(:final type), permission: final u, value: final v)
        when type == Type.empty =>
      '${sub(u)} ->? ${sub(v)}',
    Morphism(guarantee: final l, permission: final u, value: final v) =>
      '(${sub(l)} ⊆ dom ⊆ ${sub(u)}) -> ${sub(v)}',
  };
}
