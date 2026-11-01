/// Staging (DESIGN.md sec:staging, step L1.28): which terms the build evaluates.
///
/// A term is build-stage when every name it reads is bound to a build-stage term or is a
/// prelude word, and it reads no port. [mix] evaluates the build-stage terms the program
/// demands and leaves the rest to run; a term whose form does not show that it ends ([ends]),
/// or whose evaluation fails, is left to run whole. A definition nothing reads is never
/// evaluated. The Trick ([trick], [split]) specializes a function on a parameter only when the
/// parameter's domain is finite.
library;

import 'dart:collection';

import 'elab.dart' show Def, Unit, free;
import 'interp.dart' show prelude, word;
import 'kernel.dart';

/// When a term is evaluated.
enum Stage {
  /// By the build, once.
  build,

  /// By each wave.
  run,
}

/// What [mix] did.
final class Report {
  /// The definitions the build computed, in order.
  final built = <String>[];

  /// The definitions, top-level or local, nothing reads, which are never evaluated.
  final unread = <String>[];

  /// The build-stage terms left to run, each with why.
  final left = <(String, String)>[];

  @override
  String toString() => 'Report(built: $built, unread: $unread, left: $left)';
}

/// The subterms of a term that binds nothing.
List<Term> _children(Term t) => switch (t) {
  App(:final f, :final args) => [f, ...args],
  PrimApp(:final args) => args,
  If(:final cond, :final then, :final orElse) => [cond, then, orElse],
  Reindex(:final family, :final kf, :final vf) => [family, kf, vf],
  Discard(:final family, :final sel) => [family, sel],
  Fold(:final family, :final op, :final identity) => [family, op, ?identity],
  Gen(:final init, :final step, :final guard) => [init, step, guard],
  Push(:final value) => [value],
  _ => const [],
};

/// Whether `t` is shown to end by its form (docs/thresholds.md, replacement 6): it has no
/// `fix` or `gen`, and every function it calls, or hands to a family operation, is a
/// primitive, a lambda whose body ends, or a name a `let` binds to one. A `let` binds a name
/// only in its body, so such calls nest no deeper than the term; a call through a parameter
/// or a pattern variable, as in `w(w)`, is not shown to end. Free names are prelude words,
/// which are primitives. Each subterm is read once.
bool ends(Term t) => _Around().ends(t);

/// The names bound around a term, each with whether it is bound to a function that ends. A
/// term nests as deep as its source, past the depth of the call stack, so the walk runs over
/// a stack of tasks, and each result goes on a stack of results.
final class _Around {
  /// For each name, its bindings, innermost last.
  final _byName = <String, List<bool>>{};

  /// The names in the order bound, innermost last.
  final _order = <String>[];

  /// The tasks due, the next last.
  final _tasks = <void Function()>[];

  /// The results of the terms read, the latest last.
  final _results = <bool>[];

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

  bool ends(Term t) {
    _tasks.add(() => _visit(t));
    while (_tasks.isNotEmpty) {
      _tasks.removeLast()();
    }
    return _results.single;
  }

  /// Runs `steps` in order, before the tasks already due.
  void _then(List<void Function()> steps) {
    for (var i = steps.length - 1; i >= 0; i--) {
      _tasks.add(steps[i]);
    }
  }

  void Function() _ends(Term t) =>
      () => _visit(t);

  /// Replaces the last `k` results with whether all of them hold.
  void Function() _all(int k) => () {
    var all = true;
    for (var i = 0; i < k; i++) {
      all = _results.removeLast() && all;
    }
    _results.add(all);
  };

  /// Reads `body` with `names` bound around it to values not known to be functions that end.
  List<void Function()> _under(Iterable<String> names, Term body) {
    late final int n;
    return [
      () {
        n = _order.length;
        for (final x in names) {
          _push(x, false);
        }
      },
      _ends(body),
      () => _truncate(n),
    ];
  }

  void _visit(Term t) {
    switch (t) {
      case Lit() || Var() || PrimFn() || Read():
        _results.add(true);
      case Fix() || Gen():
        _results.add(false);
      case Lam(:final params, :final body):
        _then(_under(params, body));
      case App(:final f, :final args):
        _then([_callable(f), for (final a in args) _ends(a), _all(1 + args.length)]);
      case Let(:final name, :final value, :final body):
        _let(name, value, body);
      case Match(:final scrutinee, :final arms):
        _then([
          _ends(scrutinee),
          for (final arm in arms) ..._under(_binds(arm.$1), arm.$2),
          _all(1 + arms.length),
        ]);
      case Fam(:final domain, :final variable, :final body):
        _then([
          _ends(domain),
          ..._under([variable], body),
          _all(2),
        ]);
      case Reindex(:final family, :final kf, :final vf):
        _then([_ends(family), _callable(kf), _callable(vf), _all(3)]);
      case Discard(:final family, :final sel):
        _then([_ends(family), _callable(sel), _all(2)]);
      case Fold(:final family, :final op, :final identity):
        _then([
          _ends(family),
          _callable(op),
          if (identity != null) _ends(identity),
          _all(identity == null ? 2 : 3),
        ]);
      case PrimApp(:final args):
        _then([for (final a in args) _ends(a), _all(args.length)]);
      case If(:final cond, :final then, :final orElse):
        _then([_ends(cond), _ends(then), _ends(orElse), _all(3)]);
      case Push(:final value):
        _tasks.add(_ends(value));
    }
  }

  void _let(String x, Term e, Term b) {
    late final int n;
    if (e is Lam) {
      // A lambda bound and never called need not end, so the `let` ends when its body does.
      _then([
        _ends(e),
        () {
          n = _order.length;
          _push(x, _results.removeLast());
        },
        _ends(b),
        () => _truncate(n),
      ]);
    } else {
      // Any other binding is evaluated, so it must end.
      _then([
        _ends(e),
        () {
          n = _order.length;
          _push(x, _results.last && _named(e));
        },
        _ends(b),
        () => _truncate(n),
        _all(2),
      ]);
    }
  }

  /// Whether `f`, in the position of a function called, is one that ends: a primitive, a
  /// lambda whose body ends, or a name bound to one; a free name is a prelude word.
  void Function() _callable(Term f) =>
      () => f is Lam ? _visit(f) : _results.add(_named(f));

  /// Whether `f`, not a lambda, is a primitive or a name bound to a function that ends.
  bool _named(Term f) => switch (f) {
    PrimFn() => true,
    Var(:final name) => _byName[name]?.last ?? true,
    _ => false,
  };
}

/// The names `p` binds.
List<String> _binds(Pattern p) => switch (p) {
  BindP(:final name) => [name],
  AtomP(args: final ps) || TupleP(items: final ps) => [for (final q in ps) ..._binds(q)],
  FieldsP(:final fields) => [for (final (_, q) in fields) ..._binds(q)],
  _ => const [],
};

/// Whether `t` reads or writes a port.
bool _effects(Term t) => switch (t) {
  Read() || Push() => true,
  Lit() || Var() || PrimFn() => false,
  Lam(:final body) => _effects(body),
  Let(:final value, :final body) => _effects(value) || _effects(body),
  Match(:final scrutinee, :final arms) =>
    _effects(scrutinee) || arms.any((arm) => _effects(arm.$2)),
  Fam(:final domain, :final body) => _effects(domain) || _effects(body),
  Fix(:final init, :final step) => _effects(init) || _effects(step),
  _ => _children(t).any(_effects),
};

/// The stage of each definition of `unit`, by source name, in order.
List<(String, Stage)> color(Unit unit) {
  final m = _Mixer();
  return [for (final d in unit.defs) (d.name, m.bindStaged(d.kernel, d.term))];
}

/// `unit` with its demanded build-stage terms evaluated, keeping the definitions `roots`
/// and the tests read.
(Unit, Report) mix(Unit unit, Iterable<String> roots) {
  final rootSet = roots.toSet();
  final demanded = <String>{
    for (final d in unit.defs)
      if (rootSet.contains(d.name)) d.kernel,
    for (final t in unit.tests)
      for (final term in [t.check, ...t.args, t.want]) ...free(term),
  };
  for (final d in unit.defs.reversed) {
    if (demanded.contains(d.kernel)) demanded.addAll(free(d.term));
  }
  final m = _Mixer();
  final defs = <Def>[];
  for (final d in unit.defs) {
    if (!demanded.contains(d.kernel)) {
      m.report.unread.add(d.name);
      continue;
    }
    final term = m.mixTop(d.term);
    if (term is Lit && !identical(term, d.term)) m.report.built.add(d.name);
    m.bind(d.kernel, m.known(term), term);
    defs.add(Def(d.name, d.kernel, term, d.firstOrder));
  }
  return (Unit(defs, unit.tests), m.report);
}

/// The domain of a parameter.
sealed class Domain {
  const Domain();
}

/// The values of a type.
final class TypeDomain extends Domain {
  final Type type;

  const TypeDomain(this.type);
}

/// The integers between two bounds, either of which may be absent.
final class Ints extends Domain {
  final int? lo, hi;

  const Ints(this.lo, this.hi);
}

/// What the Trick decides for a parameter.
sealed class Choice {
  const Choice();
}

/// Specialize on each of these values.
final class Split extends Choice {
  final List<Value> values;

  const Split(this.values);

  @override
  String toString() => 'Split($values)';
}

/// Do not specialize, for this reason.
final class Keep extends Choice {
  final String why;

  const Keep(this.why);

  @override
  String toString() => 'Keep($why)';
}

/// The Trick: split on the members of `d` among `passed` only when `d` is finite. A type is
/// finite here when it lists its values no longer than it is written ([Type.listed]).
Choice trick(Domain d, Iterable<Value> passed) {
  final List<Value> within;
  switch (d) {
    case TypeDomain(:final type):
      if (type.listed == null) return Keep('the domain `$type` is not a finite list');
      within = [
        for (final v in passed)
          if (type.contains(v)) v,
      ];
    case Ints(:final lo?, :final hi?):
      within = [
        for (final v in passed)
          if (v case Int(:final value) when lo <= value && value <= hi) v,
      ];
    case Ints():
      return const Keep('an unbounded integer domain is infinite');
  }
  if (within.isEmpty) return const Keep('no static call passes a value of the domain');
  return Split(within);
}

/// The values the static calls of `name` in `unit` pass its parameter `param`, in order: each
/// call by its kernel name, in a definition once mixed, whose argument there is a literal, and
/// each case of a test of `name` whose argument there is a literal.
SplayTreeSet<Value> passed(Unit unit, String name, int param) {
  final out = SplayTreeSet<Value>();
  final f = unit.defs.where((d) => d.name == name).firstOrNull;
  if (f == null) return out;
  final (mixed, _) = mix(unit, [for (final d in unit.defs) d.name]);
  for (final d in mixed.defs) {
    _calls(d.term, f.kernel, param, out);
  }
  for (final t in unit.tests.where((t) => t.function == name && param < t.args.length)) {
    if (t.args[param] case Lit(:final value)) out.add(value);
  }
  return out;
}

/// Adds to `out` the literal argument `param` of each call of `f` in `t`.
void _calls(Term t, String f, int param, Set<Value> out) {
  final stack = [t];
  while (stack.isNotEmpty) {
    final t = stack.removeLast();
    if (t case App(f: Var(:final name), :final args) when name == f && param < args.length) {
      if (args[param] case Lit(:final value)) out.add(value);
    }
    switch (t) {
      case Lam(:final body):
        stack.add(body);
      case Let(:final value, :final body):
        stack.addAll([value, body]);
      case Match(:final scrutinee, :final arms):
        stack
          ..add(scrutinee)
          ..addAll(arms.map((arm) => arm.$2));
      case Fam(:final domain, :final body):
        stack.addAll([domain, body]);
      case Fix(:final init, :final step):
        stack.addAll([init, step]);
      default:
        stack.addAll(_children(t));
    }
  }
}

/// Why the Trick keeps a function, or why it cannot be split.
final class Kept implements Exception {
  final String why;

  const Kept(this.why);

  @override
  String toString() => why;
}

/// The function `name` of `unit` split on its parameter `param` over the values of `d` its
/// static calls pass ([passed]), each arm its body mixed with the parameter known, and the
/// general body last; throws [Kept] with why the Trick keeps it.
(Term, Report) split(Unit unit, String name, int param, Domain d) {
  final at = unit.defs.indexWhere((d) => d.name == name);
  if (at < 0) throw Kept('no definition `$name`');
  if (unit.defs[at].term case Lam(:final params, :final body)) {
    if (param >= params.length) throw Kept('`$name` has no parameter $param');
    final p = params[param];
    final values = switch (trick(d, passed(unit, name, param))) {
      Split(:final values) => values,
      Keep(:final why) => throw Kept(why),
    };
    final m = _Mixer();
    for (final d in unit.defs.take(at)) {
      m.bindStaged(d.kernel, d.term);
    }
    final n = m.scope.length;
    for (final q in params) {
      m.bind(q, Stage.run, Var(q));
    }
    final arms = <(Pattern, Term)>[];
    for (final v in values) {
      m.bind(p, Stage.build, Lit(v));
      arms.add((LitP(v), m.mixTop(body)));
      m.scope.pop();
    }
    arms.add((const WildP(), m.mixTop(body)));
    m.scope.truncate(n);
    return (Lam(params, Match(Var(p), arms)), m.report);
  }
  throw Kept('`$name` is not a function');
}

/// A name in scope: its term when it is build-stage, else null, and the names that term reads.
final class _Entry {
  final String name;
  final Term? known;
  final Set<String> reads;

  _Entry(this.name, this.known) : reads = known == null ? const {} : free(known);
}

/// The names in scope, innermost last, with the positions of each name's entries, so a name
/// is looked up without a scan of the scope.
final class _Scope {
  final entries = <_Entry>[];
  final _byName = <String, List<int>>{};

  int get length => entries.length;

  void push(String name, Term? known) {
    _byName.putIfAbsent(name, () => []).add(entries.length);
    entries.add(_Entry(name, known));
  }

  void pop() {
    final e = entries.removeLast();
    final at = _byName[e.name]!..removeLast();
    if (at.isEmpty) _byName.remove(e.name);
  }

  void truncate(int n) {
    while (length > n) {
      pop();
    }
  }

  /// The innermost entry of `x`; null for a name the scope does not bind.
  _Entry? lookup(String x) => switch (_byName[x]) {
    final at? => entries[at.last],
    null => null,
  };

  /// The position of the innermost build-stage entry of `x` below position `below`.
  int? knownBelow(String x, int below) {
    final at = _byName[x];
    if (at == null) return null;
    // The entries of `x` below `below`: a binary search, since positions only grow.
    var (lo, hi) = (0, at.length);
    while (lo < hi) {
      final mid = (lo + hi) >> 1;
      if (at[mid] < below) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    for (var i = lo - 1; i >= 0; i--) {
      if (entries[at[i]].known != null) return at[i];
    }
    return null;
  }
}

/// No name read, or none unknown at build: larger than every position.
const _none = 1 << 62;

/// A value of [_Mins]: a name read that cannot be known at build, or a port read.
const _run = -1;

/// The least of the values of a range of positions, with one value changed at a time, in
/// `O(log n)` each.
final class _Mins {
  final int n;
  final List<int> tree;

  _Mins(List<int> values)
    : n = values.length,
      tree = [...List.filled(values.length, _none), ...values] {
    for (var i = n - 1; i >= 1; i--) {
      tree[i] = _min(tree[2 * i], tree[2 * i + 1]);
    }
  }

  static int _min(int a, int b) => a < b ? a : b;

  void set(int i, int v) {
    i += n;
    tree[i] = v;
    while (i > 1) {
      i >>= 1;
      tree[i] = _min(tree[2 * i], tree[2 * i + 1]);
    }
  }

  /// The least value of the positions `l` to `r`, `r` excluded.
  int min(int l, int r) {
    var m = _none;
    l += n;
    r += n;
    for (; l < r; l >>= 1, r >>= 1) {
      if (l.isOdd) m = _min(m, tree[l++]);
      if (r.isOdd) m = _min(m, tree[--r]);
    }
    return m;
  }
}

/// The subterms of a term, in the order `mix` meets them, each with the names it is under.
/// The join of a lattice recursion is marked, since a port it reads is not an effect of the
/// recursion ([_effects]).
List<(Term, List<String>, bool)> _kids(Term t) => switch (t) {
  Lam(:final params, :final body) => [(body, params, false)],
  Let(:final name, :final value, :final body) => [
    (value, const [], false),
    (body, [name], false),
  ],
  Match(:final scrutinee, :final arms) => [
    (scrutinee, const [], false),
    for (final (p, a) in arms) (a, _binds(p), false),
  ],
  Fam(:final domain, :final variable, :final body) => [
    (domain, const [], false),
    (body, [variable], false),
  ],
  Fix(:final init, :final step, :final self, :final key, :final kind) => [
    (init, const [], false),
    (step, [self, key], false),
    if (kind case Lattice(:final join)) (join, [self, key], true),
  ],
  _ => [for (final c in _children(t)) (c, const [], false)],
};

/// The term `mix` is mixing, by preorder position: a subterm is build-stage when no name it
/// reads, bound outside it, is unknown at build and it reads no port. Each position holds the
/// position of the binder of the unknown name read there, or [_run], so a subterm at
/// `p..p + size` is build-stage exactly when the least value there is at least `p`: its own
/// binders are at `p` or after. Deciding the stage of a subterm is then one query, where
/// reading its free names costs `O(size)` at each of the nodes `mix` enters.
final class _Index {
  final size = <int>[];

  /// For a name read, the position of the binder inside the term that binds it.
  final binder = <int?>[];

  /// The positions reading each binder's names.
  final reads = <int, List<int>>{};

  /// How many names of each binder the mixed term still reads.
  final kept = <int, int>{};

  late final _Mins _mins;

  _Index(Term t, _Scope scope) {
    final values = <int>[];
    _walk(t, scope, values);
    _mins = _Mins(values);
  }

  _Index.empty() {
    _mins = _Mins(const []);
  }

  /// Numbers the subterms of `root` in preorder. A term nests as deep as its source, past the
  /// depth of the call stack, so the walk runs over a stack of tasks.
  void _walk(Term root, _Scope scope, List<int> values) {
    final bound = <String, List<int>>{};
    final tasks = <void Function()>[];
    void visit(Term t, bool join) {
      final at = size.length;
      size.add(0);
      binder.add(null);
      values.add(_none);
      switch (t) {
        case Var(:final name):
          if (bound[name] case [..., final b]) {
            binder[at] = b;
            reads.putIfAbsent(b, () => []).add(at);
            values[at] = b;
          } else {
            final known = switch (scope.lookup(name)) {
              final e? => e.known != null,
              null => word(name),
            };
            if (!known) values[at] = _run;
          }
        case Read() || Push() when !join:
          values[at] = _run;
        default:
      }
      final steps = <void Function()>[
        for (final (c, names, inJoin) in _kids(t)) ...[
          () {
            for (final x in names) {
              bound.putIfAbsent(x, () => []).add(at);
            }
          },
          () => visit(c, join || inJoin),
          () {
            for (final x in names) {
              final b = bound[x]!..removeLast();
              if (b.isEmpty) bound.remove(x);
            }
          },
        ],
        () => size[at] = size.length - at,
      ];
      tasks.addAll(steps.reversed);
    }

    tasks.add(() => visit(root, false));
    while (tasks.isNotEmpty) {
      tasks.removeLast()();
    }
  }

  bool build(int at) => _mins.min(at, at + size[at]) >= at;

  /// The positions of the subterms of the term at `at`, of which there are `n`.
  List<int> kids(int at, int n) {
    var p = at + 1;
    return [
      for (var i = 0; i < n; i++)
        (() {
          final k = p;
          p += size[k];
          return k;
        })(),
    ];
  }

  /// The binder at `at` is known at build: the names it binds no longer make a term run-stage.
  void known(int at) {
    for (final p in reads[at] ?? const <int>[]) {
      _mins.set(p, _none);
    }
  }

  /// The subterm at `at` is kept as written: the names it reads are read by the mixed term.
  void keep(int at) {
    for (var p = at; p < at + size[at]; p++) {
      if (binder[p] case final b?) kept[b] = (kept[b] ?? 0) + 1;
    }
  }
}

final class _Mixer {
  final scope = _Scope();
  final report = Report();
  var index = _Index.empty();

  void bind(String name, Stage stage, Term t) => scope.push(name, stage == Stage.build ? t : null);

  /// Binds `name` to `t` at the stage `t` has, which it returns.
  Stage bindStaged(String name, Term t) {
    final s = stage(t);
    bind(name, s, t);
    return s;
  }

  /// The stage a name bound to the mixed term `t` has: build when `t` is a literal or a
  /// build-stage function, run when it is left to run, so that nothing evaluates it again.
  Stage known(Term t) => switch (t) {
    Lit() => Stage.build,
    Lam() || PrimFn() || Var() => stage(t),
    _ => Stage.run,
  };

  void unknown(List<String> names) {
    for (final x in names) {
      scope.push(x, null);
    }
  }

  Stage stage(Term t) {
    final known = free(t).every(
      (x) => switch (scope.lookup(x)) {
        final e? => e.known != null,
        null => word(x),
      },
    );
    return known && !_effects(t) ? Stage.build : Stage.run;
  }

  /// The value of the build-stage term `t`, under the bindings it needs: the innermost
  /// build-stage entry of each name it reads, and of each name those read, below them. Throws
  /// a [Kept] with why it is not computed.
  Value eval(Term t) {
    final top = scope.length;
    final todo = SplayTreeSet<int>.of([for (final x in free(t)) ?scope.knownBelow(x, top)]);
    var closed = t;
    while (todo.isNotEmpty) {
      final i = todo.last;
      todo.remove(i);
      final e = scope.entries[i];
      todo.addAll([for (final x in e.reads) ?scope.knownBelow(x, i)]);
      closed = Let(e.name, e.known!, closed);
    }
    if (!ends(closed)) throw const Kept('its form does not show that it ends');
    try {
      return Evaluator(World()).run(prelude(closed));
    } on KernelError catch (e) {
      throw Kept('$e');
    }
  }

  /// `t` with its build-stage subterms evaluated.
  Term mixTop(Term t) {
    index = _Index(t, scope);
    return _mix(t, 0);
  }

  /// The tasks due, the next last, and the mixed terms, the latest last. A term nests as
  /// deep as its source, past the depth of the call stack, so mixing runs over these stacks.
  final _tasks = <void Function()>[];
  final _terms = <Term>[];

  /// The subterm `t` at position `at` of the term [mixTop] is mixing, with its build-stage
  /// subterms evaluated.
  Term _mix(Term t, int at) {
    final base = _tasks.length;
    _tasks.add(_m(t, at));
    while (_tasks.length > base) {
      _tasks.removeLast()();
    }
    return _terms.removeLast();
  }

  /// Runs `steps` in order, before the tasks already due.
  void _then(List<void Function()> steps) {
    for (var i = steps.length - 1; i >= 0; i--) {
      _tasks.add(steps[i]);
    }
  }

  void Function() _m(Term t, int at) =>
      () => _step(t, at);

  /// Replaces the last `k` terms mixed with `f` of them.
  void Function() _join(int k, Term Function(List<Term>) f) => () {
    final parts = _terms.sublist(_terms.length - k);
    _terms.length -= k;
    _terms.add(f(parts));
  };

  /// Mixes `t` with `names` bound around it to values unknown at build.
  List<void Function()> _under(List<String> names, Term t, int at) {
    late final int n;
    return [
      () {
        n = scope.length;
        unknown(names);
      },
      _m(t, at),
      () => scope.truncate(n),
    ];
  }

  void _step(Term t, int at) {
    final value = switch (t) {
      Lit() || PrimFn() || Lam() => false,
      Var(:final name) => switch (scope.lookup(name)?.known) {
        null || Lam() || PrimFn() => false,
        _ => true,
      },
      _ => true,
    };
    if (value && index.build(at)) {
      try {
        _terms.add(Lit(eval(t)));
      } on Kept catch (e) {
        report.left.add(('$t', e.why));
        index.keep(at);
        _terms.add(t);
      }
      return;
    }
    final k = index.kids(at, _kids(t).length);
    switch (t) {
      // A name kept here is bound to no literal (one bound to a literal was computed above),
      // so it does not keep a definition `Let` would drop.
      case Lit() || Var() || PrimFn() || Read():
        _terms.add(t);
      case Lam(:final params, :final body):
        _then([..._under(params, body, k[0]), _join(1, (p) => Lam(params, p[0]))]);
      case Let(:final name, :final value, :final body):
        if (index.build(k[0]) && !index.reads.containsKey(at)) {
          report.unread.add(name);
          _tasks.add(_m(body, k[1]));
          return;
        }
        _then([
          _m(value, k[0]),
          () {
            final e = _terms.last;
            final stage = known(e);
            bind(name, stage, e);
            if (stage == Stage.build) index.known(at);
          },
          _m(body, k[1]),
          () {
            scope.pop();
            final b = _terms.removeLast();
            final e = _terms.removeLast();
            _terms.add(e is Lit && !index.kept.containsKey(at) ? b : Let(name, e, b));
          },
        ]);
      case If(:final cond, :final then, :final orElse):
        _then([
          _m(cond, k[0]),
          () => switch (_terms.removeLast()) {
            Lit(value: Bool(value: true)) => _tasks.add(_m(then, k[1])),
            Lit(value: Bool(value: false)) => _tasks.add(_m(orElse, k[2])),
            final atom && Lit(value: Atom()) => _terms.add(atom),
            final c => _then([
              _m(then, k[1]),
              _m(orElse, k[2]),
              _join(2, (p) => If(c, p[0], p[1])),
            ]),
          },
        ]);
      case App(:final f, :final args):
        _then([
          _m(f, k[0]),
          for (var i = 0; i < args.length; i++) _m(args[i], k[i + 1]),
          _join(1 + args.length, (p) => App(p[0], p.sublist(1))),
        ]);
      case PrimApp(:final prim, :final args):
        _then([
          for (var i = 0; i < args.length; i++) _m(args[i], k[i]),
          _join(args.length, (p) => PrimApp(prim, p)),
        ]);
      case Match(:final scrutinee, :final arms):
        _then([
          _m(scrutinee, k[0]),
          for (var i = 0; i < arms.length; i++) ..._under(_binds(arms[i].$1), arms[i].$2, k[i + 1]),
          _join(
            1 + arms.length,
            (p) => Match(p[0], [for (var i = 0; i < arms.length; i++) (arms[i].$1, p[i + 1])]),
          ),
        ]);
      case Fam(:final domain, :final variable, :final body):
        _then([
          _m(domain, k[0]),
          ..._under([variable], body, k[1]),
          _join(2, (p) => Fam(p[0], variable, p[1])),
        ]);
      case Reindex(:final family, :final kf, :final vf, :final witness):
        _then([
          _m(family, k[0]),
          _m(kf, k[1]),
          _m(vf, k[2]),
          _join(3, (p) => Reindex(p[0], p[1], p[2], witness)),
        ]);
      case Discard(:final family, :final sel):
        _then([_m(family, k[0]), _m(sel, k[1]), _join(2, (p) => Discard(p[0], p[1]))]);
      case Fold(:final family, :final op, :final identity, :final depth, :final ev):
        _then([
          _m(family, k[0]),
          _m(op, k[1]),
          if (identity != null) _m(identity, k[2]),
          _join(
            identity == null ? 2 : 3,
            (p) => Fold(p[0], p[1], identity == null ? null : p[2], depth, ev),
          ),
        ]);
      case Gen(:final init, :final step, :final guard, :final pos):
        _then([
          _m(init, k[0]),
          _m(step, k[1]),
          _m(guard, k[2]),
          _join(3, (p) => Gen(p[0], p[1], p[2], pos)),
        ]);
      // A recursion's binders are left as written; recursion arrives at L6.
      case Fix():
        index.keep(at);
        _terms.add(t);
      case Push(:final port, :final value):
        _then([_m(value, k[0]), _join(1, (p) => Push(port, p[0]))]);
    }
  }
}
