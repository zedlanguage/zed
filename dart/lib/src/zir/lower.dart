/// Kernel → ZIR lowering (step L1.33), and the inverse map back to a kernel term.
///
/// [lower] turns a closed kernel term into a graph whose root region yields the term's value.
/// Where DESIGN.md does not say, step L1.33 decides:
///
/// - **One node per operation, constants on edges.** A literal is a constant input, a `let`
///   binds a name to an edge and makes no node, and its name becomes a hint facet `name` on
///   that edge. A prelude word applied to its arguments is a `prim` node; passed as a value it
///   is a `prim` node with no inputs, not a lambda that calls it, since the kernel tells the two
///   apart: a fold of `+` itself sums exactly, and of `(a, b) -> a + b` rounds at each step. A
///   call of a literal lambda, `((x) -> e)(a)`, binds `x` to `a`'s edge and lowers `e` in place.
/// - **Captures on demand.** A name bound outside the region being built enters it as a
///   capture, through every region between, in the order the body first reads it. The regions
///   of one node share one capture list, the union of theirs in order, so each region is
///   renumbered to it after it is built.
/// - **State edges on demand.** The first read of or push to a port takes its state edge,
///   which enters a region as a capture and leaves it as a result, after the values. Only
///   `match` and `port` regions carry state (step L1.31), so a `match` or `if` whose arms touch
///   different ports passes each port's state through the arm that does not touch it, and the
///   root region is a `port` region when the term uses a port and a `function` region when not.
/// - **A function that uses a port threads its state.** A `let`-bound lambda whose body reads
///   or pushes a port, or calls such a function, is inlined at its call when its name occurs
///   once in the term. Otherwise it is one `lambda` node whose region takes a state argument
///   for each of those ports after its parameters and returns their states after its value,
///   and each call is an `apply` that passes the current states in and takes the new ones
///   out. So each body is lowered once, and a chain of such functions, each calling the one
///   before twice, is linear in size, not exponential as inlining every call would make it
///   (DESIGN.md Part G). Used as a value, such a function is an error, since a call through
///   an unknown function could not thread the states.
/// - **CSE by content address.** A node is entered in its region under the key of its
///   canonical form ([nodeKey], hashed from the keys of its regions, so equal keys mean equal
///   normal forms of the one-node regions holding the nodes), and a second node with that key
///   is not added: its uses read the first. Nodes that differ only in hints, binder names or
///   facet order are one node. A read, a push, or a node an effect passes through is never
///   merged, since its state input is used once.
/// - **Edges carry `_` and no facts but hints.** The checker's types and the store's domains
///   reach the graph in a later step; the lowering keeps the term's structure exactly.
///
/// [raise] maps a graph back to a kernel term: each node a `let`, each region a lambda body or
/// a match arm. Evaluating the raised term gives the original term's value, which is how the
/// tests check the lowering against the interpreter.
///
/// A term nests as deep as its source, past the depth of the call stack, so the lowering runs
/// over a stack of tasks, and each result goes on a stack of results.
library;

import '../../address.dart';
import '../canon/canon.dart' show Facet;
import '../kernel/pmap.dart';
import '../kernel/term.dart';
import '../kernel/types.dart' show Type;
import '../kernel/value.dart';
import 'canon.dart';
import 'graph.dart';
import 'text.dart' as text;

/// The graph of the closed term `t`, validated; throws a [ZirError] when the graph cannot hold
/// `t`. A prelude word is read only where the term binds it, as `prelude` does.
Region lower(Term t) => _Lower(t).run(t);

/// What a name is bound to while lowering.
sealed class _Val {}

/// An edge of the region at `depth` in the frame stack.
final class _Edge extends _Val {
  final Src src;
  final int depth;

  _Edge(this.src, this.depth);
}

/// A prelude word, not yet a node.
final class _Prim extends _Val {
  final Prim prim;

  _Prim(this.prim);
}

/// A `let`-bound lambda whose body uses `ports`, in the order of their first use, called only
/// by name.
final class _Closure extends _Val {
  final List<String> params;
  final List<String> ports;
  final _Call call;

  _Closure(this.params, this.ports, this.call);
}

/// How a call of a [_Closure] lowers.
sealed class _Call {}

/// Its body in place, under the bindings it was defined under: the name occurs once.
final class _Inline extends _Call {
  final Term body;
  final _Scope env;

  _Inline(this.body, this.env);
}

/// An `apply` of its `lambda` node's output `fun`, in the region at depth `at`.
final class _Applied extends _Call {
  final Src fun;
  final int at;

  _Applied(this.fun, this.at);
}

/// The binding of each name in scope, kept persistently so that a closure keeps the scope it
/// was defined in at no cost.
typedef _Scope = PMap<String, _Val>;

int _byName(String a, String b) => a.compareTo(b);

/// What a lambda body uses from outside it: a port it reads or pushes, or a name free in it.
typedef _Use = ({bool port, String name});

/// A region being built, and once built, what its node needs to know about it.
final class _Frame {
  final Region region;

  /// The arguments before the captures.
  final int fixed;

  /// Where each capture comes from in the enclosing region, in argument order.
  final captures = <Src>[];

  /// The current state edge of each port the region has touched.
  final states = <String, Src>{};

  /// The nodes entered by content address.
  final seen = <ContentAddress, int>{};

  /// The keys of each node's regions, in node order.
  final keys = <List<ContentAddress>>[];

  _Frame(RegionKind kind, List<Edge> args)
    : region = Region(kind, args, [], []),
      fixed = args.length;
}

final class _Lower {
  final _frames = <_Frame>[];
  _Scope _scope = const PMap.empty(_byName);
  var _fresh = 0;

  /// How often each name occurs in the term, binders of the same name counted together.
  final _uses = <String, int>{};

  /// The uses of each lambda body met so far, by identity.
  final Map<Term, List<_Use>> _bodies = Map.identity();

  /// The tasks due, the next last.
  final _tasks = <void Function()>[];

  /// The values of the terms lowered, the latest last.
  final _vals = <_Val>[];

  /// The edges of the terms lowered as values, the latest last.
  final _srcs = <Src>[];

  /// The regions built, the latest last.
  final _built = <_Frame>[];

  _Lower(Term t) {
    final todo = [t];
    while (todo.isNotEmpty) {
      final s = todo.removeLast();
      if (s case Var(:final name)) _uses[name] = (_uses[name] ?? 0) + 1;
      todo.addAll(_subterms(s));
    }
  }

  Region run(Term t) {
    _frames.add(_Frame(RegionKind.function, []));
    _value(t);
    while (_tasks.isNotEmpty) {
      _tasks.removeLast()();
    }
    final f = _frames.single;
    final results = [
      _srcs.single,
      for (final a in f.region.args)
        if (a case StateEdge(:final port)) f.states[port]!,
    ];
    final args = f.region.args;
    final root = Region(
      args.any((a) => a.isState) ? RegionKind.port : RegionKind.function,
      args,
      f.region.nodes,
      results,
    );
    try {
      validate(root);
    } on ZirError catch (e) {
      throw ZirError('the lowered graph is invalid: $e');
    }
    return root;
  }

  /// Runs `steps` in order, before the tasks already due.
  void _then(List<void Function()> steps) {
    for (var i = steps.length - 1; i >= 0; i--) {
      _tasks.add(steps[i]);
    }
  }

  int get _top => _frames.length - 1;

  _Frame get _frame => _frames.last;

  String _freshName() => '\u0000lower${++_fresh}';

  _Val _lookup(String x) =>
      _scope[x] ??
      (throw ZirError(
        '`$x` is not bound, and a term lowers only when every name it reads is bound in it or '
        'is a prelude word',
      ));

  /// The last `k` edges lowered, in order.
  List<Src> _pop(int k) {
    final out = _srcs.sublist(_srcs.length - k);
    _srcs.length -= k;
    return out;
  }

  /// The last `k` values lowered, in order.
  List<_Val> _popVals(int k) {
    final out = _vals.sublist(_vals.length - k);
    _vals.length -= k;
    return out;
  }

  /// `v` as an edge of the current region.
  Src _src(_Val v) => switch (v) {
    _Edge(:final src, :final depth) => _bring(src, depth),
    _Prim(:final prim) => _primFn(prim),
    _Closure(:final params, :final ports) => throw ZirError(
      'a function of ${_plural(params.length, 'parameter')} that uses the ports '
      '${ports.map((p) => '`$p`').join(', ')} is used as a value: a call threads the states of '
      "those ports, and only a call by the function's name knows them, so such a function is "
      'only called',
    ),
  };

  /// The edge `s` of the region at depth `at`, captured into each region down to the top.
  Src _bring(Src s, int at) {
    if (s is Const) return s;
    for (var k = at + 1; k < _frames.length; k++) {
      s = _capture(k, s);
    }
    return s;
  }

  /// The argument of frame `k` that receives `s`, an edge of frame `k - 1`. A name read twice
  /// is captured twice; [_node] merges the repeats.
  Src _capture(int k, Src s) {
    final edge = _frames[k - 1].region.edge(s);
    final f = _frames[k];
    f.captures.add(s);
    f.region.args.add(edge);
    return Arg(f.region.args.length - 1);
  }

  /// The current state edge of port `p` in frame `k`, taken from the enclosing regions.
  Src _state(int k, String p) {
    // The innermost frame from `k` out that has the state, or the root.
    var j = k;
    while (j > 0 && !_frames[j].states.containsKey(p)) {
      final kind = _frames[j].region.kind;
      if (kind != RegionKind.match && kind != RegionKind.port) {
        throw ZirError(
          'port `$p` is used inside a ${kind.name} region, and a state edge enters only a match '
          'or port region or the region of a `let`-bound lambda (step L1.31): a port is read or '
          'pushed outside loops and families, and a function that uses one is bound by `let` '
          'and called by its name',
        );
      }
      j--;
    }
    var s = _frames[j].states[p];
    if (s == null) {
      final root = _frames[0];
      root.region.args.add(StateEdge(p));
      s = root.states[p] = Arg(root.region.args.length - 1);
    }
    for (var i = j + 1; i <= k; i++) {
      final f = _frames[i];
      f.captures.add(s!);
      f.region.args.add(StateEdge(p));
      s = f.states[p] = Arg(f.region.args.length - 1);
    }
    return s!;
  }

  /// Adds `node`, whose regions have the keys `regions`, unless a node of its key is there. A
  /// node that takes a state edge never repeats one, since each state edge is used once, so
  /// the effects stay apart without a test of their own.
  int _add(Node node, List<ContentAddress> regions) {
    final key = nodeKey(node, regions);
    final f = _frame;
    if (f.seen[key] case final n?) return n;
    f.region.nodes.add(node);
    f.keys.add(regions);
    return f.seen[key] = f.region.nodes.length - 1;
  }

  /// A one-output node with no region.
  _Val _leaf(Op op, List<Src> inputs) =>
      _Edge(Out(_add(Node(op, inputs, [_anything()]), const []), 0), _top);

  /// Lowers `t` as a value, its edge going on [_srcs].
  void _value(Term t) => _then([() => _term(t), () => _srcs.add(_src(_vals.removeLast()))]);

  /// The steps that lower each of `ts` as a value.
  List<void Function()> _values(List<Term> ts) => [for (final t in ts) () => _value(t)];

  /// Builds a region of `kind` whose arguments are `params` and then the states of `ports`,
  /// which it returns after the value of `body`; it goes on [_built].
  void _region(RegionKind kind, List<String> params, Term body, [List<String> ports = const []]) {
    final frame = _Frame(kind, [
      for (final _ in params) _anything(),
      for (final p in ports) StateEdge(p),
    ]);
    for (var j = 0; j < ports.length; j++) {
      frame.states[ports[j]] = Arg(params.length + j);
    }
    _frames.add(frame);
    final mark = _scope;
    for (var i = 0; i < params.length; i++) {
      _scope = _scope.put(params[i], _Edge(Arg(i), _top));
    }
    _then([
      () => _value(body),
      () {
        _scope = mark;
        final f = _frames.removeLast();
        f.region.results.add(_srcs.removeLast());
        for (final p in ports) {
          f.region.results.add(f.states[p]!);
        }
        _built.add(f);
      },
    ]);
  }

  /// The last `k` regions built, in order.
  List<_Frame> _popBuilt(int k) {
    final out = _built.sublist(_built.length - k);
    _built.length -= k;
    return out;
  }

  /// The node `op` with inputs `fixed` and regions `built`, their captures merged.
  _Edge _node(Op op, List<Src> fixed, List<_Frame> built) {
    // The union of the regions' captures, in order, with the position of each.
    final caps = <Src>[];
    final at = <(int, int), int>{};
    for (final b in built) {
      for (final c in b.captures) {
        at.putIfAbsent(_captured(c), () {
          caps.add(c);
          return caps.length - 1;
        });
      }
    }
    final parent = _frame.region;
    final edges = [for (final c in caps) parent.edge(c)];
    final ports = [
      for (var i = 0; i < edges.length; i++)
        if (edges[i] case StateEdge(:final port)) (i, port),
    ];
    final regions = <Region>[];
    final keys = <ContentAddress>[];
    for (final b in built) {
      final map = [
        for (var i = 0; i < b.fixed; i++) i,
        for (final c in b.captures) b.fixed + at[_captured(c)]!,
      ];
      final r = b.region;
      _renumber(r, map);
      r.args
        ..length = b.fixed
        ..addAll(edges);
      for (final (i, p) in ports) {
        // The node that last used the port, or the argument when the region does not touch it.
        r.results.add(b.states[p] ?? Arg(b.fixed + i));
      }
      keys.add(regionKey(r, b.keys));
      regions.add(r);
    }
    final outputs = [_anything(), for (final (_, p) in ports) StateEdge(p)];
    final n = _add(Node(op, [...fixed, ...caps], outputs, regions), keys);
    for (var j = 0; j < ports.length; j++) {
      _frame.states[ports[j].$2] = Out(n, 1 + j);
    }
    return _Edge(Out(n, 0), _top);
  }

  /// A prelude word as a function value: a `prim` node with no inputs.
  Src _primFn(Prim p) {
    if (p.arity == null) {
      throw ZirError(
        'the primitive `${text.spell(p)}` takes any number of arguments, so with no inputs its '
        'node is a call, not the function; call it instead of passing it as a value',
      );
    }
    return (_leaf(PrimOp(p), []) as _Edge).src;
  }

  /// The ports `b`, a lambda body, reads or pushes, itself or by calling a function free in it
  /// that does, in the order of their first use in the text.
  List<String> _ports(Term b) {
    final out = <String>[];
    final seen = <String>{};
    for (final u in _bodyUses(b)) {
      if (u.port) {
        if (seen.add(u.name)) out.add(u.name);
      } else if (_scope[u.name] case _Closure(:final ports)) {
        for (final p in ports) {
          if (seen.add(p)) out.add(p);
        }
      }
    }
    return out;
  }

  /// The uses of the lambda body `b`, in the order of their first occurrence: a lambda inside
  /// `b` adds the uses of its own body, less the names bound around it in `b`. Each body is
  /// read once, after the bodies inside it.
  List<_Use> _bodyUses(Term b) {
    if (_bodies[b] case final u?) return u;
    // A walk over the subterms, with a mark after each new body that reads it once the bodies
    // inside it are read.
    final found = Set<Term>.identity()..add(b);
    final todo = <Object>[_Read(b), b];
    while (todo.isNotEmpty) {
      switch (todo.removeLast()) {
        case _Read(:final body):
          _bodies[body] = _readBody(body);
        case Lam(:final body):
          if (!_bodies.containsKey(body) && found.add(body)) todo.addAll([_Read(body), body]);
        case final Term t:
          todo.addAll(_subterms(t));
      }
    }
    return _bodies[b]!;
  }

  /// The uses of the lambda body `b`, the bodies of the lambdas inside it already read.
  List<_Use> _readBody(Term b) {
    final bound = <String, int>{};
    final seen = <_Use>{};
    final out = <_Use>[];
    void add(_Use u) {
      if (!u.port && bound.containsKey(u.name)) return;
      if (seen.add(u)) out.add(u);
    }

    void bind(List<String> xs) {
      for (final x in xs) {
        bound[x] = (bound[x] ?? 0) + 1;
      }
    }

    void unbind(List<String> xs) {
      for (final x in xs) {
        if ((bound[x] = bound[x]! - 1) == 0) bound.remove(x);
      }
    }

    // Terms to read, and the names to bind or unbind around them, the next last.
    final todo = <Object>[b];
    void then(List<Object> items) => todo.addAll(items.reversed);
    List<Object> under(List<String> xs, Term t) => [_Bind(xs), t, _Unbind(xs)];
    while (todo.isNotEmpty) {
      switch (todo.removeLast()) {
        case _Bind(:final names):
          bind(names);
        case _Unbind(:final names):
          unbind(names);
        case Lit() || PrimFn():
          break;
        case Var(:final name):
          add((port: false, name: name));
        case Read(:final port):
          add((port: true, name: port));
        case Push(:final port, :final value):
          add((port: true, name: port));
          todo.add(value);
        case Lam(:final params, :final body):
          bind(params);
          _bodies[body]!.forEach(add);
          unbind(params);
        case Let(:final name, :final value, :final body):
          then([
            value,
            ...under([name], body),
          ]);
        case Match(:final scrutinee, :final arms):
          then([scrutinee, for (final (p, a) in arms) ...under(_names(p), a)]);
        case Fam(:final domain, :final variable, :final body):
          then([
            domain,
            ...under([variable], body),
          ]);
        case Fix(:final init, :final step, :final self, :final key, :final kind):
          then([
            init,
            ...switch (kind) {
              Lattice(:final join) => [step, join],
              Definedness() => under([self, key], step),
            },
          ]);
        case final Term t:
          then(_subterms(t));
      }
    }
    return out;
  }

  void _term(Term t) {
    final at = _top;
    switch (t) {
      case Lit(:final value):
        _vals.add(_Edge(Const(value), at));
      case Var(:final name):
        _vals.add(_lookup(name));
      case PrimFn(:final prim):
        _vals.add(_Prim(prim));
      case Let(:final name, :final value, :final body):
        final ports = value is Lam ? _ports(value.body) : const <String>[];
        final steps = <void Function()>[];
        if (value case Lam(:final params, body: final b) when ports.isNotEmpty) {
          if ((_uses[name] ?? 0) <= 1) {
            _vals.add(_Closure(params, ports, _Inline(b, _scope)));
          } else {
            steps.addAll([
              () => _region(RegionKind.function, params, b, ports),
              () {
                final fun = _node(const LambdaOp(), [], _popBuilt(1));
                _vals.add(_Closure(params, ports, _Applied(fun.src, fun.depth)));
              },
            ]);
          }
        } else {
          steps.add(() => _term(value));
        }
        steps.add(() {
          final v = _vals.removeLast();
          if (v case _Edge(src: Out(:final node, :final port), :final depth) when depth == at) {
            final outputs = _frame.region.nodes[node].outputs;
            if (outputs[port] case ValueEdge(:final type, :final domain, :final facets)
                when !facets.any((f) => f.hint && f.kind == 'name')) {
              outputs[port] = ValueEdge(
                type,
                domain: domain,
                facets: [...facets, Facet('name', Str(name), hint: true)],
              );
            }
          }
          _bound([name], [v], body);
        });
        _then(steps);
      case Lam(:final params, :final body):
        _then([
          () => _region(RegionKind.function, params, body),
          () => _vals.add(_node(const LambdaOp(), [], _popBuilt(1))),
        ]);
      case App(:final f, :final args):
        if (f case Lam(:final params, :final body) when params.length == args.length) {
          _then([
            for (final a in args) () => _term(a),
            () => _bound(params, _popVals(args.length), body),
          ]);
        } else {
          _then([() => _term(f), () => _call(_vals.removeLast(), args, at)]);
        }
      case PrimApp(:final prim, :final args):
        if (prim.arity case final k? when k != args.length) {
          throw ZirError(
            'the primitive `${text.spell(prim)}` takes ${_plural(k, 'argument')} and is given '
            '${args.length}',
          );
        }
        _then([..._values(args), () => _vals.add(_leaf(PrimOp(prim), _pop(args.length)))]);
      case If(:final cond, :final then, :final orElse):
        _then([
          () => _value(cond),
          () => _region(RegionKind.match, [], then),
          () => _region(RegionKind.match, [], orElse),
          () => _vals.add(_node(const IfOp(), _pop(1), _popBuilt(2))),
        ]);
      case Match(:final scrutinee, :final arms):
        _then([
          () => _value(scrutinee),
          for (final (p, body) in arms) () => _region(RegionKind.match, _names(p), body),
          () => _vals.add(
            _node(MatchOp([for (final (p, _) in arms) p]), _pop(1), _popBuilt(arms.length)),
          ),
        ]);
      case Fam(:final domain, :final variable, :final body):
        _then([
          () => _value(domain),
          () => _region(RegionKind.function, [variable], body),
          () => _vals.add(_node(const FamOp(), _pop(1), _popBuilt(1))),
        ]);
      case Reindex(:final family, :final kf, :final vf, :final witness):
        _then([
          ..._values([family, kf, vf]),
          () => _vals.add(_leaf(ReindexOp(witness), _pop(3))),
        ]);
      case Discard(:final family, :final sel):
        _then([
          ..._values([family, sel]),
          () => _vals.add(_leaf(const DiscardOp(), _pop(2))),
        ]);
      case Fold(:final family, :final op, :final identity, :final depth, :final ev):
        final ins = [family, op, ?identity];
        _then([
          ..._values(ins),
          () => _vals.add(_leaf(FoldOp(depth, identity != null, ev), _pop(ins.length))),
        ]);
      case Fix(:final init, :final step, kind: Lattice(:final join), :final ev):
        _then([
          ..._values([init, join]),
          () {
            final x = _freshName();
            _region(RegionKind.loop, [x], App(step, [Var(x)]));
          },
          () => _vals.add(_node(FixOp(true, ev), _pop(2), _popBuilt(1))),
        ]);
      case Fix(:final init, :final step, :final self, :final key, kind: Definedness(), :final ev):
        _then([
          () => _value(init),
          () => _region(RegionKind.loop, [self, key], step),
          () => _vals.add(_node(FixOp(false, ev), _pop(1), _popBuilt(1))),
        ]);
      case Gen(:final init, :final step, :final guard, :final pos):
        _then([
          () => _value(init),
          for (final f in [step, guard])
            () {
              final x = _freshName();
              _region(RegionKind.loop, [x], App(f, [Var(x)]));
            },
          () => _vals.add(_node(GenOp(pos), _pop(1), _popBuilt(2))),
        ]);
      case Read(:final port):
        final s = _state(at, port);
        final n = _add(Node(ReadOp(port), [s], [_anything(), StateEdge(port)]), const []);
        _frame.states[port] = Out(n, 1);
        _vals.add(_Edge(Out(n, 0), at));
      case Push(:final port, :final value):
        _then([
          () => _value(value),
          () {
            final v = _srcs.removeLast();
            final s = _state(at, port);
            final n = _add(Node(PushOp(port), [s, v], [_anything(), StateEdge(port)]), const []);
            _frame.states[port] = Out(n, 1);
            _vals.add(_Edge(Out(n, 0), at));
          },
        ]);
    }
  }

  /// The call of `fv`, a function lowered in the region at depth `at`, with `args`.
  void _call(_Val fv, List<Term> args, int at) {
    switch (fv) {
      case _Prim(:final prim) when prim.arity == null || prim.arity == args.length:
        _then([..._values(args), () => _vals.add(_leaf(PrimOp(prim), _pop(args.length)))]);
      case _Closure(:final params, :final ports, :final call):
        if (params.length != args.length) {
          throw ZirError(
            'a function of ${_plural(params.length, 'parameter')} that uses a port is called '
            'with ${_plural(args.length, 'argument')}',
          );
        }
        switch (call) {
          case _Inline(:final body, :final env):
            _then([
              for (final a in args) () => _term(a),
              () {
                final vals = _popVals(args.length);
                final saved = _scope;
                _then([() => _scope = saved]);
                _scope = env;
                _bound(params, vals, body);
              },
            ]);
          case _Applied(:final fun, at: final atFun):
            final f = _bring(fun, atFun);
            _then([
              ..._values(args),
              () {
                final ins = [f, ..._pop(args.length)];
                final outputs = <Edge>[_anything()];
                for (final p in ports) {
                  ins.add(_state(at, p));
                  outputs.add(StateEdge(p));
                }
                final n = _add(Node(const ApplyOp(), ins, outputs), const []);
                for (var j = 0; j < ports.length; j++) {
                  _frame.states[ports[j]] = Out(n, 1 + j);
                }
                _vals.add(_Edge(Out(n, 0), at));
              },
            ]);
        }
      default:
        final f = _src(fv);
        _then([
          ..._values(args),
          () => _vals.add(_leaf(const ApplyOp(), [f, ..._pop(args.length)])),
        ]);
    }
  }

  /// Lowers `body` with `params` bound to `vals`, in the current region.
  void _bound(List<String> params, List<_Val> vals, Term body) {
    final mark = _scope;
    for (var i = 0; i < params.length; i++) {
      _scope = _scope.put(params[i], vals[i]);
    }
    _then([() => _term(body), () => _scope = mark]);
  }
}

/// A mark in [_Lower._bodyUses]: the bodies inside `body` are read.
final class _Read {
  final Term body;

  _Read(this.body);
}

/// A mark in [_Lower._readBody]: `names` are bound from here.
final class _Bind {
  final List<String> names;

  _Bind(this.names);
}

/// A mark in [_Lower._readBody]: `names` are bound no longer.
final class _Unbind {
  final List<String> names;

  _Unbind(this.names);
}

/// The key of a captured edge: a constant is never captured.
(int, int) _captured(Src s) => switch (s) {
  Arg(:final i) => (-1, i),
  Out(:final node, :final port) => (node, port),
  Const() => throw StateError('a constant is never captured'),
};

/// An edge of type `_` with no facts.
Edge _anything() => Edge.value(Type.top);

String _plural(int n, String thing) => n == 1 ? '1 $thing' : '$n ${thing}s';

/// The names pattern `p` binds, in preorder.
List<String> _names(Pattern p) => switch (p) {
  BindP(:final name) => [name],
  AtomP(args: final ps) || TupleP(items: final ps) => [for (final q in ps) ..._names(q)],
  FieldsP(:final fields) => [for (final (_, q) in fields) ..._names(q)],
  WildP() || LitP() || AnyAtomP() || IsP() => const [],
};

/// The direct subterms of `t`, in order, the bodies under binders included.
List<Term> _subterms(Term t) => switch (t) {
  Lit() || Var() || PrimFn() || Read() => const [],
  Lam(:final body) => [body],
  App(:final f, :final args) => [f, ...args],
  PrimApp(:final args) => args,
  Let(:final value, :final body) => [value, body],
  If(:final cond, :final then, :final orElse) => [cond, then, orElse],
  Match(:final scrutinee, :final arms) => [scrutinee, for (final (_, a) in arms) a],
  Fam(:final domain, :final body) => [domain, body],
  Reindex(:final family, :final kf, :final vf) => [family, kf, vf],
  Discard(:final family, :final sel) => [family, sel],
  Fold(:final family, :final op, :final identity) => [family, op, ?identity],
  Fix(:final init, :final step, :final kind) => [
    init,
    step,
    if (kind case Lattice(:final join)) join,
  ],
  Gen(:final init, :final step, :final guard) => [init, step, guard],
  Push(:final value) => [value],
};

/// Maps the argument indices `r`'s own nodes and results read; inner regions are isolated.
void _renumber(Region r, List<int> map) {
  Src renumbered(Src s) => s is Arg ? Arg(map[s.i]) : s;
  for (final n in r.nodes) {
    for (var i = 0; i < n.inputs.length; i++) {
      n.inputs[i] = renumbered(n.inputs[i]);
    }
  }
  for (var i = 0; i < r.results.length; i++) {
    r.results[i] = renumbered(r.results[i]);
  }
}

/// The kernel term graph `g` computes: each node a `let`, in the region's order, and each region
/// the body of a lambda, a family, a loop or a match arm. A read or a push is the kernel's
/// `Read` or `Push`; a state edge carries no value, so it becomes `()`, and the order of the
/// `let`s, which is the order of the nodes, keeps the order of the effects. Throws a
/// [ZirError] for a graph no term lowers to.
Term raise(Region g) {
  if (g.results.isEmpty || g.results.length != 1 + g.args.length) {
    throw ZirError(
      'the root region has ${_plural(g.args.length, 'argument')} and '
      "${_plural(g.results.length, 'result')}, and a term's root has one value and a state "
      'result for each state argument',
    );
  }
  return _Raise().region(g, [for (final _ in g.args) _unit], 'r');
}

/// The term region `r` computes, its arguments being `args`: [raise] for a region that is not
/// a root, such as a function's body with its captured values (step L1.34).
Term raiseWith(Region r, List<Term> args) => _Raise().region(r, args, 'r');

const _unit = Lit(Tuple([]));

final class _Raise {
  var _fresh = 0;

  String _name() => '\u0000raise${++_fresh}';

  Term region(Region r, List<Term> args, String path) {
    final outs = <String>[];
    Term termOf(Src s) => switch (s) {
      Arg(:final i) => args[i],
      Out(:final node, :final port) when r.nodes[node].outputs[port].isState => _unit,
      Out(:final node) => Var(outs[node]),
      Const(:final value) => Lit(value),
    };
    final lets = <(String, Term)>[];
    for (var k = 0; k < r.nodes.length; k++) {
      final node = r.nodes[k];
      final at = '$path.$k';
      final ins = [for (final s in node.inputs) termOf(s)];
      Term sub(int i, List<Term> fixed, int from) =>
          region(node.regions[i], [...fixed, ...ins.skip(from)], '$at/$i');
      final t = switch (node.op) {
        PrimOp(:final prim) when ins.isEmpty && prim.arity != null => PrimFn(prim),
        PrimOp(:final prim) => PrimApp(prim, ins),
        // A state edge has no term: the kernel orders effects by evaluation. The states are the
        // last inputs, one for each output after the value.
        ApplyOp() => App(ins[0], ins.sublist(1, ins.length + 1 - node.outputs.length)),
        LambdaOp() => () {
          final args = node.regions[0].args;
          final ps = <String>[];
          final vars = [
            for (final e in args.take(args.length - ins.length))
              if (e.isState) _unit else Var(_param(ps)),
          ];
          return Lam(ps, sub(0, vars, 0));
        }(),
        IfOp() => If(ins[0], sub(0, [], 1), sub(1, [], 1)),
        MatchOp(:final patterns) => Match(ins[0], [
          for (var i = 0; i < patterns.length; i++)
            () {
              final xs = <Term>[];
              final p = _rename(patterns[i], () {
                final x = _name();
                xs.add(Var(x));
                return x;
              });
              return (p, sub(i, xs, 1));
            }(),
        ]),
        FamOp() => () {
          final x = _name();
          return Fam(ins[0], x, sub(0, [Var(x)], 1));
        }(),
        ReindexOp(:final witness) => Reindex(ins[0], ins[1], ins[2], witness),
        DiscardOp() => Discard(ins[0], ins[1]),
        FoldOp(:final depth, :final identity, :final ev) => Fold(
          ins[0],
          ins[1],
          identity ? ins[2] : null,
          depth,
          ev,
        ),
        FixOp(lattice: true, :final ev) => () {
          final x = _name();
          return Fix(ins[0], Lam([x], sub(0, [Var(x)], 2)), '', '', Lattice(ins[1]), ev);
        }(),
        FixOp(lattice: false, :final ev) => () {
          final self = _name(), key = _name();
          return Fix(ins[0], sub(0, [Var(self), Var(key)], 1), self, key, const Definedness(), ev);
        }(),
        GenOp(:final pos) => () {
          final [step, guard] = [
            for (var i = 0; i < 2; i++)
              () {
                final x = _name();
                return Lam([x], sub(i, [Var(x)], 1));
              }(),
          ];
          return Gen(ins[0], step, guard, pos);
        }(),
        ReadOp(:final port) => Read(port),
        PushOp(:final port) => Push(port, ins[1]),
        DerivedOp() || RecOp() || WaveOp() => throw ZirError(
          '$at: `${node.op.name}` has no kernel term here; the lowering does not make it',
        ),
      };
      final x = _name();
      lets.add((x, t));
      outs.add(x);
    }
    var body = termOf(r.results[0]);
    for (final (x, e) in lets.reversed) {
      body = Let(x, e, body);
    }
    return body;
  }

  /// A fresh parameter, added to `ps`.
  String _param(List<String> ps) {
    final p = _name();
    ps.add(p);
    return p;
  }
}

/// `p` with each binder renamed, in preorder, to what `f` gives.
Pattern _rename(Pattern p, String Function() f) => switch (p) {
  BindP() => BindP(f()),
  AtomP(:final name, :final args) => AtomP(name, [for (final q in args) _rename(q, f)]),
  FieldsP(:final name, :final fields) => FieldsP(name, [
    for (final (k, q) in fields) (k, _rename(q, f)),
  ]),
  TupleP(:final items) => TupleP([for (final q in items) _rename(q, f)]),
  WildP() || LitP() || AnyAtomP() || IsP() => p,
};
