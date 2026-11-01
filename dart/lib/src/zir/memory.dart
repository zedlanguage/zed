/// Memory (step L1.34): static last-use drops, borrow inference and dup/drop fusion over ZIR,
/// giving precise reference counts for scalars, strings, tuples and closures, and a machine
/// that runs a graph under the plan and checks every count.
///
/// **The plan.** [plan] decides, for each region the machine runs (the root, a lambda's body,
/// an arm of an `if` or a `match`), how each value edge is held and where its counts change.
/// An edge is *owned*, holding one reference, or *borrowed*, read under a reference someone
/// else holds. A node's output is owned. A lambda's parameter is owned when some use consumes
/// it, and borrowed otherwise (borrow inference); its captures are borrowed, since the closure
/// holds them. Each use of an edge takes it *owned*, consuming a reference, or *borrowed*:
///
/// - a tuple and an atom's payload take their parts owned, a lambda its captures, a push its
///   value, and a result is owned; an `apply` passes each argument as the callee's parameter
///   takes it when the callee is a lambda the plan can see (in the same region, or through
///   captures to an enclosing one), and owned otherwise;
/// - an `if` or a `match` passes a capture owned when it is the edge's last use, the edge is
///   owned and some arm consumes it, and a `match` takes its scrutinee owned on the same
///   terms, an arm consuming a binder; otherwise they are borrowed;
/// - every other use, a primitive's operand, a called function, and each input of a family
///   node, is borrowed.
///
/// An owned edge gets a dup before each owned use but its last, and a drop after its last use
/// when that use borrows; an owned edge with no use is dropped where it appears. A borrowed
/// edge gets a dup before each owned use and is never dropped. So each reference is dropped at
/// its last use (static last-use drops), and a value used once is never counted.
///
/// **Fusion.** A `match` that owns its scrutinee hands the arm the binders it uses, owned. With
/// fusion ([Plan.fuse]), the arm's entry releases the scrutinee keeping those binders: if the
/// scrutinee's count is 1 its cell is freed without a count write and the binders' references
/// move out of it, the other parts dropped; otherwise each kept binder gets a dup and the
/// scrutinee one decrement. Without fusion, each kept binder gets a dup and the scrutinee a
/// drop. Destructuring a fresh pair of strings and keeping one costs one count write fused,
/// and four unfused.
///
/// **The heap.** A string, a big integer, a rational, a keypath and a family are each one
/// cell; a non-empty tuple and an atom with a payload are a cell whose children are their
/// parts' cells; a closure is a cell whose children are its captures. An integer, a float, a
/// boolean, the empty tuple and a bare atom are unboxed, and a constant is static: neither is
/// ever counted. A family's own entries are kernel data, held whole (step L3.17 manages them),
/// and the loop and family regions run in the kernel, which borrows their inputs.
///
/// **The machine.** [run] runs the graph, each node under its plan. The value of each scalar,
/// family or port node comes from the kernel, which runs the node alone, raised with its
/// inputs as literals; a tuple, a closure, a call, a branch and a match run in the machine,
/// which therefore keeps the sharing the program makes. After each node, the machine checks
/// that each live cell's count is the number of references to it: from owned edges still to
/// be used, in every frame, and from live cells. So a missed drop, an extra drop, a use after
/// free and a value kept past its last use are each an error, and at the end only the result
/// is live.
library;

import '../kernel/error.dart';
import '../kernel/eval.dart';
import '../kernel/term.dart';
import '../kernel/text.dart' show compareUtf8;
import '../kernel/value.dart';
import 'graph.dart';
import 'lower.dart' show raiseWith;

/// How an edge is held, or how a use takes it.
enum Mode {
  /// Holding, or consuming, one reference.
  owned,

  /// Read under a reference held elsewhere.
  borrowed,
}

/// The plan of one node.
final class NodePlan {
  /// How each input is taken; a state input is borrowed.
  final List<Mode> modes;

  /// The inputs that get a dup before the node.
  final List<int> dups = [];

  /// The edges dropped after the node.
  final List<Src> drops = [];

  /// The edges whose last use is the node.
  final List<Src> last = [];

  /// The body of the lambda an `apply` calls, when the plan sees it.
  final RegionPlan? callee;

  /// The plans of the node's regions the machine runs: a lambda's body, or each arm.
  final List<RegionPlan> regions = [];

  NodePlan(this.modes, this.callee);
}

/// The plan of one region: node [node]'s region [index] in [parent], or the root.
final class RegionPlan {
  final RegionPlan? parent;
  final int node, index;

  /// How each argument is held.
  final List<Mode> args = [];

  /// The arguments dropped on entry, having no use.
  final List<int> entryDrops = [];

  /// The nodes' plans.
  final List<NodePlan> nodes = [];

  /// The results that get a dup.
  final List<int> resultDups = [];

  final _Uses _uses;

  RegionPlan._(this.parent, this.node, this.index, this._uses);

  /// The region's path: `r` for the root, then `r.3/0` for node 3's first region.
  late final String path = parent == null ? 'r' : '${parent!.path}.$node/$index';
}

/// A memory plan: the root region's plan, holding the plans of the regions inside it, and
/// whether `match` fuses its release.
final class Plan {
  final RegionPlan root;

  /// Whether a `match` that owns its scrutinee releases it fused with its binders' dups.
  final bool fuse;

  const Plan._(this.root, this.fuse);

  /// The plan of the region at [path], such as `r.3/0`.
  RegionPlan at(String path) {
    final steps = path.split('.');
    if (steps.first != 'r') throw ArgumentError('not a region path: $path');
    var rp = root;
    for (final step in steps.skip(1)) {
      final [k, i] = step.split('/').map(int.parse).toList();
      rp = rp.nodes[k].regions[i];
    }
    return rp;
  }
}

/// The counts of one run.
final class Stats {
  /// Count increments.
  var increments = 0;

  /// Count decrements.
  var decrements = 0;

  /// Cells allocated.
  var allocations = 0;

  /// Cells freed.
  var frees = 0;

  /// The most cells live at once.
  var peak = 0;

  /// The cells whose count ever exceeded 1.
  var shared = 0;

  /// The count writes: increments and decrements.
  int get writes => increments + decrements;
}

/// The memory plan of graph [g].
Plan plan(Region g, bool fuse) {
  final root = _Ctx(g, null, null, 0, 0);
  _Planner().regions(root, List.filled(g.args.length, Mode.borrowed));
  return Plan._(root.plan, fuse);
}

/// Where an edge is used: input [j] of node [k], or result [j] when [k] is -1.
typedef _At = (int k, int j);

/// The edges of a region, its arguments and then its nodes' outputs, each with its uses.
final class _Uses {
  final List<int> base = [];
  final List<bool> state;
  final List<List<_At>> uses;

  _Uses._(this.state) : uses = [for (final _ in state) []];

  factory _Uses(Region r) {
    final state = [for (final e in r.args) e.isState];
    final base = <int>[];
    for (final n in r.nodes) {
      base.add(state.length);
      state.addAll(n.outputs.map((e) => e.isState));
    }
    final u = _Uses._(state)..base.addAll(base);
    for (var k = 0; k < r.nodes.length; k++) {
      final ins = r.nodes[k].inputs;
      for (var j = 0; j < ins.length; j++) {
        if (u.slot(ins[j]) case final e?) u.uses[e].add((k, j));
      }
    }
    for (var i = 0; i < r.results.length; i++) {
      if (u.slot(r.results[i]) case final e?) u.uses[e].add((-1, i));
    }
    return u;
  }

  int? slot(Src s) => switch (s) {
    Arg(:final i) => i,
    Out(:final node, :final port) => base[node] + port,
    Const() => null,
  };

  /// The node holding edge [e]'s last use, when that use is not a result.
  int? last(int e) => switch (uses[e]) {
    [..., (final k, _)] when k >= 0 => k,
    _ => null,
  };

  /// The source of edge [e]: the last node whose outputs start at or before it, found by
  /// binary search, since [base] never decreases.
  Src src(int e, int args) {
    if (e < args) return Arg(e);
    var (lo, hi) = (0, base.length);
    while (lo < hi) {
      final mid = (lo + hi) >> 1;
      if (base[mid] <= e) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return Out(lo - 1, e - base[lo - 1]);
  }
}

/// A region the planner sees, with the way to its enclosing one: argument [firstArg] on is
/// the input [firstInput] on of [node] in [up]. Each is made once, so its memos are shared by
/// every question asked of it.
final class _Ctx {
  final Region r;
  final _Ctx? up;
  final Node? node;
  final int firstArg, firstInput;
  final _Uses uses;
  late final RegionPlan plan;

  /// Each node's regions, made when first asked for.
  final Map<int, List<_Ctx>> _kids = {};

  /// Whether the region consumes each argument it owns.
  final Map<int, bool> consumed = {};

  /// How the region, a lambda's body, takes its parameters.
  List<Mode>? params;

  /// The lambda each argument is, when the plan can see it.
  final Map<int, (_Ctx, int)?> resolved = {};

  _Ctx(this.r, this.up, this.node, this.firstArg, this.firstInput, [int k = 0, int i = 0])
    : uses = _Uses(r) {
    plan = RegionPlan._(up?.plan, k, i, uses);
  }

  /// Region [i] of node [k]: a lambda's body, or an arm of an `if` or a `match`.
  _Ctx kid(int k, int i) => _kids.putIfAbsent(k, () {
    final n = r.nodes[k];
    return [
      for (var x = 0; x < n.regions.length; x++)
        switch (n.op) {
          LambdaOp() => _Ctx(
            n.regions[x],
            this,
            n,
            (n.regions[x].args.length - n.inputs.length).clamp(0, n.regions[x].args.length),
            0,
            k,
            x,
          ),
          MatchOp(:final patterns) => _Ctx(n.regions[x], this, n, binds(patterns[x]), 1, k, x),
          _ => _Ctx(n.regions[x], this, n, 0, 1, k, x),
        },
    ];
  })[i];
}

/// The lambda node [s] is in [ctx], as its region and index, when the plan can see it.
/// Each argument passed on the way is answered too, so no chain is followed twice.
(_Ctx, int)? _resolve(_Ctx ctx, Src s) {
  final passed = <(_Ctx, int)>[];
  (_Ctx, int)? found;
  var (c, src) = (ctx, s);
  while (true) {
    if (src case Out(:final node, port: 0) when c.r.nodes[node].op is LambdaOp) {
      found = (c, node);
    } else if (src case Arg(:final i)) {
      if (c.resolved.containsKey(i)) {
        found = c.resolved[i];
      } else {
        passed.add((c, i));
        final up = c.up;
        final x = i - c.firstArg;
        final ins = c.node?.inputs ?? const <Src>[];
        final at = c.firstInput + x;
        if (up != null && x >= 0 && at < ins.length) {
          (c, src) = (up, ins[at]);
          continue;
        }
      }
    }
    break;
  }
  for (final (c, i) in passed) {
    c.resolved[i] = found;
  }
  return found;
}

final class _Planner {
  /// How the use at input [j] of node [k] takes an edge that is [owned] or not, the node
  /// being its [last] use or not.
  Mode mode(_Ctx ctx, int k, int j, bool owned, bool last) {
    final node = ctx.r.nodes[k];
    Mode take(bool b) => b ? Mode.owned : Mode.borrowed;
    switch (node.op) {
      case PrimOp(prim: Prim.tuple) || LambdaOp():
        return Mode.owned;
      case PrimOp(prim: Prim.atom):
        return take(j >= 2);
      case PushOp():
        return take(j == 1);
      case ApplyOp() || IfOp() when j == 0:
        return Mode.borrowed;
      case ApplyOp():
        if (_resolve(ctx, node.inputs[0]) case (final c, final n)) {
          final ps = params(c, n);
          return j - 1 < ps.length ? ps[j - 1] : Mode.owned;
        }
        return Mode.owned;
      case IfOp() || MatchOp() when !(owned && last):
        return Mode.borrowed;
      case MatchOp(:final patterns) when j == 0:
        for (var i = 0; i < patterns.length; i++) {
          final arm = ctx.kid(k, i);
          for (var b = 0; b < arm.firstArg; b++) {
            if (arm.uses.uses[b].isNotEmpty && consumes(arm, b)) return Mode.owned;
          }
        }
        return Mode.borrowed;
      case IfOp():
        return take(consumes(ctx.kid(k, 0), j - 1) || consumes(ctx.kid(k, 1), j - 1));
      case MatchOp(:final patterns):
        for (var i = 0; i < patterns.length; i++) {
          final arm = ctx.kid(k, i);
          if (consumes(arm, arm.firstArg + j - 1)) return Mode.owned;
        }
        return Mode.borrowed;
      default:
        return Mode.borrowed;
    }
  }

  /// The questions [mode] asks to give the mode of the same use: whether an arm or a lambda's
  /// body consumes an argument.
  Iterable<(_Ctx, int)> needs(_Ctx ctx, int k, int j, bool owned, bool last) sync* {
    final node = ctx.r.nodes[k];
    switch (node.op) {
      case ApplyOp() when j > 0:
        if (_resolve(ctx, node.inputs[0]) case (final c, final n)) {
          final body = c.kid(n, 0);
          for (var i = 0; i < body.firstArg; i++) {
            if (!body.r.args[i].isState) yield (body, i);
          }
        }
      case IfOp() when j > 0 && owned && last:
        yield (ctx.kid(k, 0), j - 1);
        yield (ctx.kid(k, 1), j - 1);
      case MatchOp(:final patterns) when owned && last:
        for (var i = 0; i < patterns.length; i++) {
          final arm = ctx.kid(k, i);
          if (j > 0) {
            yield (arm, arm.firstArg + j - 1);
            continue;
          }
          for (var b = 0; b < arm.firstArg; b++) {
            if (arm.uses.uses[b].isNotEmpty) yield (arm, b);
          }
        }
      default:
    }
  }

  /// Whether region [ctx] consumes its argument [a] when it owns it. The questions this asks
  /// of the arms and lambdas below are answered first, on a stack, so a nest of any depth is
  /// planned; each is answered once.
  bool consumes(_Ctx ctx, int a) {
    if (ctx.consumed[a] case final c?) return c;
    final todo = [(ctx, a, false)];
    while (todo.isNotEmpty) {
      final (c, x, ready) = todo.removeLast();
      if (c.consumed.containsKey(x)) continue;
      if (ready) {
        c.consumed[x] = answer(c, x);
        continue;
      }
      todo.add((c, x, true));
      final u = c.uses;
      final last = u.last(x);
      for (final (k, j) in u.uses[x]) {
        if (k < 0) continue;
        for (final (d, y) in needs(c, k, j, true, last == k)) {
          if (!d.consumed.containsKey(y)) todo.add((d, y, false));
        }
      }
    }
    return ctx.consumed[a]!;
  }

  /// Whether region [ctx] consumes its argument [a], the questions it asks answered.
  bool answer(_Ctx ctx, int a) {
    final u = ctx.uses;
    final last = u.last(a);
    for (final (k, j) in u.uses[a]) {
      if (k < 0 || mode(ctx, k, j, true, last == k) == Mode.owned) return true;
    }
    return false;
  }

  /// How the lambda at node [n] of region [ctx] takes its parameters.
  List<Mode> params(_Ctx ctx, int n) {
    final body = ctx.kid(n, 0);
    return body.params ??= [
      // A state argument holds no value, so it is borrowed, as in an arm.
      for (var i = 0; i < body.firstArg; i++)
        !body.r.args[i].isState && consumes(body, i) ? Mode.owned : Mode.borrowed,
    ];
  }

  /// Plans region [root], its arguments held as [args], and the regions it holds, from a
  /// worklist.
  void regions(_Ctx root, List<Mode> args) {
    final todo = [(root, args)];
    while (todo.isNotEmpty) {
      final (ctx, a) = todo.removeLast();
      region(ctx, a, todo);
    }
  }

  /// Plans region [ctx], its arguments held as [args], and adds the regions it holds to
  /// [todo].
  void region(_Ctx ctx, List<Mode> args, List<(_Ctx, List<Mode>)> todo) {
    final r = ctx.r;
    final u = ctx.uses;
    final plan = ctx.plan..args.addAll(args);
    bool owned(int e) => !u.state[e] && (e >= args.length || args[e] == Mode.owned);
    final nodes = plan.nodes;
    for (var k = 0; k < r.nodes.length; k++) {
      final n = r.nodes[k];
      final modes = [
        for (var j = 0; j < n.inputs.length; j++)
          switch (u.slot(n.inputs[j])) {
            final e? when u.state[e] => Mode.borrowed,
            final e? => mode(ctx, k, j, owned(e), u.last(e) == k),
            null => mode(ctx, k, j, false, false),
          },
      ];
      final callee = n.op is ApplyOp && n.inputs.isNotEmpty
          ? switch (_resolve(ctx, n.inputs[0])) {
              (final c, final m) => c.kid(m, 0).plan,
              null => null,
            }
          : null;
      nodes.add(NodePlan(modes, callee));
    }
    for (var e = 0; e < u.state.length; e++) {
      final us = u.uses[e];
      if (u.last(e) case final k?) nodes[k].last.add(u.src(e, r.args.length));
      if (u.state[e]) continue;
      if (us.isEmpty) {
        if (owned(e)) {
          switch (u.src(e, r.args.length)) {
            case Arg(:final i):
              plan.entryDrops.add(i);
            case final Out s:
              nodes[s.node].drops.add(s);
            case Const():
              throw StateError('an edge is not a constant');
          }
        }
        continue;
      }
      // The use that takes over the edge's own reference, if any.
      _At? moved;
      if (owned(e)) {
        final end = us.last;
        final k = end.$1;
        if (k < 0) {
          moved = end;
        } else {
          // The uses at node k are the last ones, since uses are in node order.
          var borrows = false;
          for (var x = us.length - 1; x >= 0 && us[x].$1 == k; x--) {
            if (nodes[k].modes[us[x].$2] == Mode.borrowed) borrows = true;
          }
          if (borrows) {
            nodes[k].drops.add(u.src(e, r.args.length));
          } else {
            moved = end;
          }
        }
      }
      for (final at in us) {
        if (at == moved) continue;
        final (k, j) = at;
        if (k < 0) {
          plan.resultDups.add(j);
        } else if (nodes[k].modes[j] == Mode.owned) {
          nodes[k].dups.add(j);
        }
      }
    }
    for (var k = 0; k < r.nodes.length; k++) {
      final n = r.nodes[k];
      final m = nodes[k].modes;
      switch (n.op) {
        case LambdaOp():
          final body = ctx.kid(k, 0);
          final a = [...params(ctx, k)];
          while (a.length < body.r.args.length) {
            a.add(Mode.borrowed);
          }
          a.length = body.r.args.length;
          todo.add((body, a));
          nodes[k].regions.add(body.plan);
        case IfOp() || MatchOp():
          for (var i = 0; i < n.regions.length; i++) {
            final arm = ctx.kid(k, i);
            final a = [
              for (var x = 0; x < arm.firstArg; x++)
                m[0] == Mode.owned && arm.uses.uses[x].isNotEmpty ? Mode.owned : Mode.borrowed,
              ...m.skip(1),
            ];
            for (var x = 0; x < arm.r.args.length; x++) {
              if (arm.r.args[x].isState) a[x] = Mode.borrowed;
            }
            todo.add((arm, a));
            nodes[k].regions.add(arm.plan);
          }
        default:
      }
    }
  }
}

/// A value in the machine.
sealed class _Mv {
  const _Mv();

  int? get cell => null;
}

/// Data, with its cell unless it is unboxed or static.
final class _Data extends _Mv {
  final Value value;
  @override
  final int? cell;

  const _Data(this.value, this.cell);
}

/// A closure: its cell, its lambda node, the plan of its body and its captures.
final class _Clo extends _Mv {
  @override
  final int cell;
  final Node node;
  final RegionPlan body;
  final List<_Mv> caps;

  const _Clo(this.cell, this.node, this.body, this.caps);
}

/// A primitive as a function.
final class _PrimFn extends _Mv {
  final Prim prim;

  const _PrimFn(this.prim);
}

/// A lookup port.
final class _Source extends _Mv {
  final String port;

  const _Source(this.port);
}

/// A port's state.
final class _State extends _Mv {
  const _State();
}

/// An edge's value in a frame, and whether the frame owns a reference to it.
typedef _Slot = (_Mv, bool);

/// A heap cell: its count, 0 once freed, and its children's cells.
final class _Cell {
  var count = 1;
  List<int?> kids;
  var shared = false;

  _Cell(this.kids);
}

/// A region the machine is running: its next node, and what to do when the region that node
/// entered returns.
final class _Act {
  final Region r;
  final RegionPlan rp;
  var k = 0;
  void Function()? after;

  _Act(this.r, this.rp);
}

/// The lookup ports a kernel term reads, each once, in the order first met.
final class _Lets {
  final Set<String> seen = {};
  final List<String> order = [];
}

/// Runs graph [g] under [plan], the kernel running each scalar and family node in [ev], and
/// checks every count; returns the value and the counts. A count that does not check throws
/// a [ZirError]; the kernel's errors pass through.
(Value, Stats) run(Region g, Plan plan, Evaluator ev) {
  final m = _Machine(plan, ev);
  final out = m.regions(g, plan.root, [for (final _ in g.args) (const _State(), false)]);
  final v = out.first;
  m.pushFrame([(v, true)]);
  m.check(() => 'the end of the run');
  m.popFrame();
  m.dec(v.cell);
  if (m.live != 0) {
    throw ZirError('memory: ${_plural(m.live, 'cell')} live after the result is dropped');
  }
  return switch (v) {
    _Data(:final value) => (value, m.stats),
    _ => throw const KernelTypeError("the program's result is a function"),
  };
}

final class _Machine {
  final Plan plan;
  final Evaluator ev;
  final List<_Cell> heap = [];
  final List<List<_Slot?>> frames = [];

  /// For each cell, its references from owned slots and from the kids of live cells, and the
  /// slots that hold it, owned or not: kept as they change, so that a check need only look at
  /// the cells touched since the last one.
  final List<int> refs = [], holds = [];
  List<int> touched = [];
  final stats = Stats();
  var live = 0;
  final Map<Node, Region> _alone = Map.identity();

  /// The regions being run, innermost last: a node that enters a region does not wait for it
  /// on the call stack, so a nest of any depth runs.
  final List<_Act> acts = [];

  _Machine(this.plan, this.ev);

  /// Runs region [r] on [args] and every region it enters; returns its results.
  List<_Mv> regions(Region r, RegionPlan rp, List<_Slot> args) {
    enter(r, rp, args, null);
    while (true) {
      final a = acts.last;
      if (a.k < a.r.nodes.length) {
        if (begin(a) case final outs?) finish(a, outs);
        continue;
      }
      final outs = leave(a);
      acts.removeLast();
      if (acts.isEmpty) return outs;
      final up = acts.last;
      final after = up.after;
      up.after = null;
      after?.call();
      finish(up, outs);
    }
  }

  /// Enters region [r] on [args]; [after] runs when it returns, before the node that entered
  /// it finishes.
  void enter(Region r, RegionPlan rp, List<_Slot> args, void Function()? after) {
    for (var i = 0; i < args.length; i++) {
      final owned = args[i].$2;
      if (!r.args[i].isState && owned != (rp.args[i] == Mode.owned)) {
        throw ZirError(
          'memory: argument $i of `${rp.path}` arrives ${_held(owned)}, and the plan holds '
          'it ${_held(rp.args[i] == Mode.owned)}',
        );
      }
    }
    final u = rp._uses;
    final frame = List<_Slot?>.filled(u.state.length, null);
    frame.setRange(0, args.length, args);
    pushFrame(frame);
    for (final a in rp.entryDrops) {
      final (v, _) = take(u, Arg(a), () => rp.path, () => 'an entry drop');
      dec(v.cell);
    }
    check(() => 'the entry of `${rp.path}`');
    if (acts.isNotEmpty) acts.last.after = after;
    acts.add(_Act(r, rp));
  }

  /// Starts node `a.k`: reads its inputs, dups and takes them, and runs it; returns its
  /// outputs, or null when it entered a region.
  List<_Mv>? begin(_Act a) {
    final (rp, k, u) = (a.rp, a.k, a.rp._uses);
    final node = a.r.nodes[k];
    String at() => '${rp.path}.$k';
    final np = rp.nodes[k];
    final ins = [for (final s in node.inputs) read(u, s, at)];
    final dup = List.filled(node.inputs.length, false);
    for (final j in np.dups) {
      dup[j] = true;
      inc(ins[j].cell);
    }
    for (var j = 0; j < node.inputs.length; j++) {
      final s = node.inputs[j];
      if (np.modes[j] == Mode.owned && !dup[j] && u.slot(s) != null) {
        take(u, s, at, () => 'input $j, taken owned');
      }
    }
    return this.node(node, np, at, ins);
  }

  /// Finishes node `a.k` with its outputs [outs]: sets them, drops and ends its last uses,
  /// and checks the counts.
  void finish(_Act a, List<_Mv> outs) {
    final (rp, k, u) = (a.rp, a.k++, a.rp._uses);
    final node = a.r.nodes[k];
    String at() => '${rp.path}.$k';
    final np = rp.nodes[k];
    for (var p = 0; p < outs.length; p++) {
      set(u.base[k] + p, (outs[p], !node.outputs[p].isState));
    }
    for (final s in np.drops) {
      final (v, _) = take(u, s, at, () => 'a drop');
      dec(v.cell);
    }
    for (final s in np.last) {
      final e = u.slot(s)!;
      if (frames.last[e] case (_, true)) {
        throw ZirError(
          'memory: ${at()}: edge ${_showSrc(s)} is still owned after its last use, a leak',
        );
      }
      set(e, null);
    }
    check(() => 'node ${at()}');
  }

  /// Leaves region `a`: takes or dups its results, and checks it owns nothing more.
  List<_Mv> leave(_Act a) {
    final (r, rp, u) = (a.r, a.rp, a.rp._uses);
    final dup = rp.resultDups.toSet();
    final out = <_Mv>[];
    for (var i = 0; i < r.results.length; i++) {
      final s = r.results[i];
      final v = read(u, s, () => '${rp.path} result $i');
      final e = u.slot(s);
      if (dup.contains(i)) {
        inc(v.cell);
      } else if (e != null && !u.state[e]) {
        take(u, s, () => rp.path, () => 'result $i');
      }
      out.add(v);
    }
    final ended = popFrame();
    final e = ended.indexWhere((s) => s?.$2 ?? false);
    if (e >= 0) throw ZirError('memory: `${rp.path}` ends still owning edge $e, a leak');
    return out;
  }

  /// Runs one node on its inputs, as the plan takes them; returns its outputs, owned, or null
  /// when it entered a region.
  List<_Mv>? node(Node node, NodePlan np, String Function() at, List<_Mv> ins) {
    bool data(_Mv m) => m is _Data;
    switch (node.op) {
      case PrimOp(:final prim) when ins.isEmpty && prim.arity != null:
        return [_PrimFn(prim)];
      case PrimOp(prim: Prim.tuple) when ins.every(data) && ins.isNotEmpty:
        final vals = [for (final x in ins) (x as _Data).value];
        return [
          _Data(Tuple(vals), alloc([for (final x in ins) x.cell])),
        ];
      case PrimOp(prim: Prim.atom) when ins.every(data):
        final v = kernel(node, ins);
        final names = switch (ins[1]) {
          _Data(value: Tuple(:final items)) => items,
          _ => const <Value>[],
        };
        if (v case Atom(:final args, :final fields)
            when args.isNotEmpty && args.length + 2 == ins.length) {
          final where = {for (var i = 0; i < names.length; i++) names[i]: i};
          final kids = [
            for (var i = 0; i < args.length; i++)
              ins[2 + (names.isEmpty ? i : where[Str(fields[i])]!)].cell,
          ];
          return [_Data(v, alloc(kids))];
        }
        consume(np, ins);
        return [fresh(v)];
      case PrimOp(prim: Prim.tupleGet):
        final v = kernel(node, ins);
        if ((ins[0], ins[1]) case (
          _Data(value: Tuple(), cell: final c?),
          _Data(value: Int(value: final i)),
        )) {
          final kid = heap[c].kids[i];
          inc(kid);
          return [_Data(v, kid)];
        }
        return [fresh(v)];
      case LambdaOp():
        final cell = alloc([for (final x in ins) x.cell]);
        return [_Clo(cell, node, np.regions[0], ins)];
      case ApplyOp():
        if (ins[0] case final _Clo c
            when c.node.regions[0].args.length == c.node.inputs.length + ins.length - 1) {
          return apply(c, np, at, ins);
        }
        final v = kernel(node, ins);
        consume(np, ins);
        return [fresh(v), for (var p = 1; p < node.outputs.length; p++) const _State()];
      case IfOp():
        final int arm;
        if (ins[0] case _Data(value: Bool(value: final b))) {
          arm = b ? 0 : 1;
        } else {
          final t = If(term(ins[0], _Lets()), const Lit(Int(0)), const Lit(Int(1)));
          switch (ev.run(t)) {
            case Int(value: final i):
              arm = i;
            case final v:
              return failed(node, np, ins, v);
          }
        }
        enter(node.regions[arm], np.regions[arm], [
          for (var j = 1; j < ins.length; j++) (ins[j], np.modes[j] == Mode.owned),
        ], null);
        return null;
      case MatchOp(:final patterns):
        return matched(node, patterns, np, at, ins);
      case ReadOp(:final port):
        final _Mv v;
        if (ev.world.inputs[port] case final x?) {
          v = fresh(x);
        } else if (ev.world.sources.containsKey(port)) {
          v = _Source(port);
        } else {
          ev.run(Read(port));
          throw const ZirError('a read');
        }
        return [v, const _State()];
      case PushOp():
        final v = kernel(node, ins);
        consume(np, ins);
        return [fresh(v), const _State()];
      default:
        final v = kernel(node, ins);
        consume(np, ins);
        return [fresh(v)];
    }
  }

  /// A call of closure [c]: each argument passed as the callee's parameter takes it, an owned
  /// argument to a borrowed parameter held here until the call returns.
  List<_Mv>? apply(_Clo c, NodePlan np, String Function() at, List<_Mv> ins) {
    if (np.callee case final want? when !identical(want, c.body)) {
      throw ZirError(
        'memory: ${at()}: the plan calls `${want.path}`, and the callee is `${c.body.path}`',
      );
    }
    final rp = c.body;
    final args = <_Slot>[];
    final held = <_Slot?>[];
    for (var i = 0; i < ins.length - 1; i++) {
      final v = ins[1 + i];
      switch ((np.modes[1 + i], rp.args[i])) {
        case (Mode.owned, Mode.owned):
          args.add((v, true));
        case (Mode.owned, Mode.borrowed):
          held.add((v, true));
          args.add((v, false));
        case (Mode.borrowed, Mode.borrowed):
          args.add((v, false));
        case (Mode.borrowed, Mode.owned):
          throw ZirError(
            'memory: ${at()}: argument $i is passed borrowed to `${rp.path}`, which consumes it',
          );
      }
    }
    args.addAll([for (final v in c.caps) (v, false)]);
    pushFrame(held);
    enter(c.node.regions[0], rp, args, () {
      for (final s in popFrame()) {
        dec(s!.$1.cell);
      }
    });
    return null;
  }

  /// A `match`: the kernel picks the arm and binds its values, and the machine finds the
  /// binders' cells inside the scrutinee's and releases the scrutinee.
  List<_Mv>? matched(
    Node node,
    List<Pattern> ps,
    NodePlan np,
    String Function() at,
    List<_Mv> ins,
  ) {
    final lets = _Lets();
    final s = term(ins[0], lets);
    final arms = <(Pattern, Term)>[];
    var n = 0;
    for (var i = 0; i < ps.length; i++) {
      final xs = <Term>[Lit(Int(i))];
      final p = _rename(ps[i], () {
        final x = '\u0000bind${++n}';
        xs.add(Var(x));
        return x;
      });
      arms.add((p, PrimApp(Prim.tuple, xs)));
    }
    final picked = ev.run(_wrap(lets, Match(s, arms)));
    final int i;
    final List<Value> vals;
    if (picked case Tuple(items: [Int(value: final x), ...final rest])
        when x >= 0 && x < ps.length) {
      (i, vals) = (x, rest);
    } else {
      return failed(node, np, ins, picked);
    }
    final arm = np.regions[i];
    final paths = <List<int>>[];
    if (ins[0] case _Data(:final value)) _binderPaths(ps[i], value, [], paths);
    final scrut = ins[0].cell;
    final cells = [
      for (var b = 0; b < vals.length; b++) b < paths.length ? cellAt(scrut, paths[b], 0) : null,
    ];
    final args = <_Slot>[];
    if (np.modes[0] == Mode.owned) {
      final kept = [
        for (var b = 0; b < vals.length; b++)
          if (arm.args[b] == Mode.owned) b,
      ];
      if (plan.fuse) {
        release(scrut, [
          for (final b in kept)
            if (b < paths.length) paths[b],
        ], 0);
      } else {
        for (final b in kept) {
          inc(cells[b]);
        }
        dec(scrut);
      }
      for (var b = 0; b < vals.length; b++) {
        final owned = arm.args[b] == Mode.owned;
        args.add((_Data(vals[b], owned ? cells[b] : null), owned));
      }
    } else {
      for (var b = 0; b < vals.length; b++) {
        if (arm.args[b] == Mode.owned) {
          throw ZirError('memory: ${at()}: the scrutinee is borrowed, and arm $i owns binder $b');
        }
        args.add((_Data(vals[b], cells[b]), false));
      }
    }
    for (var j = 1; j < ins.length; j++) {
      args.add((ins[j], np.modes[j] == Mode.owned));
    }
    enter(node.regions[i], arm, args, null);
    return null;
  }

  /// An `if` or `match` whose decision is a failure value [v]: the value is the result, and
  /// the owned inputs are dropped.
  List<_Mv> failed(Node node, NodePlan np, List<_Mv> ins, Value v) {
    consume(np, ins);
    return [fresh(v), for (var p = 1; p < node.outputs.length; p++) const _State()];
  }

  /// Fused release of the scrutinee [cell], keeping the cells at [kept], each from its step
  /// [d] on.
  void release(int? cell, List<List<int>> kept, int d) {
    if (cell == null || kept.any((p) => p.length == d)) return;
    final c = heap[cell];
    if (c.count == 1) {
      c.count = 0;
      stats.frees++;
      live--;
      touched.add(cell);
      final kids = c.kids;
      c.kids = const [];
      for (final k in kids) {
        if (k != null) {
          refs[k]--;
          touched.add(k);
        }
      }
      final byKid = <int, List<List<int>>>{};
      for (final p in kept) {
        (byKid[p[d]] ??= []).add(p);
      }
      for (var i = 0; i < kids.length; i++) {
        if (byKid[i] case final sub?) {
          release(kids[i], sub, d + 1);
        } else {
          dec(kids[i]);
        }
      }
    } else {
      for (final p in kept) {
        inc(cellAt(cell, p, d));
      }
      dec(cell);
    }
  }

  /// The cell at [path] from its step [d] on, inside cell [c].
  int? cellAt(int? c, List<int> path, int d) {
    for (var x = d; x < path.length && c != null; x++) {
      final kids = heap[c].kids;
      c = path[x] < kids.length ? kids[path[x]] : null;
    }
    return c;
  }

  /// Drops each input the node took owned.
  void consume(NodePlan np, List<_Mv> ins) {
    for (var j = 0; j < ins.length; j++) {
      if (np.modes[j] == Mode.owned) dec(ins[j].cell);
    }
  }

  /// The value the kernel gives [node] run alone on [ins].
  Value kernel(Node node, List<_Mv> ins) {
    final lets = _Lets();
    final terms = [for (final v in ins) term(v, lets)];
    return ev.run(_wrap(lets, raiseWith(alone(node), terms)));
  }

  /// A one-node region running [node] on its arguments.
  Region alone(Node node) => _alone.putIfAbsent(
    node,
    () => Region(
      RegionKind.function,
      const [],
      [
        Node(
          node.op,
          [for (var i = 0; i < node.inputs.length; i++) Arg(i)],
          node.outputs,
          node.regions,
        ),
      ],
      const [Out(0, 0)],
    ),
  );

  /// The kernel term for [v]; a lookup port is read once, by a `let` in [lets].
  Term term(_Mv v, _Lets lets) => switch (v) {
    _Data(:final value) => Lit(value),
    _PrimFn(:final prim) => PrimFn(prim),
    _State() => const Lit(Tuple([])),
    _Source(:final port) => () {
      if (lets.seen.add(port)) lets.order.add(port);
      return Var(_portVar(port));
    }(),
    _Clo(:final node, :final caps) => raiseWith(alone(node), [for (final x in caps) term(x, lets)]),
  };

  _Mv read(_Uses u, Src s, String Function() at) {
    final e = u.slot(s);
    if (e == null) return _Data((s as Const).value, null);
    final slot = frames.last[e];
    if (slot == null) {
      throw ZirError('memory: ${at()}: edge ${_showSrc(s)} is read after its last use');
    }
    final v = slot.$1;
    if (v.cell case final c? when heap[c].count == 0) {
      throw ZirError('memory: ${at()}: edge ${_showSrc(s)} is read after its cell $c was freed');
    }
    return v;
  }

  /// Takes the frame's reference to edge [s], which the frame must own.
  _Slot take(_Uses u, Src s, String Function() at, String Function() why) {
    final old = set(u.slot(s)!, null);
    return switch (old) {
      (_, true) => old,
      (_, false) => throw ZirError(
        'memory: ${at()}: ${why()} consumes edge ${_showSrc(s)}, which is borrowed and has no '
        'dup',
      ),
      null => throw ZirError(
        'memory: ${at()}: ${why()} consumes edge ${_showSrc(s)}, already consumed or past its '
        'last use',
      ),
    };
  }

  int alloc(List<int?> kids) {
    for (final k in kids) {
      if (k != null) {
        refs[k]++;
        touched.add(k);
      }
    }
    refs.add(0);
    holds.add(0);
    touched.add(heap.length);
    heap.add(_Cell(kids));
    stats.allocations++;
    live++;
    if (live > stats.peak) stats.peak = live;
    return heap.length - 1;
  }

  /// A fresh value: its cells allocated, the parts of a tuple or an atom each its own.
  _Mv fresh(Value v) => _Data(v, tree(v));

  int? tree(Value v) => switch (v) {
    Bool() || Int() || Float() => null,
    Tuple(:final items) when items.isEmpty => null,
    Atom(:final args) when args.isEmpty => null,
    Tuple(:final items) => alloc([for (final x in items) tree(x)]),
    Atom(:final args) => alloc([for (final x in args) tree(x)]),
    _ => alloc(const []),
  };

  void inc(int? c) {
    if (c == null) return;
    stats.increments++;
    touched.add(c);
    final cell = heap[c];
    cell.count++;
    if (cell.count == 2 && !cell.shared) {
      cell.shared = true;
      stats.shared++;
    }
  }

  /// Decrements cell [c]'s count, and frees it and its children in turn when it reaches 0:
  /// each child is handled, with its own children, before the next, as a stack keeps them.
  void dec(int? c) {
    if (c == null) return;
    final todo = [c];
    while (todo.isNotEmpty) {
      final c = todo.removeLast();
      stats.decrements++;
      final cell = heap[c];
      if (cell.count == 0) throw ZirError('memory: cell $c is dropped after it was freed');
      touched.add(c);
      cell.count--;
      if (cell.count == 0) {
        stats.frees++;
        live--;
        final kids = cell.kids;
        cell.kids = const [];
        for (final k in kids) {
          if (k != null) refs[k]--;
        }
        for (var i = kids.length - 1; i >= 0; i--) {
          if (kids[i] case final k?) todo.add(k);
        }
      }
    }
  }

  /// Counts slot [s] into the references of its cell, or out of them.
  void note(_Slot? s, bool into) {
    if (s == null) return;
    final (v, owned) = s;
    final c = v.cell;
    if (c == null) return;
    final by = into ? 1 : -1;
    holds[c] += by;
    if (owned) refs[c] += by;
    touched.add(c);
  }

  void pushFrame(List<_Slot?> frame) {
    for (final s in frame) {
      note(s, true);
    }
    frames.add(frame);
  }

  List<_Slot?> popFrame() {
    final frame = frames.removeLast();
    for (final s in frame) {
      note(s, false);
    }
    return frame;
  }

  /// Puts [s] in slot [e] of the current frame; returns what it held.
  _Slot? set(int e, _Slot? s) {
    note(s, true);
    final frame = frames.last;
    final old = frame[e];
    frame[e] = s;
    note(old, false);
    return old;
  }

  /// Checks the cells touched since the last check, which passed: no other cell's count or
  /// references changed. When one is wrong, the full audit names every fault.
  void check(String Function() when) {
    final cells = touched;
    touched = [];
    for (final c in cells) {
      final count = heap[c].count;
      if (count != refs[c] || (count == 0 && holds[c] > 0)) return audit(when());
    }
  }

  /// Checks that each live cell's count is the number of references to it, from owned slots
  /// in every frame and from live cells, and that no slot holds a freed cell.
  void audit(String when) {
    final refs = List.filled(heap.length, 0);
    for (var f = 0; f < frames.length; f++) {
      final frame = frames[f];
      for (var e = 0; e < frame.length; e++) {
        final slot = frame[e];
        final c = slot?.$1.cell;
        if (slot == null || c == null) continue;
        if (heap[c].count == 0) {
          throw ZirError('memory: at $when, edge $e of frame $f holds cell $c, which is freed');
        }
        if (slot.$2) refs[c]++;
      }
    }
    for (final cell in heap) {
      if (cell.count > 0) {
        for (final k in cell.kids) {
          if (k != null) refs[k]++;
        }
      }
    }
    final wrong = [
      for (var c = 0; c < heap.length; c++)
        if (heap[c].count != refs[c])
          'cell $c has count ${heap[c].count} and ${_plural(refs[c], 'reference')}',
    ];
    if (wrong.isEmpty) return;
    throw ZirError(
      'memory: at $when, ${wrong.join('; ')} (a count above its references is a missed drop, '
      'one below is an extra drop)',
    );
  }
}

String _portVar(String p) => '\u0000port $p';

/// [t] with each lookup port in [ports] read first.
Term _wrap(_Lets ports, Term t) {
  for (final p in ports.order.reversed) {
    t = Let(_portVar(p), Read(p), t);
  }
  return t;
}

/// Adds to [out] the path of child indices to each binder of [p] inside [v], which [p]
/// matches, in preorder; [at] is the path to [v].
void _binderPaths(Pattern p, Value v, List<int> at, List<List<int>> out) {
  void sub(int i, Pattern q, Value x) {
    at.add(i);
    _binderPaths(q, x, at, out);
    at.removeLast();
  }

  switch ((p, v)) {
    case (BindP(), _):
      out.add([...at]);
    case (TupleP(:final items), Tuple(items: final xs)):
      for (var i = 0; i < items.length && i < xs.length; i++) {
        sub(i, items[i], xs[i]);
      }
    case (AtomP(args: final ps), Atom(:final args)):
      for (var i = 0; i < ps.length && i < args.length; i++) {
        sub(i, ps[i], args[i]);
      }
    case (FieldsP(:final fields), final Atom a):
      for (final (f, q) in fields) {
        if (_fieldIndex(a.fields, f) case final i?) sub(i, q, a.args[i]);
      }
    default:
  }
}

/// The index of field [f] in the sorted [fields], found by binary search.
int? _fieldIndex(List<String> fields, String f) {
  var (lo, hi) = (0, fields.length);
  while (lo < hi) {
    final mid = (lo + hi) >> 1;
    final c = compareUtf8(fields[mid], f);
    if (c == 0) return mid;
    if (c < 0) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return null;
}

/// [p] with each binder renamed, in preorder, to what [f] gives.
Pattern _rename(Pattern p, String Function() f) => switch (p) {
  BindP() => BindP(f()),
  AtomP(:final name, :final args) => AtomP(name, [for (final q in args) _rename(q, f)]),
  TupleP(:final items) => TupleP([for (final q in items) _rename(q, f)]),
  FieldsP(:final name, :final fields) => FieldsP(name, [
    for (final (x, q) in fields) (x, _rename(q, f)),
  ]),
  WildP() || LitP() || AnyAtomP() || IsP() => p,
};

String _showSrc(Src s) => switch (s) {
  Arg(:final i) => 'argument $i',
  Out(:final node, :final port) => '$node.$port',
  Const(:final value) => 'constant $value',
};

String _held(bool owned) => owned ? 'owned' : 'borrowed';

String _plural(int n, String what) => n == 1 ? '1 $what' : '$n ${what}s';
