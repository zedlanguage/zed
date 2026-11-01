/// What the generated code and the runtime hooks share about one graph: each node the
/// counting machine runs, numbered, with its plan; each lambda; the constants; the
/// primitives used as values; the lookup ports.
library;

import '../kernel/term.dart' show Prim;
import '../kernel/value.dart';
import '../zir/graph.dart';
import '../zir/memory.dart';
import 'heap.dart' show Word;

/// One node of a planned region.
final class NodeInfo {
  /// The node.
  final Node node;

  /// Its plan.
  final NodePlan plan;

  /// The node alone in a region whose arguments are its inputs, for the kernel.
  final Region alone;

  /// Where it is (`r.3/0.1`), for messages.
  final String path;

  /// For a lambda: its index among the lambdas.
  int? lambda;

  /// For an `apply` the plan resolves: the callee's lambda.
  int? callee;

  /// An error the node raises when it runs, known before it runs.
  ZirError? error;

  NodeInfo(this.node, this.plan, this.path)
    : alone = Region(
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
      );

  /// How it takes each input.
  List<Mode> get modes => plan.modes;

  /// For an `if` or a `match`: how each arm holds each of its arguments.
  List<List<Mode>> get arms => [for (final r in plan.regions) r.args];
}

/// One lambda: its node, the plan of its body, its parameters.
final class LambdaInfo {
  /// The lambda node's number.
  final int node;

  /// The body's plan.
  final RegionPlan body;

  /// The number of parameters, before the captures.
  final int params;

  const LambdaInfo(this.node, this.body, this.params);

  /// How the body holds each parameter.
  List<Mode> get modes => body.args.sublist(0, params);
}

/// The tables of one graph.
final class Tables {
  /// The nodes, in preorder.
  final nodes = <NodeInfo>[];

  /// The numbers of each region's nodes, by the region's plan.
  final ids = Map<RegionPlan, List<int>>.identity();

  /// The lambdas.
  final lambdas = <LambdaInfo>[];

  /// The constants that are not scalars, which the heap holds uncounted.
  final consts = <Value>[];

  /// The primitives used as values.
  final prims = <Prim>[];

  /// The lookup ports.
  final ports = <String>[];

  /// Each lookup port's index among the ports.
  final portAt = <String, int>{};

  /// Each constant's index among the constants.
  final _constAt = <Value, int>{};

  /// Each lambda's index by the plan of its body.
  final _lambdaAt = Map<RegionPlan, int>.identity();

  /// Whether a `match` fuses its release.
  final bool fuse;

  /// The tables of graph [g] under [plan].
  Tables(Region g, Plan plan) : fuse = plan.fuse {
    _visit(g, plan.root);
    // An `apply` may call a lambda visited after it.
    for (final ni in nodes) {
      _resolve(ni);
    }
  }

  /// Numbers the nodes of [g] and its regions in preorder. Regions nest as deep as the term, so
  /// the regions in progress are on a stack, each with its next node.
  void _visit(Region g, RegionPlan root) {
    final stack = [_Visit(g, root)];
    while (stack.isNotEmpty) {
      final v = stack.last;
      final (r, rp) = (v.r, v.rp);
      if (v.k == 0) {
        for (final s in r.results) {
          _constant(s);
        }
        ids[rp] = [];
      }
      if (v.k == r.nodes.length) {
        stack.removeLast();
        continue;
      }
      final k = v.k++;
      final node = r.nodes[k];
      final np = rp.nodes[k];
      final id = nodes.length;
      ids[rp]!.add(id);
      for (final s in node.inputs) {
        _constant(s);
      }
      final ni = NodeInfo(node, np, '${rp.path}.$k');
      nodes.add(ni);
      switch (node.op) {
        case PrimOp(:final prim) when node.inputs.isEmpty && prim.arity != null:
          if (!prims.contains(prim)) prims.add(prim);
        case ReadOp(:final port):
          if (!portAt.containsKey(port)) {
            portAt[port] = ports.length;
            ports.add(port);
          }
        case LambdaOp():
          if (np.regions.isEmpty) {
            throw ZirError('native: lambda body `${ni.path}/0` has no plan');
          }
          final body = np.regions[0];
          final params = node.regions[0].args.length - node.inputs.length;
          _lambdaAt[body] = lambdas.length;
          ni.lambda = lambdas.length;
          lambdas.add(LambdaInfo(id, body, params));
          stack.add(_Visit(node.regions[0], body));
        case IfOp() || MatchOp():
          if (np.regions.length < node.regions.length) {
            throw ZirError('native: arm `${ni.path}/${np.regions.length}` has no plan');
          }
          // The first arm is numbered first.
          for (var i = node.regions.length - 1; i >= 0; i--) {
            stack.add(_Visit(node.regions[i], np.regions[i]));
          }
        default:
      }
    }
  }

  /// Resolves [ni]'s callee, when it is an `apply` the plan resolves, and records the error
  /// a call raises that passes borrowed what the callee consumes.
  void _resolve(NodeInfo ni) {
    if (ni.node.op is! ApplyOp) return;
    final want = ni.plan.callee;
    if (want == null) return;
    final li =
        _lambdaAt[want] ??
        (throw ZirError('native: ${ni.path}: the plan calls `${want.path}`, no lambda'));
    final l = lambdas[li];
    if (l.params + 1 == ni.node.inputs.length) {
      final modes = l.modes;
      for (var i = 0; i < l.params; i++) {
        if (ni.modes[1 + i] == Mode.borrowed && modes[i] == Mode.owned) {
          ni.error = ZirError(
            'memory: ${ni.path}: argument $i is passed borrowed to `${want.path}`, which '
            'consumes it',
          );
          break;
        }
      }
    }
    ni.callee = li;
  }

  void _constant(Src s) {
    if (s case Const(:final value) when Word.scalar(value) == null) {
      _constAt.putIfAbsent(value, () {
        consts.add(value);
        return consts.length - 1;
      });
    }
  }

  /// The word of constant [v]: its own when it is a scalar, else its index in the table.
  Word constant(Value v) => Word.scalar(v) ?? Word(4, _constAt[v]!);
}

/// A region being numbered, and the index of its next node.
final class _Visit {
  final Region r;
  final RegionPlan rp;
  var k = 0;

  _Visit(this.r, this.rp);
}
