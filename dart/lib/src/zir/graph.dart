/// ZIR, the intermediate representation (step L1.31; DESIGN.md sec:ir): an acyclic
/// hierarchical graph of the RVSDG family. A [Region] holds nodes in topological order; a
/// [Node] is an operation, and the region nodes hold regions of their own. Edges are typed:
/// a value edge carries a type, a domain and facets, and a state edge orders the effects on
/// one port. Constants and types live on edges, so a node is an opcode and its attributes.
///
/// The node inventory is the kernel's seven generators, the four derived nodes, each carrying
/// its kernel definition as a certificate region, the scalar primitives, and the region nodes:
///
/// | node | inputs | regions | outputs |
/// |---|---|---|---|
/// | `reindex` | family, key map, value map | | family |
/// | `discard` | family, selector | | family |
/// | `fold` | family, operator, the identity when it has one | | value |
/// | `fix lattice` | bottom, join, captures | loop: iterate, captures → next | value |
/// | `fix definedness` | domain, captures | loop: `this`, key, captures → entry | family |
/// | `gen` | generation 0, captures | loop: step, loop: guard (frame, captures → one) | family |
/// | `port read` | state | | value, state |
/// | `port push` | state, value | | acknowledgment, state |
/// | `fam` | domain, captures | function: key, captures → entry | family |
/// | `group`, `rank`, `scan`, `join` | any | function: the certificate | any |
/// | `prim` | the primitive's arguments, or none | | value, or the primitive as a function |
/// | `apply` | function, arguments | | value |
/// | `lambda` | captures | function: parameters, captures → value | function |
/// | `if` | condition, captures | match: then, match: else | any |
/// | `match` | scrutinee, captures | match per arm: the arm's bindings, captures | any |
/// | `rec` | captures | rec: the functions, captures → the functions | the functions |
/// | `wave` | captures | port: captures → outputs | any |
///
/// Where DESIGN.md does not say, step L1.31 decides:
///
/// - **Regions are isolated**, as in the RVSDG: a node reads its own region's arguments,
///   earlier nodes' outputs and constants, never an enclosing region's edges. A value from
///   outside enters as a capture, an input appended after the node's fixed inputs and
///   received as the matching argument after the region's own, with the same edge type.
/// - **State edges are linear**: each is used exactly once in its region, by a node or as a
///   result, so the effects on a port are totally ordered. A state edge enters only a match
///   or port region, or the function region of a `lambda`, which takes one state argument
///   for each port its body uses, after its parameters, and returns the states after its
///   value; an `apply` passes the states in after its arguments and has them as outputs after
///   the value (a `gen` step with an effect waits for the scheduler of step L4).
/// - **A certificate is kernel-only**: a derived node's region holds no derived node, at any
///   depth, so its definition bottoms out in the generators. Its arguments are the node's
///   inputs and its results the node's outputs.
/// - The validator checks structure: references, arities, region kinds, edge kinds, capture
///   types and linearity. Whether a value edge's type fits its consumer is the checker's
///   question, already answered for the kernel term the graph is lowered from (step L1.33).
library;

import '../canon/canon.dart' show Facet;
import '../canon/domain.dart';
import '../kernel/term.dart';
import '../kernel/types.dart';
import '../kernel/value.dart';
import '../store/interval.dart';
import 'text.dart' as text;

/// A graph the reader or the validator rejects, or binary data that does not decode.
final class ZirError implements Exception {
  final String message;

  const ZirError(this.message);

  @override
  String toString() => message;
}

/// The kind of a region (DESIGN.md sec:ir, "Shape"); its name is how the text form writes it.
enum RegionKind {
  /// The body of a function, a family's entries, or a certificate.
  function,

  /// An arm of an `if` or a `match`.
  match,

  /// The step or guard of a recurrence or generation.
  loop,

  /// Mutually recursive functions.
  rec,

  /// A wave over ports.
  port,
}

/// An edge's type: a value's type, domain and facets, or the state of a port.
sealed class Edge {
  const Edge();

  /// A value edge of type `type`, with no facts.
  factory Edge.value(Type type) = ValueEdge;

  bool get isState => this is StateEdge;

  @override
  String toString() => text.edge(this);
}

/// What a value edge carries.
final class ValueEdge extends Edge {
  /// The value's type.
  final Type type;

  /// The integer facts.
  final Domain domain;

  /// The other facts.
  final List<Facet> facets;

  ValueEdge(this.type, {Domain? domain, this.facets = const []}) : domain = domain ?? anyDomain;

  @override
  bool operator ==(Object other) =>
      other is ValueEdge &&
      other.type == type &&
      other.domain == domain &&
      other.facets.length == facets.length &&
      Iterable<int>.generate(facets.length).every((i) => other.facets[i] == facets[i]);

  @override
  int get hashCode => Object.hash(type, domain, Object.hashAll(facets));
}

/// The ordering of the effects on the named port.
final class StateEdge extends Edge {
  final String port;

  const StateEdge(this.port);

  @override
  bool operator ==(Object other) => other is StateEdge && other.port == port;

  @override
  int get hashCode => port.hashCode;
}

/// The domain that admits every integer.
final anyDomain = Domain.ints(IntervalSet.top());

/// Where a node's input, or a region's result, comes from.
sealed class Src {
  const Src();
}

/// Argument `i` of the region.
final class Arg extends Src {
  final int i;

  const Arg(this.i);
}

/// Output `port` of node `node` of the region, an earlier node.
final class Out extends Src {
  final int node, port;

  const Out(this.node, this.port);
}

/// A constant.
final class Const extends Src {
  final Value value;

  const Const(this.value);
}

/// One of the four derived nodes the planner matches; its name is how the text form writes it.
enum Derived {
  /// Grouping by a key.
  group,

  /// Ranking along an order.
  rank,

  /// A prefix fold.
  scan,

  /// A join of two families.
  join,
}

/// A node's operation and its attributes.
sealed class Op {
  const Op();

  /// The name of the operation, as the text form writes it first.
  String get name => switch (this) {
    ReindexOp() => 'reindex',
    DiscardOp() => 'discard',
    FoldOp() => 'fold',
    FixOp() => 'fix',
    GenOp() => 'gen',
    ReadOp() || PushOp() => 'port',
    FamOp() => 'fam',
    DerivedOp(:final derived) => derived.name,
    PrimOp() => 'prim',
    ApplyOp() => 'apply',
    LambdaOp() => 'lambda',
    IfOp() => 'if',
    MatchOp() => 'match',
    RecOp() => 'rec',
    WaveOp() => 'wave',
  };

  /// How a message names the operation: its name, with the primitive or the port.
  String get title => switch (this) {
    PrimOp(:final prim) => 'prim ${text.spell(prim)}',
    ReadOp(:final port) => 'port read $port',
    PushOp(:final port) => 'port push $port',
    _ => name,
  };
}

/// `reindex`, with its injectivity evidence.
final class ReindexOp extends Op {
  final Witness witness;

  const ReindexOp(this.witness);
}

/// `discard`.
final class DiscardOp extends Op {
  const DiscardOp();
}

/// `fold` over `depth` key levels, with an identity input or not, and the evidence for its
/// operator.
final class FoldOp extends Op {
  final int depth;
  final bool identity;
  final Evidence ev;

  const FoldOp(this.depth, this.identity, this.ev);
}

/// `fix`, a lattice ascent, whose second input is the join, or the definedness instance, with
/// the evidence for its step.
final class FixOp extends Op {
  final bool lattice;
  final Evidence ev;

  const FixOp(this.lattice, this.ev);
}

/// `gen`, testing its guard before or after each step.
final class GenOp extends Op {
  final GuardPos pos;

  const GenOp(this.pos);
}

/// `port read` of the named port.
final class ReadOp extends Op {
  final String port;

  const ReadOp(this.port);
}

/// `port push` to the named port.
final class PushOp extends Op {
  final String port;

  const PushOp(this.port);
}

/// `fam`.
final class FamOp extends Op {
  const FamOp();
}

/// A derived node.
final class DerivedOp extends Op {
  final Derived derived;

  const DerivedOp(this.derived);
}

/// A primitive, applied to its arguments; with no inputs, a primitive of fixed arity is
/// itself, as a function value (step L1.33), which the kernel tells apart from a lambda that
/// calls it (a fold of `+` itself sums exactly).
final class PrimOp extends Op {
  final Prim prim;

  const PrimOp(this.prim);
}

/// A call.
final class ApplyOp extends Op {
  const ApplyOp();
}

/// A function.
final class LambdaOp extends Op {
  const LambdaOp();
}

/// A two-armed branch.
final class IfOp extends Op {
  const IfOp();
}

/// A match, one region per pattern.
final class MatchOp extends Op {
  final List<Pattern> patterns;

  const MatchOp(this.patterns);
}

/// Mutual recursion.
final class RecOp extends Op {
  const RecOp();
}

/// A wave.
final class WaveOp extends Op {
  const WaveOp();
}

/// A node.
final class Node {
  final Op op;

  /// The inputs, fixed ones first, then captures.
  final List<Src> inputs;

  /// The outputs' edge types.
  final List<Edge> outputs;

  /// The regions, for a region node or a derived node.
  final List<Region> regions;

  const Node(this.op, this.inputs, this.outputs, [this.regions = const []]);
}

/// A region.
final class Region {
  final RegionKind kind;

  /// The arguments' edge types.
  final List<Edge> args;

  /// The nodes, each after every node it reads.
  final List<Node> nodes;

  /// The results.
  final List<Src> results;

  const Region(this.kind, this.args, this.nodes, this.results);

  /// The edge type of `src` in this region, which must be valid there.
  Edge edge(Src src) => switch (src) {
    Arg(:final i) => args[i],
    Out(:final node, :final port) => nodes[node].outputs[port],
    Const(:final value) => Edge.value(Type.lit(value) ?? Type.top),
  };
}

/// The number of names pattern `p` binds, in preorder.
int binds(Pattern p) => switch (p) {
  BindP() => 1,
  AtomP(args: final ps) || TupleP(items: final ps) => ps.fold(0, (n, p) => n + binds(p)),
  FieldsP(:final fields) => fields.fold(0, (n, f) => n + binds(f.$2)),
  WildP() || LitP() || AnyAtomP() || IsP() => 0,
};

/// What a node's operation requires of it: the inputs before the captures, whether the inputs
/// must be exactly those, the number of outputs when it is fixed, and each region's kind,
/// number of arguments before the captures, and number of results.
typedef _Shape = ({int fixed, bool exact, int? outputs, List<(RegionKind, int, int)> regions});

_Shape _shape(Node n) {
  final ins = n.inputs.length;
  final outs = n.outputs.length;
  _Shape leaf(int fixed, [int outputs = 1]) =>
      (fixed: fixed, exact: true, outputs: outputs, regions: const []);
  _Shape captures(int fixed, int? outputs, List<(RegionKind, int, int)> regions) =>
      (fixed: fixed, exact: false, outputs: outputs, regions: regions);
  return switch (n.op) {
    ReindexOp() => leaf(3),
    DiscardOp() => leaf(2),
    FoldOp(depth: 0) => throw const ZirError(
      '`fold` has depth 0, and a family has at least 1 level',
    ),
    FoldOp(:final identity) => leaf(identity ? 3 : 2),
    FixOp(lattice: true) => captures(2, 1, [(RegionKind.loop, 1, 1)]),
    FixOp(lattice: false) => captures(1, 1, [(RegionKind.loop, 2, 1)]),
    GenOp() => captures(1, 1, [(RegionKind.loop, 1, 1), (RegionKind.loop, 1, 1)]),
    ReadOp() => leaf(1, 2),
    PushOp() => leaf(2, 2),
    FamOp() => captures(1, 1, [(RegionKind.function, 1, 1)]),
    DerivedOp() when ins == 0 || outs == 0 => throw const ZirError(
      'a derived node has at least one input and one output',
    ),
    DerivedOp() => captures(0, null, [(RegionKind.function, 0, outs)]),
    PrimOp(:final prim) => switch (prim.arity) {
      _? when ins == 0 => leaf(0),
      final k? => leaf(k),
      null => captures(0, 1, const []),
    },
    ApplyOp() when ins == 0 => throw const ZirError('`apply` has no function input'),
    ApplyOp() => captures(1, null, const []),
    LambdaOp() => () {
      var (params, states) = (0, 0);
      if (n.regions.isNotEmpty) {
        final args = n.regions.first.args;
        params = args.length > ins ? args.length - ins : 0;
        states = args.take(params).where((a) => a.isState).length;
      }
      return captures(0, 1, [(RegionKind.function, params, 1 + states)]);
    }(),
    IfOp() => captures(1, null, [(RegionKind.match, 0, outs), (RegionKind.match, 0, outs)]),
    MatchOp(patterns: []) => throw const ZirError('`match` has no arm'),
    MatchOp(:final patterns) => captures(1, null, [
      for (final p in patterns) (RegionKind.match, binds(p), outs),
    ]),
    RecOp() when outs == 0 => throw const ZirError('`rec` defines no function'),
    RecOp() => captures(0, null, [(RegionKind.rec, outs, outs)]),
    WaveOp() => captures(0, null, [(RegionKind.port, 0, outs)]),
  };
}

/// Checks the structure of the graph rooted at `root`; throws a [ZirError] that names the
/// node or region at fault by its path in the text form (`r.2/0.1`) and says what is wrong.
///
/// Regions nest as deep as the program does, so the checks keep their own stack: `todo`
/// holds the checks still to make, the next on top.
void validate(Region root) {
  final todo = <void Function()>[];
  _region(root, const _Path(null, 'r'), false, false, todo);
  while (todo.isNotEmpty) {
    todo.removeLast()();
  }
}

/// The path of a region or node in the text form, kept as its last step and the path before
/// it, so that a step deeper costs the same at any depth; it is written out only in a message.
final class _Path {
  final _Path? parent;
  final String step;

  const _Path(this.parent, this.step);

  @override
  String toString() {
    final steps = <String>[];
    for (_Path? p = this; p != null; p = p.parent) {
      steps.add(p.step);
    }
    return steps.reversed.join();
  }
}

/// A state edge of a region: `(-1, i)` for argument `i`, `(k, p)` for output `p` of node `k`.
typedef _State = (int, int);

/// The text form of the state edge `e` of the region at `path`.
String _stateName(_State e, _Path path) => e.$1 < 0 ? '$path^${e.$2}' : '$path.${e.$1}^${e.$2}';

/// Checks `r`'s arguments, and leaves the checks of its nodes and results on `todo`.
/// `ofLambda` when `r` is the region of a `lambda` node, whose state arguments are the ports
/// its body uses.
void _region(Region r, _Path path, bool inCertificate, bool ofLambda, List<void Function()> todo) {
  if (r.kind != RegionKind.match && r.kind != RegionKind.port && !ofLambda) {
    final i = r.args.indexWhere((a) => a.isState);
    if (i >= 0) throw ZirError('$path^$i: a state edge cannot enter a ${r.kind.name} region');
  }
  if (ofLambda) {
    // The results are read below, so their sources are checked first.
    for (final (i, src) in r.results.indexed) {
      _source(r, src, r.nodes.length, path, path, 'result $i');
    }
    final states = r.args.where((a) => a.isState).toList();
    final back = [for (final s in r.results.skip(1)) r.edge(s)];
    if ((r.results.isNotEmpty && r.edge(r.results.first).isState) ||
        back.length != states.length ||
        Iterable<int>.generate(back.length).any((i) => back[i] != states[i])) {
      throw ZirError(
        '$path: a lambda\'s region returns its value and then the state of each port it '
        'takes, in the order of its arguments (${states.join(', ')}), and returns '
        '(${r.results.map((s) => r.edge(s)).join(', ')})',
      );
    }
  }
  // How many times each state edge of the region is used, kept in order of first use.
  final uses = <_State, int>{};
  void count(Src src) {
    if (r.edge(src).isState) {
      final e = switch (src) {
        Arg(:final i) => (-1, i),
        Out(:final node, :final port) => (node, port),
        Const() => throw StateError('a constant is not a state edge'),
      };
      uses[e] = (uses[e] ?? 0) + 1;
    }
  }

  // Pushed last to run first: each node in order, its regions' checks before the next node's.
  todo.add(() => _close(r, path, uses, count));
  for (final (k, n) in r.nodes.indexed.toList().reversed) {
    todo.add(() {
      final at = _Path(path, '.$k');
      for (final (i, src) in n.inputs.indexed) {
        _source(r, src, k, path, at, 'input $i');
        count(src);
      }
      _node(r, n, at, inCertificate, todo);
    });
  }
}

/// Checks the results of `r` and that each of its state edges is used exactly once.
void _close(Region r, _Path path, Map<_State, int> uses, void Function(Src) count) {
  for (final (i, src) in r.results.indexed) {
    _source(r, src, r.nodes.length, path, path, 'result $i');
    count(src);
  }
  for (final MapEntry(key: e, value: n) in uses.entries) {
    if (n > 1) {
      throw ZirError(
        '${_stateName(e, path)}: a state edge is used $n times, and each is used exactly once',
      );
    }
  }
  final made = <_State>[
    for (final (i, a) in r.args.indexed)
      if (a.isState) (-1, i),
    for (final (k, n) in r.nodes.indexed)
      for (final (p, e) in n.outputs.indexed)
        if (e.isState) (k, p),
  ];
  for (final e in made) {
    if (!uses.containsKey(e)) {
      throw ZirError(
        '${_stateName(e, path)}: a state edge is never used, and each is used exactly once',
      );
    }
  }
}

/// `n` of `thing`, with the plural when `n` is not 1: `1 input`, `2 inputs`.
String _several(int n, String thing) => n == 1 ? '1 $thing' : '$n ${thing}s';

/// `1 is` or `n are`.
String _written(int n) => n == 1 ? '1 is' : '$n are';

/// Checks that `src` names an argument of `r` or an output of a node before node `before`;
/// the message starts with `at` and `what`.
void _source(Region r, Src src, int before, _Path path, _Path at, String what) {
  final why = switch (src) {
    Arg(:final i) when i >= r.args.length =>
      '$path^$i: the region has ${_several(r.args.length, 'argument')}, numbered from 0',
    Out(:final node) when node >= before =>
      '$path.$node: a node reads only nodes before it, and this is node $before',
    Out(:final node, :final port) when port >= r.nodes[node].outputs.length =>
      '$path.$node^$port: node $path.$node (`${r.nodes[node].op.title}`) has '
          '${_several(r.nodes[node].outputs.length, 'output')}, numbered from 0',
    _ => null,
  };
  if (why != null) throw ZirError('$at: $what: $why');
}

/// Checks node `n`, and leaves the checks of its regions on `todo`.
void _node(Region r, Node n, _Path at, bool inCertificate, List<void Function()> todo) {
  final name = n.op.title;
  if (inCertificate && n.op is DerivedOp) {
    throw ZirError('$at: `$name` in a certificate, which holds only kernel nodes');
  }
  final _Shape s;
  try {
    s = _shape(n);
  } on ZirError catch (e) {
    throw ZirError('$at: ${e.message}');
  }
  final ins = n.inputs.length;
  if (ins < s.fixed || (s.exact && ins != s.fixed)) {
    final more = s.exact ? '' : ' or more';
    throw ZirError('$at: `$name` takes ${_several(s.fixed, 'input')}$more, and has $ins');
  }
  if (s.outputs case final k? when n.outputs.length != k) {
    throw ZirError(
      '$at: `$name` has ${_several(k, 'output')}, and ${_written(n.outputs.length)} written',
    );
  }
  if (n.regions.length != s.regions.length) {
    throw ZirError(
      '$at: `$name` has ${_several(s.regions.length, 'region')}, and '
      '${_written(n.regions.length)} written',
    );
  }
  _edges(r, n, at, s.fixed);
  final captures = n.inputs.sublist(s.fixed);
  for (final (j, sub) in n.regions.indexed.toList().reversed) {
    final sp = _Path(at, '/$j');
    // A region's results stand for the node's outputs, kind for kind.
    todo.add(() {
      if (s.outputs != null) return;
      for (var i = 0; i < sub.results.length && i < n.outputs.length; i++) {
        final (got, out) = (sub.edge(sub.results[i]), n.outputs[i]);
        if (got.isState != out.isState || (out.isState && got != out)) {
          throw ZirError('$sp: result $i is $got, and output $i is $out');
        }
      }
    });
    todo.add(() => _subregion(n, s, j, sub, sp, captures, r, inCertificate, todo));
  }
}

/// Checks region `j` of node `n` against the node's shape, and leaves its own checks on
/// `todo`.
void _subregion(
  Node n,
  _Shape s,
  int j,
  Region sub,
  _Path sp,
  List<Src> captures,
  Region r,
  bool inCertificate,
  List<void Function()> todo,
) {
  final name = n.op.title;
  final (kind, lead, results) = s.regions[j];
  if (sub.kind != kind) {
    throw ZirError(
      '$sp: region $j of `$name` must be a ${kind.name} region, and is written '
      '`${sub.kind.name}`',
    );
  }
  if (sub.args.length != lead + captures.length) {
    final why = switch (n.op) {
      MatchOp(:final patterns) =>
        ' (the pattern `${text.pattern(patterns[j])}` binds ${_several(lead, 'name')})',
      _ => '',
    };
    throw ZirError(
      '$sp: the region takes ${_several(lead, 'argument')} from the node$why and '
      '${_several(captures.length, 'capture')}, ${lead + captures.length} in all, and has '
      '${sub.args.length}',
    );
  }
  for (final (i, c) in captures.indexed) {
    final (want, got) = (r.edge(c), sub.args[lead + i]);
    if (want != got) {
      throw ZirError('$sp^${lead + i}: capture $i is $want, and the argument is $got');
    }
  }
  if (sub.results.length != results) {
    throw ZirError(
      '$sp: the region must have ${_several(results, 'result')}, and '
      '${_written(sub.results.length)} written',
    );
  }
  _region(sub, sp, inCertificate || n.op is DerivedOp, n.op is LambdaOp, todo);
}

/// Checks which of a node's inputs and outputs are state edges; `fixed` is the number of its
/// inputs before the captures.
void _edges(Region r, Node n, _Path at, int fixed) {
  final name = n.op.title;
  switch (n.op) {
    case ReadOp(:final port) || PushOp(:final port):
      final first = r.edge(n.inputs[0]);
      if (first != StateEdge(port)) {
        throw ZirError('$at: input 0 of `$name` is $first, and must be `state $port`');
      }
      for (var i = 1; i < n.inputs.length; i++) {
        if (r.edge(n.inputs[i]).isState) throw ZirError('$at: input $i of `$name` is a state edge');
      }
      if (n.outputs[0].isState || n.outputs[1] != StateEdge(port)) {
        throw ZirError(
          '$at: `$name` has outputs (a value; state $port), and has '
          '(${n.outputs[0]}; ${n.outputs[1]})',
        );
      }
    case ApplyOp():
      final ins = [for (final s in n.inputs) r.edge(s)];
      var first = ins.indexWhere((e) => e.isState);
      if (first < 0) first = ins.length;
      if (first == 0) throw ZirError('$at: input 0 of `$name`, the function, is a state edge');
      for (var i = first; i < ins.length; i++) {
        if (!ins[i].isState) {
          throw ZirError(
            '$at: input $i of `$name` is a value after a state edge, and the states come after '
            'the arguments',
          );
        }
      }
      final outs = n.outputs;
      final states = ins.sublist(first);
      if (outs.isEmpty ||
          outs.first.isState ||
          outs.length - 1 != states.length ||
          Iterable<int>.generate(states.length).any((i) => outs[i + 1] != states[i])) {
        throw ZirError(
          '$at: `$name` has outputs (a value; ${states.join('; ')}), the states it takes, and '
          'has (${outs.join('; ')})',
        );
      }
    case final op:
      // State may pass through the region nodes that thread it; elsewhere edges carry values.
      final threads = op is IfOp || op is MatchOp || op is WaveOp;
      for (final (i, src) in n.inputs.indexed) {
        if (r.edge(src).isState && !(threads && i >= fixed)) {
          throw ZirError('$at: input $i of `$name` is a state edge');
        }
      }
      final p = n.outputs.indexWhere((e) => e.isState);
      if (!threads && p >= 0) throw ZirError('$at: output $p of `$name` is a state edge');
  }
}
