/// The canonicalizer on ZIR (step L1.32): the four rules of step M0.7, moved onto the graph
/// unchanged, and the content address taken over the normal form.
///
/// A graph has no local names but one kind: a match pattern's binders, whose written names a
/// region reads by position, never by name. So the *binders* rule renames the first written
/// pattern binder in preorder to its level, its index among the binders of its pattern, which
/// is the number of the arm region's arguments before the one it binds; its written name
/// becomes a hint facet `binder (index, name)` on that argument's edge. The *hints*, *facets*
/// and *domain* rules are the M0.7 rules themselves, applied to one edge at a time, the edges
/// taken in preorder: a region's arguments, then each node's outputs and then its regions, in
/// order. Each rule applies at the first place it applies, in priority order, until none
/// applies; the ranks are the sums of the per-edge ranks, and the tuple of them decreases
/// lexicographically at every step, as it does on kernel terms.
///
/// The address is the BLAKE3-256 hash of `zed-zir\0`, the rule set's version, and the binary
/// form of the normal form. Two graphs that differ only in binder names, hints, facet order
/// or repeats, or the spelling of one set of integers, share it.
///
/// Every rule acts on one edge, or on one pattern, alone, and the binder rule's hint is
/// removed by the hints rule. So [canonicalize] normalizes each edge and each pattern in one
/// pass and reaches the normal form that [step] reaches, in time linear in the graph; and
/// [key] hashes a node from the keys of its regions, so the lowering keys each new node
/// without walking the regions below it again. Every walk keeps its own stack, since regions
/// may nest deeper than the call stack.
library;

import 'dart:convert';
import 'dart:typed_data';

import '../../address.dart';
import '../canon/binders.dart' show levelName, levelOf;
import '../canon/blake3.dart';
import '../canon/canon.dart' as canon show Def, Facet, canonicalize, rules, version;
import '../kernel/term.dart';
import '../kernel/value.dart';
import 'binary.dart' as binary;
import 'graph.dart';

/// The ranks of the four rules on `g`, in rule order.
List<int> ranks(Region g) {
  final r = [_fold<int>(g, _written), 0, 0, 0];
  for (final x in _preorder(g)) {
    for (final e in _edges(x)) {
      if (e is ValueEdge) {
        final d = _def(e);
        for (var k = 1; k < r.length; k++) {
          r[k] += canon.rules[k].rank(d);
        }
      }
    }
  }
  return r;
}

/// One rewrite: the first rule that applies anywhere, applied at the first place it applies.
/// Returns the rewritten graph and the rule's name, or null when `g` is in normal form.
(Region, String)? step(Region g) {
  for (final x in _preorder(g)) {
    if (x case Node(op: MatchOp(:final patterns))) {
      for (var arm = 0; arm < patterns.length; arm++) {
        final index = [0];
        final (p, name) = _renameFirst(patterns[arm], index);
        if (name == null) continue;
        final hint = canon.Facet('binder', Tuple([Int(index[0]), Str(name)]), hint: true);
        return (
          _replace(g, x, (n) {
            final n0 = n as Node;
            final r = n0.regions[arm];
            final args = [...r.args];
            if (args[index[0]] case final ValueEdge v) {
              args[index[0]] = ValueEdge(v.type, domain: v.domain, facets: [...v.facets, hint]);
            }
            return Node(
              MatchOp([...patterns]..[arm] = p),
              n0.inputs,
              n0.outputs,
              [...n0.regions]..[arm] = Region(r.kind, args, r.nodes, r.results),
            );
          }),
          canon.rules[0].name,
        );
      }
    }
  }
  for (final rule in canon.rules.skip(1)) {
    for (final x in _preorder(g)) {
      final edges = _edges(x);
      for (var i = 0; i < edges.length; i++) {
        if (edges[i] case final ValueEdge v) {
          final d = _def(v);
          if (!rule.apply(d)) continue;
          final e = ValueEdge(v.type, domain: d.domain, facets: d.facets);
          return (
            _replace(
              g,
              x,
              (y) => switch (y) {
                Region r => Region(r.kind, [...r.args]..[i] = e, r.nodes, r.results),
                Node n => Node(n.op, n.inputs, [...n.outputs]..[i] = e, n.regions),
                _ => throw StateError('a region or a node'),
              },
            ),
            rule.name,
          );
        }
      }
    }
  }
  return null;
}

/// The normal form of `g`: the graph [step] reaches, in one pass.
Region canonicalize(Region g) => _fold<Region>(
  g,
  (r, inner) => Region(
    r.kind,
    [for (final e in r.args) _normalEdge(e)],
    [for (var k = 0; k < r.nodes.length; k++) _normalShell(r.nodes[k], inner[k])],
    r.results,
  ),
);

/// Node `n` with the regions `regions`, its operation and outputs in normal form.
Node _normalShell(Node n, List<Region> regions) => Node(
  switch (n.op) {
    MatchOp(:final patterns) => MatchOp([
      for (final p in patterns) _renameAll(p, [0]),
    ]),
    final op => op,
  },
  n.inputs,
  [for (final e in n.outputs) _normalEdge(e)],
  regions,
);

/// An edge in normal form.
Edge _normalEdge(Edge e) => switch (e) {
  ValueEdge(:final type) => () {
    final d = canon.canonicalize(_def(e));
    return ValueEdge(type, domain: d.domain, facets: d.facets);
  }(),
  StateEdge() => e,
};

/// Each written binder of `p` renamed to its level, the number of binders before it, counted
/// in `index`.
Pattern _renameAll(Pattern p, List<int> index) => switch (p) {
  BindP(:final name) => BindP(switch (index[0]++) {
    final i when levelOf(name) == null => levelName(i),
    _ => name,
  }),
  AtomP(:final name, :final args) => AtomP(name, [for (final q in args) _renameAll(q, index)]),
  TupleP(:final items) => TupleP([for (final q in items) _renameAll(q, index)]),
  FieldsP(:final name, :final fields) => FieldsP(name, [
    for (final (f, q) in fields) (f, _renameAll(q, index)),
  ]),
  WildP() || LitP() || AnyAtomP() || IsP() => p,
};

/// `p` with its first written binder renamed to its level, counting in `index` the binders
/// before it, and the binder's written name; the name is null when `p` has no written binder.
(Pattern, String?) _renameFirst(Pattern p, List<int> index) {
  (List<Pattern>, String?) first(List<Pattern> ps) {
    for (var i = 0; i < ps.length; i++) {
      final (q, name) = _renameFirst(ps[i], index);
      if (name != null) return ([...ps]..[i] = q, name);
    }
    return (ps, null);
  }

  switch (p) {
    case BindP(:final name) when levelOf(name) == null:
      return (BindP(levelName(index[0])), name);
    case BindP():
      index[0]++;
      return (p, null);
    case AtomP(:final name, :final args):
      final (qs, written) = first(args);
      return (AtomP(name, qs), written);
    case TupleP(:final items):
      final (qs, written) = first(items);
      return (TupleP(qs), written);
    case FieldsP(:final name, :final fields):
      final (qs, written) = first([for (final (_, q) in fields) q]);
      return (FieldsP(name, [for (var i = 0; i < qs.length; i++) (fields[i].$1, qs[i])]), written);
    case WildP() || LitP() || AnyAtomP() || IsP():
      return (p, null);
  }
}

/// The key of node `n` whose regions have the keys `regions`: equal keys mean equal normal
/// forms of the one-node regions holding the nodes (up to the hash).
ContentAddress nodeKey(Node n, List<ContentAddress> regions) {
  final shell = _normalShell(n, const []);
  final b = BytesBuilder(copy: false)
    ..add(utf8.encode('zed-zir-node\u0000'))
    ..add(_u32(canon.version))
    ..add(binary.encode(Region(RegionKind.function, const [], [shell], const [])))
    ..add(_u64(regions.length));
  for (final r in regions) {
    b.add(r.bytes);
  }
  return ContentAddress(blake3(b.takeBytes()));
}

/// The key of region `r` whose nodes' regions have the keys `inner`, one list per node.
ContentAddress regionKey(Region r, List<List<ContentAddress>> inner) {
  final shell = Region(r.kind, [for (final e in r.args) _normalEdge(e)], const [], r.results);
  final b = BytesBuilder(copy: false)
    ..add(utf8.encode('zed-zir-region\u0000'))
    ..add(_u32(canon.version))
    ..add(binary.encode(shell))
    ..add(_u64(r.nodes.length));
  for (var k = 0; k < r.nodes.length; k++) {
    b.add(nodeKey(r.nodes[k], inner[k]).bytes);
  }
  return ContentAddress(blake3(b.takeBytes()));
}

/// The key of `g` from the bottom up: what [regionKey] gives with every region's key.
ContentAddress key(Region g) => _fold<ContentAddress>(g, regionKey);

/// The content address of `g`.
ContentAddress address(Region g) => ContentAddress(
  blake3(
    (BytesBuilder(copy: false)
          ..add(utf8.encode('zed-zir\u0000'))
          ..add(_u32(canon.version))
          ..add(binary.encode(canonicalize(g))))
        .takeBytes(),
  ),
);

/// An edge's facts as the M0.7 rules see a definition: no name and no body.
canon.Def _def(ValueEdge v) =>
    canon.Def('', const Lit(Tuple([])), domain: v.domain, facets: [...v.facets]);

/// The pattern binders of region `r` that still carry their written names, given the counts
/// `inner` of its nodes' regions.
int _written(Region r, List<List<int>> inner) {
  var n = 0;
  for (var k = 0; k < r.nodes.length; k++) {
    if (r.nodes[k].op case MatchOp(:final patterns)) {
      for (final p in patterns) {
        n += _names(p).where((name) => levelOf(name) == null).length;
      }
    }
    n += inner[k].fold(0, (a, b) => a + b);
  }
  return n;
}

/// The binder names of `p`, in preorder.
Iterable<String> _names(Pattern p) sync* {
  switch (p) {
    case BindP(:final name):
      yield name;
    case AtomP(args: final ps) || TupleP(items: final ps):
      for (final q in ps) {
        yield* _names(q);
      }
    case FieldsP(:final fields):
      for (final (_, q) in fields) {
        yield* _names(q);
      }
    case WildP() || LitP() || AnyAtomP() || IsP():
  }
}

/// The edges a preorder item holds: a region's arguments or a node's outputs.
List<Edge> _edges(Object x) => x is Region ? x.args : (x as Node).outputs;

/// The regions and nodes of `g` in preorder: a region, then each of its nodes followed by the
/// node's regions.
Iterable<Object> _preorder(Region g) sync* {
  final todo = <Object>[g];
  while (todo.isNotEmpty) {
    final x = todo.removeLast();
    yield x;
    todo.addAll(x is Region ? x.nodes.reversed : (x as Node).regions.reversed);
  }
}

/// The value `f` gives `g`, computed from the bottom up: `f` takes a region and, for each of
/// its nodes, the values of the node's regions.
R _fold<R>(Region g, R Function(Region, List<List<R>>) f) {
  final stack = [_Frame<R>(g)];
  while (true) {
    final top = stack.last;
    if (top.node < top.region.nodes.length) {
      final n = top.region.nodes[top.node];
      if (top.inner.length == top.node) top.inner.add([]);
      final done = top.inner[top.node];
      if (done.length < n.regions.length) {
        stack.add(_Frame(n.regions[done.length]));
      } else {
        top.node++;
      }
      continue;
    }
    final v = f(top.region, top.inner);
    stack.removeLast();
    if (stack.isEmpty) return v;
    stack.last.inner[stack.last.node].add(v);
  }
}

/// A region whose value [_fold] is computing, and the values of its nodes' regions so far.
final class _Frame<R> {
  final Region region;
  final inner = <List<R>>[];
  var node = 0;

  _Frame(this.region);
}

/// `g` with the region or node `at`, rebuilt with its new regions, replaced by `change` of it.
Region _replace(Region g, Object at, Object Function(Object) change) =>
    _fold<Region>(g, (r, inner) {
      final nodes = [
        for (var k = 0; k < r.nodes.length; k++)
          () {
            final n = r.nodes[k];
            final m = Node(n.op, n.inputs, n.outputs, inner[k]);
            return identical(n, at) ? change(m) as Node : m;
          }(),
      ];
      final out = Region(r.kind, r.args, nodes, r.results);
      return identical(r, at) ? change(out) as Region : out;
    });

Uint8List _u32(int n) => (ByteData(4)..setUint32(0, n, Endian.little)).buffer.asUint8List();

Uint8List _u64(int n) => (ByteData(8)..setUint64(0, n, Endian.little)).buffer.asUint8List();
