// Provenance (step L1.20, DESIGN.md sec:keypaths): the fact address of every value a run
// computes, and the facts each one read.
//
// A fact is one node instance: a node of the term together with the instances of the regions
// around it (sec:kernel, the objects of the dependency theorem). Its address is the pair of a
// static [NodeAddress], code identity, and a dynamic keypath, data identity, and no two facts
// of a run share one. A run records its facts when the [Evaluator] is given a provenance root;
// the record is the run graph, each fact naming the facts it read.
part of 'eval.dart';

/// A persistent stack: pushing shares the stack below, so the addresses of the facts of a
/// recursion `n` calls deep share their call sites instead of copying `n` of them each.
final class _Link<T> {
  final T head;
  final _Link<T>? tail;
  final int length;

  _Link(this.head, this.tail) : length = (tail?.length ?? 0) + 1;
}

/// The items of `link`, bottom first.
List<T> _items<T>(_Link<T>? link) {
  final out = <T>[];
  for (var l = link; l != null; l = l.tail) {
    out.add(l.head);
  }
  return out.reversed.toList();
}

/// Whether two stacks of the same length hold the same positions; a shared tail is equal
/// without being walked.
bool _samePositions(_Link<int>? a, _Link<int>? b) {
  for (; a != null && b != null && !identical(a, b); a = a.tail, b = b.tail) {
    if (a.head != b.head) return false;
  }
  return true;
}

/// The static half of a fact address: the position of each call site through which the run
/// entered the function holding the node, and then the node's own position. A position is
/// the node's number in the preorder of the evaluated term. Only equality and order mean
/// anything; the numbers change with the build (sec:keypaths, the opaque token).
final class NodeAddress {
  final _Link<int> _link;

  NodeAddress._(this._link);

  /// The node's own position, the last.
  int get position => _link.head;

  /// How many positions: the call sites, then the node.
  int get length => _link.length;

  /// The call sites, then the node.
  late final List<int> positions = _items(_link);

  @override
  bool operator ==(Object other) =>
      other is NodeAddress && length == other.length && _samePositions(_link, other._link);

  @override
  int get hashCode => Object.hashAll(positions);

  @override
  String toString() => positions.join('/');
}

/// A fact address: (static node address, dynamic keypath). The keypath holds the wave stamp,
/// then each enclosing region's coordinate: a family key, a generation number, an iterate of
/// a lattice `fix`, the key of a definedness `fix` entry, the step of a `fold`.
final class FactAddress {
  /// The code identity.
  final NodeAddress node;
  final _Link<Value>? _keys;

  FactAddress._(this.node, this._keys);

  /// The data identity.
  late final List<Value> keypath = _items(_keys);

  @override
  bool operator ==(Object other) =>
      other is FactAddress && node == other.node && _samePath(keypath, other.keypath);

  @override
  int get hashCode => Object.hash(node, Object.hashAll(keypath));

  @override
  String toString() => '$node@(${keypath.join(', ')})';
}

/// One node instance of a run.
final class Fact {
  /// Where it is.
  final FactAddress address;

  /// Its value; null for a function.
  final Value? value;

  /// The facts it read, by index into [Provenance.facts], in the order it read them.
  final List<int> inputs;

  Fact._(this.address, this.value, this.inputs);
}

/// The run graph of one evaluation: its facts, each after the facts it read.
final class Provenance {
  final Term _term;

  /// Every fact, in the order the run completed them.
  final List<Fact> facts;

  Provenance._(this._term, this.facts);

  /// The fact the run's result came from, the last one completed.
  int get result => facts.length - 1;

  /// The term at `node`'s position. It walks the term to the position, so the terms of many
  /// facts are read from [terms].
  Term term(NodeAddress node) => _preorder().elementAt(node.position);

  /// The term at each position, in one walk: `terms()[f.address.node.position]`.
  List<Term> terms() => _preorder().toList();

  Iterable<Term> _preorder() sync* {
    final stack = [_term];
    while (stack.isNotEmpty) {
      final t = stack.removeLast();
      stack.addAll(_children(t).reversed);
      yield t;
    }
  }

  /// The addresses held by more than one fact; a correct run has none (sec:keypaths, one
  /// writer per fact address).
  List<FactAddress> repeated() {
    final seen = <FactAddress>{};
    return [
      for (final f in facts)
        if (!seen.add(f.address)) f.address,
    ];
  }

  /// The origins of the failure that fact `i` holds, in index order: for each distinct
  /// failure, the facts where it first appeared, so a merged `#errs` keeps the origins of all
  /// its operands rather than a winner (sec:failure). A failure first appears at a fact none
  /// of whose inputs holds it. Empty when the fact holds no failure.
  SplayTreeSet<int> origins(int i) {
    final out = SplayTreeSet<int>();
    final v = facts[i].value;
    if (v is! Atom) return out;
    final members = SplayTreeSet<Value>.of(v.errs?.keys ?? [v]);
    // The members each fact reached holds, its value walked once: each member's search walked
    // every value it tested, an `#errs` of up to all the members.
    final held = <int, Set<Value>>{};
    for (final m in members) {
      final stack = [i], seen = <int>{};
      while (stack.isNotEmpty) {
        final j = stack.removeLast();
        if (!seen.add(j)) continue;
        final from = [
          for (final k in facts[j].inputs)
            if (held.putIfAbsent(k, () => _holds(facts[k].value, members)).contains(m)) k,
        ];
        if (from.isEmpty) out.add(j);
        stack.addAll(from);
      }
    }
    return out;
  }
}

/// The failures of `members` that `v` holds: that `v` is, has as a member of an `#errs`, or
/// holds in a tuple, a family or a payload.
Set<Value> _holds(Value? v, Set<Value> members) {
  final found = <Value>{};
  void walk(Value v) {
    if (members.contains(v)) found.add(v);
    switch (v) {
      case Atom(:final args):
        args.forEach(walk);
      case Tuple(items: final xs) || Path(keys: final xs):
        xs.forEach(walk);
      case Family():
        for (final (_, x) in v.entries) {
          walk(x);
        }
      default:
    }
  }

  if (v != null) walk(v);
  return found;
}

/// The subterms of a term in the order that numbers the positions.
List<Term> _children(Term t) => switch (t) {
  Lit() || Var() || PrimFn() || Read() => const [],
  Lam(:final body) => [body],
  App(:final f, :final args) => [f, ...args],
  PrimApp(:final args) => args,
  Let(:final value, :final body) => [value, body],
  If(:final cond, :final then, :final orElse) => [cond, then, orElse],
  Match(:final scrutinee, :final arms) => [scrutinee, for (final (_, b) in arms) b],
  Fam(:final domain, :final body) => [domain, body],
  Reindex(:final family, :final kf, :final vf) => [family, kf, vf],
  Discard(:final family, :final sel) => [family, sel],
  Fold(:final family, :final op, :final identity) => [family, op, ?identity],
  Fix(:final init, :final step, kind: Lattice(:final join)) => [init, step, join],
  Fix(:final init, :final step) => [init, step],
  Gen(:final init, :final step, :final guard) => [init, step, guard],
  Push(:final value) => [value],
};

/// A copy of `t` in which every node is a distinct object: a position is keyed by a node's
/// identity while the run lasts, and a term may hold one node, a constant among them, at
/// several places.
Term _unshare(Term t) {
  List<Term> all(List<Term> ts) => [for (final t in ts) _unshare(t)];
  return switch (t) {
    Lit(:final value) => Lit(value),
    Var(:final name) => Var(name),
    PrimFn(:final prim) => PrimFn(prim),
    Read(:final port) => Read(port),
    Lam(:final params, :final body) => Lam(params, _unshare(body)),
    App(:final f, :final args) => App(_unshare(f), all(args)),
    PrimApp(:final prim, :final args) => PrimApp(prim, all(args)),
    Let(:final name, :final value, :final body) => Let(name, _unshare(value), _unshare(body)),
    If(:final cond, :final then, :final orElse) => If(
      _unshare(cond),
      _unshare(then),
      _unshare(orElse),
    ),
    Match(:final scrutinee, :final arms) => Match(_unshare(scrutinee), [
      for (final (p, b) in arms) (p, _unshare(b)),
    ]),
    Fam(:final domain, :final variable, :final body) => Fam(
      _unshare(domain),
      variable,
      _unshare(body),
    ),
    Reindex(:final family, :final kf, :final vf, :final witness) => Reindex(
      _unshare(family),
      _unshare(kf),
      _unshare(vf),
      witness,
    ),
    Discard(:final family, :final sel) => Discard(_unshare(family), _unshare(sel)),
    Fold(:final family, :final op, :final identity, :final depth, :final ev) => Fold(
      _unshare(family),
      _unshare(op),
      identity == null ? null : _unshare(identity),
      depth,
      ev,
    ),
    Fix(:final init, :final step, :final self, :final key, :final kind, :final ev) => Fix(
      _unshare(init),
      _unshare(step),
      self,
      key,
      switch (kind) {
        Lattice(:final join) => Lattice(_unshare(join)),
        Definedness() => kind,
      },
      ev,
    ),
    Gen(:final init, :final step, :final guard, :final pos) => Gen(
      _unshare(init),
      _unshare(step),
      _unshare(guard),
      pos,
    ),
    Push(:final port, :final value) => Push(port, _unshare(value)),
  };
}
