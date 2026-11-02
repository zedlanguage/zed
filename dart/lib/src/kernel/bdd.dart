part of 'types.dart';

// Reduced ordered binary decision diagrams over the types of one universe (DESIGN.md
// sec:type_language): the form of the tuple and morphism parts.
//
// A diagram is a leaf, no value of the universe or every value, or a node `(atom & hi) |
// (!atom & lo)`, with each atom smaller than every atom below it and `hi` and `lo` distinct.
// Two diagrams over one order of atoms denote one Boolean function of their atoms exactly when
// they are equal. The complement swaps the leaves, in time linear in the size of the diagram,
// and a union or intersection takes each pair of nodes at most once, in time the product of
// the two sizes: a union of clauses would make the complement of a union of `C` clauses of two
// types each a union of `2^C` clauses.
//
// Nodes are shared: every node is kept in one table, so that one atom with one pair of
// children is one node, and two equal diagrams are one object. Each node and expression keeps
// a hash of its contents made from its children's, and two are ordered by it first, so a
// comparison reads their contents only when the hashes are equal.
//
// A diagram is canonical, so some functions have only diagrams exponential in the number of
// their atoms: `(m1 & !n1) | … | (mC & !nC)`, with every `m` ordered before every `n`, has
// `2^C` nodes. A union or intersection therefore keeps its diagram only when it has no more
// nodes than its two operands together, and otherwise keeps the expression ([Expr]), built in
// constant time; so a diagram has no more nodes than the atoms written to build it.
//
// A part is decided (empty.dart) by three-valued operations, none of which walks paths, whose
// number can be exponential in the nodes. It is evaluated with some atoms known
// ([Part.eval3]) and restricted to them ([Part.restrict]), each in one pass over its nodes and
// expressions; settled on its shared subexpressions ([Part.settle]), one pass per shared
// subexpression in each round; and asked which atoms every value takes or refuses
// ([Part.forced]): for a diagram in time `O(n log n)` in its nodes, for an expression one pass
// per atom. Listing values takes one pass over the nodes ([Bdd.reaching]); [Bdd.walk] remains
// for display.

/// An atom of a diagram: a tuple type of one length, or a morphism type.
abstract interface class Literal<A> implements Comparable<A> {
  /// A hash of the atom, equal for equal atoms.
  int get digest;
}

/// A tuple part of one length, or the morphism part: a diagram, or, when a connective's diagram
/// would have more nodes than its operands together, the connective applied to its operands.
/// Diagrams order before expressions.
sealed class Part<A extends Literal<A>> implements Comparable<Part<A>> {
  const Part();

  /// The diagram of the one atom `a`.
  factory Part.literal(A a) => Bdd._node(a, Leaf<A>(true), Leaf<A>(false));

  /// The hash of the part's contents.
  int get digest;

  /// Whether the part is no value (false) or every value (true) as built; null otherwise.
  bool? get leaf => null;

  /// The complement.
  Part<A> operator ~();

  @override
  bool operator ==(Object other) => other is Part<A> && compareTo(other) == 0;

  @override
  int get hashCode => digest;

  /// The union (`or`) or intersection.
  Part<A> zip(Part<A> o, bool or) {
    // A leaf that absorbs is the result; a leaf that does not leaves the other operand.
    if (leaf == or) return this;
    if (o.leaf == or) return o;
    if (leaf != null) return o;
    if (o.leaf != null) return this;
    if ((this, o) case (final Bdd<A> a, final Bdd<A> b)) {
      if (Bdd._zip(a, b, or) case final r?) return r;
    }
    return Expr(or ? ExprOp.or : ExprOp.and, this, o);
  }

  /// The part's value on a set of values where `holds` gives each atom's: in every value
  /// (true), in none (false), or in some (null), by three-valued logic, each node and
  /// expression evaluated once. True or false is the part's value on every value of the set;
  /// null says nothing.
  bool? eval3(bool? Function(A) holds) => _eval3(holds, const {});

  /// [eval3], with each expression in `pins` taken to have the value beside it.
  bool? _eval3(bool? Function(A) holds, Map<Expr<A>, bool> pins) {
    final nodes = <int, bool?>{};
    final exprs = Map<Expr<A>, bool?>.identity()..addAll(pins);
    bool known(Part<A> p) => p is! Expr<A> || exprs.containsKey(p);
    bool? value(Part<A> p) => switch (p) {
      final Bdd<A> b => b._value3(holds, nodes),
      final Expr<A> e => exprs[e],
    };
    // Each expression is evaluated after its operands, on a stack of parts still to do.
    final stack = <Part<A>>[this];
    while (stack.isNotEmpty) {
      final p = stack.last;
      if (known(p)) {
        stack.removeLast();
        continue;
      }
      p as Expr<A>;
      final missing = [?p.b, p.a].where((q) => !known(q)).toList();
      if (missing.isNotEmpty) {
        stack.addAll(missing);
        continue;
      }
      stack.removeLast();
      final (x, y) = (value(p.a), p.b == null ? null : value(p.b!));
      exprs[p] = switch (p.op) {
        ExprOp.not => x == null ? null : !x,
        ExprOp.or => x == true || y == true ? true : (x == false && y == false ? false : null),
        ExprOp.and => x == false || y == false ? false : (x == true && y == true ? true : null),
      };
    }
    return value(this);
  }

  /// The part with each expression used more than once in it replaced by `true` when making
  /// it `false` makes the part `false` by three-valued logic, every atom unknown, and by
  /// `false` in the converse case, until no more is replaced. Every value of the part is in,
  /// or outside, such an expression, so the result holds every value of the part, and may
  /// hold more: it is empty only if the part is. Each round evaluates the part once per
  /// shared expression and replaces at least one, so the time is at most the square of the
  /// shared expressions times the size.
  Part<A> settle() {
    var p = this;
    while (true) {
      final uses = Map<Expr<A>, int>.identity();
      final stack = [p];
      while (stack.isNotEmpty) {
        if (stack.removeLast() case final Expr<A> e) {
          final n = uses[e] = (uses[e] ?? 0) + 1;
          if (n == 1) stack.addAll([?e.b, e.a]);
        }
      }
      final pins = Map<Expr<A>, bool>.identity();
      for (final MapEntry(key: e, value: n) in uses.entries) {
        if (n < 2) continue;
        for (final v in [true, false]) {
          pins[e] = !v;
          if (p._eval3((_) => null, pins) == false) {
            pins[e] = v;
            break;
          }
          pins.remove(e);
        }
      }
      if (pins.isEmpty) return p;
      p = p._map((b) => b, pins);
    }
  }

  /// The part with each atom that `fix` decides replaced by its value, each node and
  /// expression rebuilt once.
  Part<A> restrict(bool? Function(A) fix) {
    final nodes = <int, Bdd<A>>{};
    return _map((b) => b._restrict(fix, nodes), const {});
  }

  /// The part with each diagram replaced by `bdd` of it, and each expression in `pins` by its
  /// value, each expression rebuilt once, after its operands.
  Part<A> _map(Bdd<A> Function(Bdd<A>) bdd, Map<Expr<A>, bool> pins) {
    final memo = Map<Expr<A>, Part<A>>.identity();
    Part<A>? known(Part<A> p) => switch (p) {
      final Bdd<A> b => bdd(b),
      final Expr<A> e => pins[e] == null ? memo[e] : Leaf<A>(pins[e]!),
    };
    final stack = <Part<A>>[this];
    while (stack.isNotEmpty) {
      final p = stack.last;
      if (p is! Expr<A> || known(p) != null) {
        stack.removeLast();
        continue;
      }
      final missing = [?p.b, p.a].where((q) => known(q) == null).toList();
      if (missing.isNotEmpty) {
        stack.addAll(missing);
        continue;
      }
      stack.removeLast();
      memo[p] = p._rebuild((q) => known(q)!);
    }
    return known(this)!;
  }

  /// The atoms in every value of the part (`.$1`) and those in none (`.$2`), among the atoms
  /// in it: for a diagram, those taken or refused on every path to `true`; for an expression,
  /// each atom whose refusal, or whose taking, makes the part `false` by three-valued logic,
  /// one evaluation per atom.
  (List<A>, List<A>) forced() {
    if (this case final Bdd<A> b) return b._forced();
    final atoms = SplayTreeSet<A>((x, y) => x.compareTo(y));
    this.atoms((a) {
      atoms.add(a);
      return true;
    });
    final taken = <A>[], refused = <A>[];
    for (final a in atoms) {
      if (eval3((x) => x == a ? false : null) == false) {
        taken.add(a);
      } else if (eval3((x) => x == a ? true : null) == false) {
        refused.add(a);
      }
    }
    return (taken, refused);
  }

  /// Whether the value whose membership in each atom `holds` decides is in the part.
  bool eval(bool Function(A) holds) {
    final memo = Map<Expr<A>, bool>.identity();
    bool go(Part<A> p) => switch (p) {
      final Bdd<A> b => b._eval(holds),
      final Expr<A> e => memo[e] ??= switch (e.op) {
        ExprOp.not => !go(e.a),
        ExprOp.or => go(e.a) || go(e.b!),
        ExprOp.and => go(e.a) && go(e.b!),
      },
    };
    return go(this);
  }

  /// Whether `f` holds of every atom, each node and expression visited once.
  bool atoms(bool Function(A) f) {
    final nodes = <int>{};
    final exprs = Set<Expr<A>>.identity();
    // In preorder, `hi` before `lo`: the second branch is pushed first.
    final stack = <Part<A>>[this];
    while (stack.isNotEmpty) {
      switch (stack.removeLast()) {
        case Leaf():
          break;
        case Node(:final id, :final atom, :final hi, :final lo):
          if (!nodes.add(id)) break;
          if (!f(atom)) return false;
          stack
            ..add(lo)
            ..add(hi);
        case final Expr<A> e:
          if (!exprs.add(e)) break;
          stack.addAll([?e.b, e.a]);
      }
    }
    return true;
  }
}

/// The paths a test is asked of, one at a time: after each path is read from [asked], [held] is
/// set to whether the test holds of it, and once [asked] ends, [result] is whether it held of
/// every path. The lists of a path are valid until the next is read.
final class Paths<A extends Literal<A>> {
  Paths._();

  late final Iterable<(List<A>, List<A>)> asked;
  bool held = true;
  bool result = true;

  /// Whether `f` holds of every path, asked in turn.
  bool all(bool Function(List<A> pos, List<A> neg) f) {
    for (final (pos, neg) in asked) {
      held = f(pos, neg);
    }
    return result;
  }
}

/// A diagram: a [Leaf] or a [Node].
sealed class Bdd<A extends Literal<A>> extends Part<A> {
  const Bdd();

  /// The node's number in the table; 0 and 1 for the leaves.
  int get _id;

  static final _table = <(Object, int, int), Object>{};
  static var _next = 2;

  /// The node `(atom & hi) | (!atom & lo)`, shared with every equal one.
  static Bdd<A> _node<A extends Literal<A>>(A atom, Bdd<A> hi, Bdd<A> lo) {
    if (hi._id == lo._id) return hi;
    final key = (atom, hi._id, lo._id);
    return (_table[key] ??= Node<A>._(_next++, atom, hi, lo)) as Node<A>;
  }

  /// The union or intersection, or null when it would have more nodes than the two operands
  /// together.
  static Bdd<A>? _zip<A extends Literal<A>>(Bdd<A> a, Bdd<A> b, bool or) {
    final memo = <(int, int), Bdd<A>>{};
    final made = <int>{};
    final most = a._size + b._size;
    Bdd<A>? known(Bdd<A> x, Bdd<A> y) {
      // A leaf that absorbs is the result; a leaf that does not leaves the other operand.
      if (x.leaf case final v?) return v == or ? x : y;
      if (y.leaf case final v?) return v == or ? y : x;
      if (x._id == y._id) return x;
      return memo[(x._id, y._id)];
    }

    // The pairs to combine, each popped once both its cofactor pairs are combined. The `lo`
    // pair is pushed first, so the `hi` pair is combined first. A loop with its own stack, as
    // a diagram can be deeper than the call stack.
    final stack = [(a, b)];
    while (stack.isNotEmpty) {
      final (x, y) = stack.last;
      if (known(x, y) != null) {
        stack.removeLast();
        continue;
      }
      final (m, n) = (x as Node<A>, y as Node<A>);
      final c = m.atom.compareTo(n.atom);
      final (xh, xl) = c <= 0 ? (m.hi, m.lo) : (x, x);
      final (yh, yl) = c >= 0 ? (n.hi, n.lo) : (y, y);
      final hi = known(xh, yh), lo = known(xl, yl);
      if (hi == null || lo == null) {
        if (lo == null) stack.add((xl, yl));
        if (hi == null) stack.add((xh, yh));
        continue;
      }
      stack.removeLast();
      final r = _node(c <= 0 ? m.atom : n.atom, hi, lo);
      // The result's nodes are among those made by this union or intersection.
      if (r is Node<A> && made.add(r.id) && made.length > most) return null;
      memo[(x._id, y._id)] = r;
    }
    return known(a, b);
  }

  /// The number of nodes.
  int get _size {
    var n = 0;
    atoms((_) {
      n++;
      return true;
    });
    return n;
  }

  @override
  Bdd<A> operator ~() {
    final memo = <int, Bdd<A>>{};
    Bdd<A>? known(Bdd<A> b) => switch (b) {
      Leaf(:final value) => Leaf(!value),
      Node(:final id) => memo[id],
    };
    // The nodes to flip, each popped once both its branches are flipped, `hi` first.
    final stack = <Bdd<A>>[if (this is Node<A>) this];
    while (stack.isNotEmpty) {
      final n = stack.last as Node<A>;
      if (memo.containsKey(n.id)) {
        stack.removeLast();
        continue;
      }
      final hi = known(n.hi), lo = known(n.lo);
      if (hi == null || lo == null) {
        if (lo == null) stack.add(n.lo);
        if (hi == null) stack.add(n.hi);
        continue;
      }
      stack.removeLast();
      memo[n.id] = _node(n.atom, hi, lo);
    }
    return known(this)!;
  }

  /// Whether `f` holds of every path to the `true` leaf, given as the atoms it takes and those
  /// it refuses, in order, stopping at the first path where it does not. Below a node whose
  /// `hi` is `true` the `lo` path does not refuse the node's atom, since `a | (!a & L)` is
  /// `a | L`, so a union of atoms is a path per atom. With `prune`, `f` is also asked of each
  /// path's atoms taken so far with none refused, and the paths below are passed over when it
  /// holds: refusing more atoms only removes values, so if `f` holds of `pos` alone it holds of
  /// every path below.
  bool walk(bool prune, bool Function(List<A> pos, List<A> neg) f) => _walk(prune).all(f);

  /// The questions [walk] asks of `f`.
  Paths<A> _walk(bool prune) {
    final q = Paths<A>._();
    q.asked = _ask(q, prune);
    return q;
  }

  Iterable<(List<A>, List<A>)> _ask(Paths<A> q, bool prune) sync* {
    final pos = <A>[], neg = <A>[];
    // The nodes above the current one, each with whether its `lo` branch is being walked: a
    // loop with its own stack, as a diagram can be deeper than the call stack.
    final path = <(Node<A>, bool)>[];
    Bdd<A> lo(Node<A> n) {
      pos.removeLast();
      if (n.hi.leaf != true) neg.add(n.atom);
      path.add((n, true));
      return n.lo;
    }

    var b = this;
    while (true) {
      while (b is Node<A>) {
        final n = b;
        pos.add(n.atom);
        var held = false;
        if (prune && n.hi.leaf != false) {
          yield (pos, const []);
          held = q.held;
        }
        if (held) {
          b = lo(n);
        } else {
          path.add((n, false));
          b = n.hi;
        }
      }
      if (b.leaf!) {
        yield (pos, neg);
        if (!q.held) {
          q.result = false;
          return;
        }
      }
      while (true) {
        if (path.isEmpty) return;
        final (n, onLo) = path.removeLast();
        if (!onLo) {
          b = lo(n);
          break;
        }
        if (n.hi.leaf != true) neg.removeLast();
      }
    }
  }

  /// Whether `f` holds of each node's atom and state, for the nodes whose `hi` is not `false`.
  /// The root has the state `start`; an edge to a node's `hi` passes on `take` of its state and
  /// its atom, an edge to its `lo` its state; a node's state is `join` of the states of the
  /// edges into it. Each node is visited once, after every node with an edge into it, so the
  /// time is linear in the nodes however many paths there are.
  bool reaching<S>(
    S start,
    S Function(S, A) take,
    S Function(S, S) join,
    bool Function(A, S) f,
  ) {
    final root = this;
    if (root is! Node<A>) return true;
    // Nodes in reverse postorder of a depth-first walk: each after those above it.
    final order = <Node<A>>[];
    final seen = Set<Node<A>>.identity();
    final stack = [(root, false)];
    while (stack.isNotEmpty) {
      final (n, below) = stack.removeLast();
      if (below) {
        order.add(n);
        continue;
      }
      if (!seen.add(n)) continue;
      stack.add((n, true));
      for (final c in [n.lo, n.hi]) {
        if (c is Node<A> && !seen.contains(c)) stack.add((c, false));
      }
    }
    final state = Map<Node<A>, S>.identity()..[root] = start;
    for (final n in order.reversed) {
      final here = state.remove(n) as S;
      if (n.hi.leaf != false && !f(n.atom, here)) return false;
      for (final (child, s) in [(n.hi, take(here, n.atom)), (n.lo, here)]) {
        if (child is Node<A>) {
          state[child] = state.containsKey(child) ? join(state[child] as S, s) : s;
        }
      }
    }
    return true;
  }

  /// Whether the path that `holds` chooses at each atom ends at `true`.
  bool _eval(bool Function(A) holds) {
    var b = this;
    while (true) {
      switch (b) {
        case Leaf(:final value):
          return value;
        case Node(:final atom, :final hi, :final lo):
          b = holds(atom) ? hi : lo;
      }
    }
  }

  /// [Part.eval3] of the diagram, each node's value kept in `memo`.
  bool? _value3(bool? Function(A) holds, Map<int, bool?> memo) {
    bool known(Bdd<A> b) => b is! Node<A> || memo.containsKey(b.id);
    bool? value(Bdd<A> b) => switch (b) {
      Leaf(:final value) => value,
      Node(:final id) => memo[id],
    };
    // The nodes to evaluate, each popped once the branches it reads are evaluated.
    final stack = <Bdd<A>>[this];
    while (stack.isNotEmpty) {
      final b = stack.last;
      if (known(b)) {
        stack.removeLast();
        continue;
      }
      final n = b as Node<A>;
      final h = holds(n.atom);
      final (needHi, needLo) = (h != false && !known(n.hi), h != true && !known(n.lo));
      if (needHi || needLo) {
        if (needLo) stack.add(n.lo);
        if (needHi) stack.add(n.hi);
        continue;
      }
      stack.removeLast();
      memo[n.id] = switch (h) {
        true => value(n.hi),
        false => value(n.lo),
        null => value(n.hi) == value(n.lo) ? value(n.hi) : null,
      };
    }
    return value(this);
  }

  /// The diagram with each atom that `fix` decides replaced by its value, each node rebuilt
  /// once; `memo` holds the nodes rebuilt so far.
  Bdd<A> _restrict(bool? Function(A) fix, Map<int, Bdd<A>> memo) {
    Bdd<A>? known(Bdd<A> b) => b is Node<A> ? memo[b.id] : b;
    // The nodes to rebuild, each popped once the branches it keeps are rebuilt.
    final stack = <Bdd<A>>[this];
    while (stack.isNotEmpty) {
      final b = stack.last;
      if (known(b) != null) {
        stack.removeLast();
        continue;
      }
      final n = b as Node<A>;
      final v = fix(n.atom);
      final hi = v == false ? null : known(n.hi), lo = v == true ? null : known(n.lo);
      final (needHi, needLo) = (v != false && hi == null, v != true && lo == null);
      if (needHi || needLo) {
        if (needLo) stack.add(n.lo);
        if (needHi) stack.add(n.hi);
        continue;
      }
      stack.removeLast();
      memo[n.id] = switch (v) {
        true => hi!,
        false => lo!,
        null => _node(n.atom, hi!, lo!),
      };
    }
    return known(this)!;
  }

  /// [Part.forced] of a diagram: the atoms taken on every path to `true`, and those refused
  /// on every path, found as the branches that dominate the `true` leaf. The nodes that reach
  /// it are taken in topological order, and each branch between them is a vertex of its own;
  /// a vertex's dominator is the nearest common one of the vertices with an edge into it,
  /// found by binary lifting, so the time is `O(n log n)` in the nodes.
  (List<A>, List<A>) _forced() {
    final root = this;
    if (root is! Node<A>) return (<A>[], <A>[]);
    // The nodes that reach `true`, in postorder of a depth-first walk that takes `hi` first.
    final reaches = <int, bool>{};
    final entered = <int>{};
    final post = <Node<A>>[];
    bool reach(Bdd<A> b) => switch (b) {
      Leaf(:final value) => value,
      Node(:final id) => reaches[id]!,
    };
    final walk = [(root, false)];
    while (walk.isNotEmpty) {
      final (n, below) = walk.removeLast();
      if (below) {
        final r = reaches[n.id] = reach(n.hi) || reach(n.lo);
        if (r) post.add(n);
        continue;
      }
      if (!entered.add(n.id)) continue;
      walk.add((n, true));
      for (final c in [n.lo, n.hi]) {
        if (c is Node<A> && !entered.contains(c.id)) walk.add((c, false));
      }
    }
    if (post.isEmpty) return (<A>[], <A>[]);
    // Vertex 0 is the `true` leaf, 1 to `nodes.length` the nodes, root first, and then a
    // vertex per branch, with its node's vertex and whether it is the `hi` branch. Each vertex
    // has its dominator (-1 while none is known), its depth in the dominator tree, and its
    // ancestors there `2^i` steps up.
    final nodes = post.reversed.toList();
    final index = {for (var k = 0; k < nodes.length; k++) nodes[k].id: k + 1};
    final up = [-1, for (var k = 0; k < nodes.length; k++) k == 0 ? 1 : -1];
    final depth = List.filled(nodes.length + 1, 0, growable: true);
    final lift = List<List<int>>.filled(nodes.length + 1, const [], growable: true);
    final branch = List<(int, bool)?>.filled(nodes.length + 1, null, growable: true);
    List<int> ancestors(int p) {
      final l = [p];
      while (l.length - 1 < lift[l.last].length) {
        l.add(lift[l.last][l.length - 1]);
      }
      return l;
    }

    int meet(int a, int b) {
      if (depth[a] < depth[b]) (a, b) = (b, a);
      for (var (i, d) = (0, depth[a] - depth[b]); d > 0; i++, d >>= 1) {
        if (d & 1 != 0) a = lift[a][i];
      }
      if (a == b) return a;
      for (var i = lift[a].length - 1; i >= 0; i--) {
        if (i < lift[a].length && lift[a][i] != lift[b][i]) {
          (a, b) = (lift[a][i], lift[b][i]);
        }
      }
      return lift[a][0];
    }

    for (var k = 0; k < nodes.length; k++) {
      final u = k + 1;
      // Every edge into the node comes from a node before it, so its dominator is known.
      if (u != 1) {
        depth[u] = depth[up[u]] + 1;
        lift[u] = ancestors(up[u]);
      }
      for (final (child, v) in [(nodes[k].hi, true), (nodes[k].lo, false)]) {
        final c = switch (child) {
          Leaf(:final value) => value ? 0 : null,
          Node(:final id) => index[id],
        };
        if (c == null) continue;
        final e = up.length;
        up.add(u);
        depth.add(depth[u] + 1);
        lift.add(ancestors(u));
        branch.add((u, v));
        up[c] = up[c] == -1 ? e : meet(up[c], e);
      }
    }
    final taken = <A>[], refused = <A>[];
    for (var x = up[0]; x != 1; x = up[x]) {
      if (branch[x] case (final u, final v)) (v ? taken : refused).add(nodes[u - 1].atom);
    }
    return (taken, refused);
  }
}

/// No value of the universe, or every value.
final class Leaf<A extends Literal<A>> extends Bdd<A> {
  final bool value;

  const Leaf(this.value);

  @override
  int get _id => value ? 1 : 0;

  @override
  int get digest => mix(7, _id);

  @override
  bool get leaf => value;

  @override
  int compareTo(Part<A> o) => switch (o) {
    Leaf(:final value) => _cmpBool(this.value, value),
    _ => -1,
  };
}

/// `(atom & hi) | (!atom & lo)`.
final class Node<A extends Literal<A>> extends Bdd<A> {
  final int id;
  final A atom;
  final Bdd<A> hi, lo;

  @override
  final int digest;

  Node._(this.id, this.atom, this.hi, this.lo)
    : digest = mix(mix(atom.digest, hi.digest), lo.digest);

  @override
  int get _id => id;

  @override
  int compareTo(Part<A> o) {
    if (identical(this, o)) return 0;
    if (o is! Node<A>) return o is Leaf<A> ? 1 : -1;
    var c = _cmpDigest(digest, o.digest);
    if (c == 0) c = atom.compareTo(o.atom);
    if (c == 0) c = hi.compareTo(o.hi);
    if (c == 0) c = lo.compareTo(o.lo);
    return c;
  }
}

/// The connective of an [Expr], in the order expressions sort by.
enum ExprOp { not, or, and }

/// A connective kept unevaluated: `op` of `a`, and of `b` unless it is [ExprOp.not].
final class Expr<A extends Literal<A>> extends Part<A> {
  final ExprOp op;
  final Part<A> a;
  final Part<A>? b;

  @override
  final int digest;

  Expr(this.op, this.a, [this.b])
    : digest = switch (op) {
        ExprOp.not => mix(8, a.digest),
        ExprOp.or => mix(mix(9, a.digest), b!.digest),
        ExprOp.and => mix(mix(10, a.digest), b!.digest),
      };

  @override
  Part<A> operator ~() => op == ExprOp.not ? a : Expr(ExprOp.not, this);

  /// The connective applied again to `f` of each operand.
  Part<A> _rebuild(Part<A> Function(Part<A>) f) => switch (op) {
    ExprOp.not => ~f(a),
    ExprOp.or => f(a).zip(f(b!), true),
    ExprOp.and => f(a).zip(f(b!), false),
  };

  @override
  int compareTo(Part<A> o) {
    if (identical(this, o)) return 0;
    if (o is! Expr<A>) return 1;
    var c = _cmpDigest(digest, o.digest);
    if (c == 0) c = op.index - o.op.index;
    if (c == 0) c = a.compareTo(o.a);
    if (c == 0 && b != null) c = b!.compareTo(o.b!);
    return c;
  }
}
