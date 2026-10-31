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
// constant time; so a diagram has no more nodes than the atoms written to build it. An
// expression is decided by its paths ([Part.paths]): its Shannon expansion on the smallest
// atom at its top, each step taking the cofactors of its operands, each operand once.
// Emptiness of these Boolean combinations is coNP-hard, so the number of paths can be
// exponential in the atoms; the walk holds one path at a time, and no count of nodes or paths
// stops it.

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

  /// Whether `f` holds of every path of the part to `true`, as [Bdd.walk] gives them with
  /// `prune`, stopping at the first path where it does not; `f` must hold of a path whenever it
  /// holds of one that takes a subset of its atoms and refuses a subset of its atoms. An
  /// expression is first expanded on a subexpression it shares between two operands: it is
  /// `x & e[x := true] | !x & e[x := false]`, and the two cofactors are built again from their
  /// operands, so a part like `b & !(b | a)` is `false` at once. Each expansion leaves one fewer
  /// shared subexpression. An expression that shares none is expanded on the smallest atom at
  /// the top of any of its diagrams, its cofactors being its operands' cofactors combined
  /// again.
  bool paths(bool Function(List<A> pos, List<A> neg) f) {
    final pos = <A>[], neg = <A>[];
    bool go(Part<A> p) {
      if (p is Bdd<A>) {
        // The diagram's own walk, after the atoms taken and refused so far.
        return p.walk(true, (bp, bn) => f([...pos, ...bp], [...neg, ...bn]));
      }
      if (p._shared() case final x?) {
        return [true, false].every((v) {
          final rest = p._substitute(x, v, Map.identity());
          final side = v ? x : ~x;
          return go(side.zip(rest, false));
        });
      }
      final a = p._top();
      // An expression of leaves alone is a constant.
      if (a == null) return !p.eval((_) => false) || f(pos, neg);
      final hi = p._cofactor(a, true, Map.identity());
      pos.add(a);
      final r = hi.leaf == false || f(pos, const []) || go(hi);
      pos.removeLast();
      if (!r) return false;
      final lo = p._cofactor(a, false, Map.identity());
      final refuse = hi.leaf != true;
      if (refuse) neg.add(a);
      final l = go(lo);
      if (refuse) neg.removeLast();
      return l;
    }

    return go(this);
  }

  /// An expression that is an operand of two connectives in the part, if any: the first met
  /// from the root, so the largest.
  Expr<A>? _shared() {
    final seen = Map<Expr<A>, int>.identity();
    void count(Part<A> p) {
      if (p is! Expr<A>) return;
      final n = seen[p] = (seen[p] ?? 0) + 1;
      if (n == 1) {
        count(p.a);
        if (p.b case final b?) count(b);
      }
    }

    final done = Set<Expr<A>>.identity();
    Expr<A>? find(Part<A> p) {
      if (p is! Expr<A>) return null;
      if (seen[p]! > 1) return p;
      if (!done.add(p)) return null;
      return find(p.a) ?? (p.b == null ? null : find(p.b!));
    }

    count(this);
    return find(this);
  }

  /// The part with the expression `x` replaced by the leaf `v`, each expression rebuilt once.
  Part<A> _substitute(Expr<A> x, bool v, Map<Expr<A>, Part<A>> memo) {
    final e = this;
    if (e is! Expr<A>) return e;
    if (identical(e, x)) return Leaf<A>(v);
    return memo[e] ??= e._rebuild((p) => p._substitute(x, v, memo));
  }

  /// The smallest atom at the top of a diagram in the part, each expression visited once.
  A? _top() {
    final seen = Set<Expr<A>>.identity();
    A? best;
    void go(Part<A> p) {
      switch (p) {
        case Leaf():
          break;
        case Node(:final atom):
          if (best == null || atom.compareTo(best as A) < 0) best = atom;
        case Expr(:final a, :final b):
          if (seen.add(p)) {
            go(a);
            if (b != null) go(b);
          }
      }
    }

    go(this);
    return best;
  }

  /// The part with `a` taken (`v`) or refused, for `a` no larger than any atom in it, each
  /// expression rebuilt once.
  Part<A> _cofactor(A a, bool v, Map<Expr<A>, Part<A>> memo) => switch (this) {
    Node(:final atom, :final hi, :final lo) when atom.compareTo(a) == 0 => v ? hi : lo,
    Bdd() => this,
    final Expr<A> e => memo[e] ??= e._rebuild((p) => p._cofactor(a, v, memo)),
  };

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
    bool go(Part<A> p) => switch (p) {
      Leaf() => true,
      Node(:final id, :final atom, :final hi, :final lo) =>
        !nodes.add(id) || (f(atom) && go(hi) && go(lo)),
      Expr(:final a, :final b) => !exprs.add(p) || (go(a) && (b == null || go(b))),
    };
    return go(this);
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
    Bdd<A>? apply(Bdd<A> x, Bdd<A> y) {
      // A leaf that absorbs is the result; a leaf that does not leaves the other operand.
      if (x.leaf case final v?) return v == or ? x : y;
      if (y.leaf case final v?) return v == or ? y : x;
      if (x._id == y._id) return x;
      final key = (x._id, y._id);
      if (memo[key] case final r?) return r;
      final (m, n) = (x as Node<A>, y as Node<A>);
      final c = m.atom.compareTo(n.atom);
      final Bdd<A> r;
      if (c == 0) {
        final hi = apply(m.hi, n.hi);
        if (hi == null) return null;
        final lo = apply(m.lo, n.lo);
        if (lo == null) return null;
        r = _node(m.atom, hi, lo);
      } else if (c < 0) {
        final hi = apply(m.hi, y);
        if (hi == null) return null;
        final lo = apply(m.lo, y);
        if (lo == null) return null;
        r = _node(m.atom, hi, lo);
      } else {
        final hi = apply(x, n.hi);
        if (hi == null) return null;
        final lo = apply(x, n.lo);
        if (lo == null) return null;
        r = _node(n.atom, hi, lo);
      }
      // The result's nodes are among those made by this union or intersection.
      if (r is Node<A> && made.add(r.id) && made.length > most) return null;
      return memo[key] = r;
    }

    return apply(a, b);
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
    Bdd<A> flip(Bdd<A> b) => switch (b) {
      Leaf(:final value) => Leaf(!value),
      Node(:final id, :final atom, :final hi, :final lo) => memo[id] ??= _node(
        atom,
        flip(hi),
        flip(lo),
      ),
    };
    return flip(this);
  }

  /// Whether `f` holds of every path to the `true` leaf, given as the atoms it takes and those
  /// it refuses, in order, stopping at the first path where it does not. Below a node whose
  /// `hi` is `true` the `lo` path does not refuse the node's atom, since `a | (!a & L)` is
  /// `a | L`, so a union of atoms is a path per atom. With `prune`, `f` is also asked of each
  /// path's atoms taken so far with none refused, and the paths below are passed over when it
  /// holds: refusing more atoms only removes values, so if `f` holds of `pos` alone it holds of
  /// every path below.
  bool walk(bool prune, bool Function(List<A> pos, List<A> neg) f) {
    final pos = <A>[], neg = <A>[];
    bool go(Bdd<A> b) {
      final Node<A> n;
      switch (b) {
        case Leaf(value: false):
          return true;
        case Leaf(value: true):
          return f(pos, neg);
        case final Node<A> node:
          n = node;
      }
      pos.add(n.atom);
      final hi = (prune && n.hi.leaf != false && f(pos, const [])) || go(n.hi);
      pos.removeLast();
      if (!hi) return false;
      final refuse = n.hi.leaf != true;
      if (refuse) neg.add(n.atom);
      final lo = go(n.lo);
      if (refuse) neg.removeLast();
      return lo;
    }

    return go(this);
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
