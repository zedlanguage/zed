/// The store's cells (DESIGN.md sec:domains, the engine paragraph; step L1.24).
///
/// Every fact address owns a cell, and the cell holds one element per domain, each with the
/// premises it rests on. A premise is a written constraint, a declared type or a narrowing test,
/// named by its fact address, or a widening that gave more than the join at a component head.
/// A cell's premise set is its certificate (sec:constraints), and an element that rests on a
/// widening is not proof-grade evidence (sec:property_tracking).
///
/// An entry's premises change with its element. A meet that narrows the element adds the
/// premises of what it met with; a meet that changes nothing adds none, since the element did
/// not need it. A join adds the premises of both sides, since the joined element holds only if
/// each side does. A widening joins, and adds the widening as a premise when it gives more
/// than the join.
///
/// A premise set is [Premises], which shares what two sets have in common: a union takes
/// constant time, so a chain of `k` narrowings costs `O(k)` and not `O(k²)` (the rule of low
/// complexity, DESIGN.md Part G). The set itself is built only when it is read.
///
/// The domains here are those of step L1.24: intervals with symbolic affine bounds,
/// congruences, finite sets of scalars and atoms, float classes and lengths. The cell's type,
/// linear relations and binding time join it, with the reduction between its domains, at step
/// L1.39.
library;

import 'dart:collection';

import '../kernel/eval.dart' show FactAddress;
import '../kernel/value.dart';
import 'affine.dart';
import 'float.dart';
import 'interval.dart';
import 'lattice.dart';

/// What an element rests on: a written constraint, a declared type or a narrowing test at an
/// address, or the widening at the component head with that address, which gave more than the
/// join. Constraints come before widenings, each in address order.
final class Premise implements Comparable<Premise> {
  final FactAddress address;
  final bool widened;

  const Premise.constraint(this.address) : widened = false;

  const Premise.widened(this.address) : widened = true;

  @override
  int compareTo(Premise other) =>
      widened != other.widened ? (widened ? 1 : -1) : address.compareTo(other.address);

  @override
  bool operator ==(Object other) =>
      other is Premise && other.widened == widened && other.address == address;

  @override
  int get hashCode => Object.hash(widened, address);

  @override
  String toString() => '${widened ? 'Widened' : 'Constraint'}($address)';
}

/// A set of premises whose union takes constant time: a set is one premise, or the union of
/// two sets it shares with whatever else holds them.
final class Premises {
  final _Node? _node;

  const Premises._(this._node);

  /// The empty set.
  static const empty = Premises._(null);

  /// The set of `p` alone.
  Premises.one(Premise p) : _node = _One(p);

  /// The set of `ps`.
  factory Premises.of(Iterable<Premise> ps) => ps.fold(empty, (a, p) => a.union(Premises.one(p)));

  /// Whether the set is empty.
  bool get isEmpty => _node == null;

  /// Whether a premise of the set is a widening.
  bool get widened => _node?.widened ?? false;

  /// Every premise of `this` and of `other`, in constant time.
  Premises union(Premises other) => switch ((_node, other._node)) {
    (_, null) => this,
    (null, _) => other,
    (final a?, final b?) when identical(a, b) => this,
    (final a?, final b?) => Premises._(_Both(a, b)),
  };

  /// The premises, each once, in order. It visits each shared part once.
  SplayTreeSet<Premise> get set {
    final out = SplayTreeSet<Premise>();
    final seen = HashSet<_Node>.identity();
    final todo = [?_node];
    while (todo.isNotEmpty) {
      final n = todo.removeLast();
      if (!seen.add(n)) continue;
      switch (n) {
        case _One(:final p):
          out.add(p);
        case _Both(:final a, :final b):
          todo.addAll([a, b]);
      }
    }
    return out;
  }

  /// Whether `p` is a premise of the set.
  bool contains(Premise p) => set.contains(p);

  /// The same premises: at once when both are the same shared set or one is empty.
  @override
  bool operator ==(Object other) {
    if (other is! Premises) return false;
    final (a, b) = (_node, other._node);
    if (a == null || b == null) return a == b;
    if (identical(a, b)) return true;
    final (x, y) = (set, other.set);
    return x.length == y.length && x.containsAll(y);
  }

  @override
  int get hashCode => Object.hashAllUnordered(set);

  @override
  String toString() => '{${set.join(', ')}}';
}

sealed class _Node {
  /// Whether a premise of the set is a widening.
  final bool widened;

  _Node(this.widened);
}

final class _One extends _Node {
  final Premise p;

  _One(this.p) : super(p.widened);
}

final class _Both extends _Node {
  final _Node a, b;

  _Both(this.a, this.b) : super(a.widened || b.widened);
}

/// An element and the premises it rests on.
final class Entry<L extends Lattice<L>> {
  /// The element.
  L element;

  /// What the element rests on.
  Premises premises;

  /// The element, resting on `premises`, by default none.
  Entry(this.element, [this.premises = Premises.empty]);

  /// Meets `element`, which rests on `premises`, into the entry. Returns whether the element
  /// changed; the premises are added only then.
  bool meet(L element, Premises premises) {
    final m = this.element.meet(element);
    if (m == this.element) return false;
    this.element = m;
    this.premises = this.premises.union(premises);
    return true;
  }

  /// Joins `other` into the entry, with both sides' premises. Returns whether the element
  /// changed.
  bool join(Entry<L> other) {
    final j = element.join(other.element);
    premises = premises.union(other.premises);
    final changed = j != element;
    element = j;
    return changed;
  }

  /// Widens the entry by `other` at the component head `head`: the widening of the join, with
  /// both sides' premises and, when the widening gives more than the join, the widening
  /// itself. Returns whether the element changed.
  bool widen(Entry<L> other, FactAddress head, Landmarks marks) {
    final joined = element.join(other.element);
    final w = element.widen(joined, marks);
    premises = premises.union(other.premises);
    if (w != joined) premises = premises.union(Premises.one(Premise.widened(head)));
    final changed = w != element;
    element = w;
    return changed;
  }

  /// Whether the element rests on no widening.
  bool get proofGrade => !premises.widened;

  @override
  bool operator ==(Object other) =>
      other is Entry<L> && other.element == element && other.premises == premises;

  @override
  int get hashCode => Object.hash(element, premises);

  @override
  String toString() => 'Entry($element, $premises)';
}

/// The elements of one fact.
final class Cell {
  /// The integer values.
  Entry<Bounds> ints;

  /// The integer values' residue class.
  Entry<Congruence> congruence;

  /// The scalar and atom values, when finitely many.
  Entry<FiniteSet<Value>> finite;

  /// The float values.
  Entry<FloatClass> float;

  /// The length of a string, or the cardinality of a family's level: never negative.
  Entry<Bounds> length;

  Cell._(this.ints, this.congruence, this.finite, this.float, this.length);

  /// The cell with no information.
  Cell.top()
    : this._(
        Entry(Bounds.top),
        Entry(Congruence.top),
        Entry(const FiniteSet.top()),
        Entry(FloatClass.top),
        Entry(sizes),
      );

  /// The nonnegative integers, the top of a length.
  static final sizes = Bounds.range(const Affine.constant(0), null);

  /// The cell of a literal: the singleton in each domain that reads its kind, and no
  /// information in the others (sec:domains, literal domains). A literal rests on nothing.
  factory Cell.literal(Value v) {
    final c = Cell.top()..finite.element = FiniteSet.of([v]);
    switch (v) {
      case Int(value: final n):
        c.ints.element = Bounds.ints(IntervalSet.single(n));
        c.congruence.element = Congruence.single(n);
      case Float(:final x):
        c.float.element = FloatClass.of(x);
      case Str(:final text):
        c.length.element = Bounds.ints(IntervalSet.single(text.text.runes.length));
      default:
    }
    return c;
  }

  /// A copy, whose entries change apart from this cell's.
  Cell copy() => Cell._(
    Entry(ints.element, ints.premises),
    Entry(congruence.element, congruence.premises),
    Entry(finite.element, finite.premises),
    Entry(float.element, float.premises),
    Entry(length.element, length.premises),
  );

  /// Joins `other` into the cell, entry by entry. Returns whether an element changed.
  bool join(Cell other) => [
    ints.join(other.ints),
    congruence.join(other.congruence),
    finite.join(other.finite),
    float.join(other.float),
    length.join(other.length),
  ].contains(true);

  /// Widens the cell by `other` at the component head `head`, entry by entry. Returns whether
  /// an element changed.
  bool widen(Cell other, FactAddress head, Landmarks marks) {
    final changed = [
      ints.widen(other.ints, head, marks),
      congruence.widen(other.congruence, head, marks),
      finite.widen(other.finite, head, marks),
      float.widen(other.float, head, marks),
      length.widen(other.length, head, marks),
    ].contains(true);
    // A widening can send a length's lower end to minus infinity; a meet or a join keeps it
    // within the top, `[0..]`.
    length.element = length.element.meet(sizes);
    return changed;
  }

  /// The premises of every entry: the cell's certificate.
  Premises get premises => [
    ints.premises,
    congruence.premises,
    finite.premises,
    float.premises,
    length.premises,
  ].fold(Premises.empty, (a, p) => a.union(p));

  @override
  bool operator ==(Object other) =>
      other is Cell &&
      other.ints == ints &&
      other.congruence == congruence &&
      other.finite == finite &&
      other.float == float &&
      other.length == length;

  @override
  int get hashCode => Object.hash(ints, congruence, finite, float, length);

  /// The entries that hold information, one per line: `ints [0..=n - 1]`.
  @override
  String toString() {
    final top = Cell.top();
    final out = StringBuffer();
    if (ints != top.ints) out.writeln('ints ${ints.element}');
    if (congruence != top.congruence) out.writeln('congruence ${congruence.element}');
    if (finite.element.members case final s?) out.writeln('finite {${s.join(', ')}}');
    if (float != top.float) out.writeln('float ${float.element}');
    if (length != top.length) out.writeln('length ${length.element}');
    return out.toString();
  }
}

/// The cells of a program's facts, by fact address. An address with no cell has the top.
final class Store {
  final _cells = SplayTreeMap<FactAddress, Cell>();

  /// A copy of the cell at `addr`, the top when it has none.
  Cell cell(FactAddress addr) => _cells[addr]?.copy() ?? Cell.top();

  /// The cell at `addr`, created at the top.
  Cell cellMut(FactAddress addr) => _cells.putIfAbsent(addr, Cell.top);

  /// Sets the cell at `addr`.
  void operator []=(FactAddress addr, Cell c) => _cells[addr] = c;

  /// The cells, in address order.
  Iterable<(FactAddress, Cell)> get cells => _cells.entries.map((e) => (e.key, e.value));
}
