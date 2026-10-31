/// The lattices of the constraint store and their widenings (DESIGN.md sec:domains and
/// sec:constraints; the widening per lattice is fixed by step M0.5).
library;

import 'dart:collection';

import '../kernel/value.dart';
import 'interval.dart';

/// The values written in a program, at which a widening stops a bound and a narrowing stops a
/// descent (step M0.5): each integer literal and each declared bound `k`, as `k - 1`, `k` and
/// `k + 1`, and the other literal values. A program has finitely many, so a chain that moves
/// only to landmarks and old endpoints is finite, with no count of its steps. A cell takes the
/// landmarks of its loop only (`Scopes` in iterate.dart).
final class Landmarks {
  /// The integer landmarks as the keys of an ordered map, for the nearest one on either side.
  final _ints = SplayTreeMap<int, bool>();
  final _values = <Value>{};

  /// No landmarks: a bound that moves goes to an old endpoint or to infinity.
  Landmarks.none();

  /// The landmarks of the given integer literals and other values.
  Landmarks.of(Iterable<int> ints, [Iterable<Value> values = const []]) {
    _values.addAll(values);
    for (final k in ints) {
      if (k != minInt) _ints[k - 1] = true;
      _ints[k] = true;
      if (k != maxInt) _ints[k + 1] = true;
    }
  }

  /// Adds the landmarks of `other`.
  void extend(Landmarks other) {
    for (final k in other._ints.keys) {
      _ints[k] = true;
    }
    _values.addAll(other._values);
  }

  /// The integer landmarks, in order.
  Iterable<int> get ints => _ints.keys;

  /// Whether `v`, an `int` or a value, is a landmark.
  bool has(Object v) => switch (v) {
    int() => _ints.containsKey(v),
    Int(:final value) => _ints.containsKey(value),
    _ => _values.contains(v),
  };

  /// The greatest integer landmark at or below `v`.
  int? atOrBelow(int v) => _ints.containsKey(v) ? v : _ints.lastKeyBefore(v);

  /// The least integer landmark at or above `v`.
  int? atOrAbove(int v) => _ints.containsKey(v) ? v : _ints.firstKeyAfter(v);
}

/// A lattice of the store, with the widening that bounds its ascending chains and the
/// narrowing that bounds its descending ones. The least and greatest elements are each
/// lattice's own constructors.
abstract mixin class Lattice<L extends Lattice<L>> {
  /// The least upper bound.
  L join(L other);

  /// The greatest lower bound.
  L meet(L other);

  /// `this ∇ next` for `next ⊒ this`: an upper bound of both such that every chain of
  /// widenings is finite. For a lattice of finite height it is the join.
  L widen(L next, Landmarks marks);

  /// `this Δ next` for `next ⊑ this`: a value between the two such that every chain of
  /// narrowings is finite. For a lattice with no infinite descending chain it is `next`.
  L narrow(L next, Landmarks marks);

  /// The order: whether `this ⊑ other`. The default reads it off the meet, which is exact for
  /// a lattice whose elements have one representation each.
  bool leq(L other) => meet(other) == this;
}

/// A congruence class `residue mod modulus`, or the bottom. Modulus 0 is the one value
/// `residue`, and modulus 1 is every integer. The residue is kept in `0..modulus`.
///
/// The modulus is a nonnegative `int`, so below 2^63. A join or a meet whose exact class
/// needs a larger modulus gives a coarser class that still holds every member.
final class Congruence with Lattice<Congruence> {
  /// The modulus, 0 for a single value, or -1 for the bottom.
  final int _modulus;

  /// The residue, in `0..modulus`, or the value when the modulus is 0.
  final int residue;

  const Congruence._(this._modulus, this.residue);

  /// No value.
  static const bottom = Congruence._(-1, 0);

  /// Every integer.
  static const top = Congruence._(1, 0);

  /// The class `residue mod modulus`, normalized; `modulus` is not negative.
  factory Congruence(int modulus, int residue) =>
      Congruence._(modulus, modulus == 0 ? residue : residue % modulus);

  /// The one value `v`.
  factory Congruence.single(int v) => Congruence(0, v);

  /// The modulus, or null for the bottom.
  int? get modulus => isBottom ? null : _modulus;

  /// Whether this is the bottom.
  bool get isBottom => _modulus < 0;

  /// Whether `v` is a member.
  bool contains(int v) => switch (_modulus) {
    < 0 => false,
    0 => v == residue,
    final m => v % m == residue,
  };

  @override
  Congruence join(Congruence other) {
    if (isBottom) return other;
    if (other.isBottom) return this;
    final (r, s) = (BigInt.from(residue), BigInt.from(other.residue));
    final g = BigInt.from(_modulus).gcd(BigInt.from(other._modulus)).gcd((r - s).abs());
    // Only the difference of two single values can pass 2^63; every integer is a sound
    // class above them.
    return g.isValidInt ? Congruence(g.toInt(), residue) : top;
  }

  @override
  Congruence meet(Congruence other) {
    if (isBottom || other.isBottom) return bottom;
    if (_modulus == 0) return other.contains(residue) ? this : bottom;
    if (other._modulus == 0) return contains(other.residue) ? other : bottom;
    // The Chinese remainder theorem: solvable iff r ≡ s mod g = gcd(m, n), and then the
    // solutions are one class modulo lcm(m, n): x = r + m·k, where (m/g)·k ≡ (s - r)/g mod n/g.
    final (m, n) = (BigInt.from(_modulus), BigInt.from(other._modulus));
    final (r, s) = (BigInt.from(residue), BigInt.from(other.residue));
    final g = m.gcd(n);
    if ((s - r) % g != BigInt.zero) return bottom;
    final (m1, n1) = (m ~/ g, n ~/ g);
    final l = m1 * n;
    if (!l.isValidInt) {
      // The class is too fine to represent; either operand is a sound bound.
      return _modulus >= other._modulus ? this : other;
    }
    final inverse = n1 == BigInt.one ? BigInt.zero : m1.modInverse(n1);
    final k = ((s - r) ~/ g) % n1 * inverse % n1;
    return Congruence(l.toInt(), ((r + m * k) % l).toInt());
  }

  /// Above any class other than the bottom, an ascending chain divides the modulus at each
  /// step, so it is finite: the widening is the join.
  @override
  Congruence widen(Congruence next, Landmarks marks) => join(next);

  /// A descending chain can multiply the modulus without end (`0 mod 2`, `0 mod 4`, ...), so
  /// the narrowing takes `next` only from the top, or when `next` is one value or none: a
  /// chain of narrowings changes at most three times.
  @override
  Congruence narrow(Congruence next, Landmarks marks) =>
      this == top || next._modulus <= 0 ? next : this;

  @override
  bool operator ==(Object other) =>
      other is Congruence && other._modulus == _modulus && other.residue == residue;

  @override
  int get hashCode => Object.hash(_modulus, residue);

  /// `{}`, `5`, `1 mod 3`, or `any` for every integer.
  @override
  String toString() => switch (_modulus) {
    < 0 => '{}',
    0 => '$residue',
    1 => 'any',
    final m => '$residue mod $m',
  };
}

/// A finite set of scalars or atoms, or the top: no finite-set fact. `T` is ordered by its
/// `compareTo`.
final class FiniteSet<T extends Object> with Lattice<FiniteSet<T>> {
  /// The members in order, or null for the top.
  final SplayTreeSet<T>? _members;

  const FiniteSet._(this._members);

  /// The set of the given values.
  FiniteSet.of(Iterable<T> values) : _members = SplayTreeSet.of(values);

  /// The empty set.
  FiniteSet.bottom() : _members = SplayTreeSet();

  /// Any value of the carrier.
  const FiniteSet.top() : _members = null;

  /// The members in order, or null for the top.
  Iterable<T>? get members => _members;

  bool get isTop => _members == null;

  @override
  FiniteSet<T> join(FiniteSet<T> other) => switch ((_members, other._members)) {
    (final a?, final b?) => FiniteSet._(SplayTreeSet.of(a)..addAll(b)),
    _ => const FiniteSet.top(),
  };

  @override
  FiniteSet<T> meet(FiniteSet<T> other) => switch ((_members, other._members)) {
    (final a?, final b?) => FiniteSet._(SplayTreeSet.of(a.where(b.contains))),
    (null, _) => other,
    (_, null) => this,
  };

  /// The join when every member it adds is a landmark, else the top; the bottom widens to
  /// `next`. The members of a chain are the first element's and landmarks, so it rises
  /// finitely often.
  @override
  FiniteSet<T> widen(FiniteSet<T> next, Landmarks marks) {
    if (_members case final old? when old.isEmpty) return next;
    final j = join(next);
    if ((_members, j._members) case (final old?, final all?)
        when all.every((v) => old.contains(v) || marks.has(v))) {
      return j;
    }
    return const FiniteSet.top();
  }

  /// A descending chain leaves the top at most once and then loses members: it is `next`.
  @override
  FiniteSet<T> narrow(FiniteSet<T> next, Landmarks marks) => next;

  @override
  bool operator ==(Object other) {
    if (other is! FiniteSet<T>) return false;
    final (a, b) = (_members, other._members);
    if (a == null || b == null) return a == b;
    if (a.length != b.length) return false;
    final (i, j) = (a.iterator, b.iterator);
    while (i.moveNext() && j.moveNext()) {
      if (i.current != j.current) return false;
    }
    return true;
  }

  @override
  int get hashCode => _members == null ? 0 : Object.hashAll(_members);

  @override
  String toString() => _members == null ? 'Top' : '{${_members.join(', ')}}';
}

/// A cardinality or a length: one interval of the nonnegative integers (sec:domains, `card`
/// and `len`). It has no pieces, since a level's size is one interval in every refinement.
final class Card with Lattice<Card> {
  /// The interval.
  final IntervalSet interval;

  const Card._(this.interval);

  /// The sizes from `lo` to `hi`.
  Card.range(End lo, End hi) : interval = IntervalSet.range(lo, hi).meet(_sizes);

  /// No size.
  const Card.bottom() : interval = const IntervalSet.empty();

  /// Every size.
  factory Card.top() => Card._(_sizes);

  static final _sizes = IntervalSet.range(const Fin(0), posInf);

  @override
  Card join(Card other) => Card._(interval.join(other.interval).hull());

  @override
  Card meet(Card other) => Card._(interval.meet(other.interval));

  /// The interval widening, whose `-inf` is then the least size, 0.
  @override
  Card widen(Card next, Landmarks marks) =>
      Card._(interval.widen(next.interval, marks).meet(_sizes));

  @override
  Card narrow(Card next, Landmarks marks) =>
      Card._(interval.narrow(next.interval, marks).meet(_sizes));

  @override
  bool operator ==(Object other) => other is Card && other.interval == interval;

  @override
  int get hashCode => interval.hashCode;

  @override
  String toString() => 'Card$interval';
}
