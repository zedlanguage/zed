/// Intervals with symbolic affine bounds (DESIGN.md sec:domains: "integer intervals and
/// congruences, with symbolic affine bounds (`int[0..<n]`, `int[0..<a::len]`)"; step L1.24).
///
/// An element is an interval union over the integers, as in interval.dart, together with a set
/// of symbolic lower bounds and a set of symbolic upper bounds: the value lies in the union and
/// within every bound. A symbolic bound is an affine expression in at least one symbol with an
/// optional numeric floor, `max(c, a)` for an upper bound and `min(c, a)` for a lower one; the
/// floor is what a join with a number needs. A bound with no symbol is a number, and goes into
/// the union. Of two bounds with the same terms, one that implies the other replaces it; bounds
/// with different terms cannot be compared without the symbols' values, so both are kept.
///
/// Join keeps, for each pair of bounds with the same terms, the looser of the two, and for each
/// bound of one side, its loosening by the other side's numeric end. Meet keeps every bound of
/// either side. The order compares bounds the same way, so it is sound and not complete:
/// `int[0..=n]` is below `int[..=m]` only when its union's end is at most `m`'s floor, or it
/// has a bound with the terms of `m`. Widening widens the union and keeps only the symbolic
/// bounds the old element had, so a chain of widenings is finite.
library;

import 'dart:collection';

import '../kernel/text.dart';
import 'interval.dart';
import 'lattice.dart';

/// A symbol an affine bound names: a name in scope or its length, `n` or `a::len`. The store
/// names each symbol by its source text, unique within one store.
extension type const Sym(String name) {}

/// `a + b`, or null past the 64-bit range.
int? _add(int a, int b) {
  final s = a + b;
  return (a ^ s) & (b ^ s) < 0 ? null : s;
}

/// `a * b`, or null past the 64-bit range.
int? _mul(int a, int b) {
  if (a == 0 || b == 0) return 0;
  if ((a == -1 && b == minInt) || (b == -1 && a == minInt)) return null;
  final p = a * b;
  return p ~/ b == a ? p : null;
}

/// The symbols of an affine expression and their coefficients, none zero, in the order of
/// their names' code points.
final class Terms implements Comparable<Terms> {
  final List<(Sym, int)> _pairs;

  const Terms._(this._pairs);

  static const none = Terms._([]);

  /// Whether there is no symbol.
  bool get isEmpty => _pairs.isEmpty;

  /// The symbols and their coefficients, in order.
  Iterable<(Sym, int)> get pairs => _pairs;

  /// Ordered as the sequences of their pairs: by name, then coefficient, a prefix first.
  @override
  int compareTo(Terms other) {
    final (a, b) = (_pairs, other._pairs);
    for (var i = 0; i < a.length && i < b.length; i++) {
      final c = compareUtf8(a[i].$1.name, b[i].$1.name);
      if (c != 0) return c;
      if (a[i].$2 != b[i].$2) return a[i].$2.compareTo(b[i].$2);
    }
    return a.length.compareTo(b.length);
  }

  @override
  bool operator ==(Object other) => other is Terms && compareTo(other) == 0;

  @override
  int get hashCode => Object.hashAll(_pairs);
}

/// `constant + Σ coefficient · symbol`, with no zero coefficient.
final class Affine implements Comparable<Affine> {
  /// The symbols and their coefficients. Bounds are ordered by these first.
  final Terms terms;

  /// The constant.
  final int constant;

  const Affine._(this.terms, this.constant);

  /// The number `c`.
  const Affine.constant(int c) : this._(Terms.none, c);

  /// The symbol `s`.
  Affine.sym(String s) : this._(Terms._([(Sym(s), 1)]), 0);

  /// `constant + Σ terms[s] · s`.
  factory Affine.of(Map<String, int> terms, int constant) {
    final names = terms.keys.where((s) => terms[s] != 0).toList()..sort(compareUtf8);
    return Affine._(Terms._([for (final s in names) (Sym(s), terms[s]!)]), constant);
  }

  /// `this + c`, or null past the 64-bit range.
  Affine? plus(int c) => switch (_add(constant, c)) {
    final k? => Affine._(terms, k),
    null => null,
  };

  /// `k · this`, or null past the 64-bit range.
  Affine? times(int k) {
    if (k == 0) return const Affine.constant(0);
    final pairs = <(Sym, int)>[];
    for (final (s, c) in terms._pairs) {
      final m = _mul(c, k);
      if (m == null) return null;
      pairs.add((s, m));
    }
    final c = _mul(constant, k);
    return c == null ? null : Affine._(Terms._(pairs), c);
  }

  /// The value at the given symbol values, exactly.
  BigInt eval(int Function(Sym) at) {
    // In 64 bits while it fits, the common case, and exactly past it.
    int? v = constant;
    for (final (s, c) in terms._pairs) {
      final t = _mul(c, at(s));
      v = t == null ? null : _add(v!, t);
      if (v == null) break;
    }
    if (v != null) return BigInt.from(v);
    var big = BigInt.from(constant);
    for (final (s, c) in terms._pairs) {
      big += BigInt.from(c) * BigInt.from(at(s));
    }
    return big;
  }

  /// Whether the bound has no symbol.
  bool get isConstant => terms.isEmpty;

  @override
  int compareTo(Affine other) {
    final c = terms.compareTo(other.terms);
    return c != 0 ? c : constant.compareTo(other.constant);
  }

  @override
  bool operator ==(Object other) =>
      other is Affine && other.constant == constant && other.terms == terms;

  @override
  int get hashCode => Object.hash(terms, constant);

  /// `n`, `-n`, `2 * n - m + 1`, `0`.
  @override
  String toString() {
    final out = StringBuffer();
    var first = true;
    for (final (s, c) in terms._pairs) {
      if (first) {
        if (c < 0) out.write('-');
      } else {
        out.write(c < 0 ? ' - ' : ' + ');
      }
      first = false;
      if (c != 1 && c != -1) out.write('${_abs(c)} * ');
      out.write(s.name);
    }
    if (terms.isEmpty) return '$constant';
    if (constant < 0) out.write(' - ${_abs(constant)}');
    if (constant > 0) out.write(' + $constant');
    return out.toString();
  }
}

/// `|c|`, printed; `minInt` has no 64-bit absolute value.
String _abs(int c) => c == minInt ? '${-BigInt.from(c)}' : '${c.abs()}';

/// Which side a bound is on.
enum Side {
  /// `x ≥ min(floor, affine)`.
  lower,

  /// `x ≤ max(floor, affine)`.
  upper;

  /// The floor of a bound with none: the end that `min` or `max` ignores.
  End get _none => this == lower ? posInf : negInf;

  /// The floor that makes a bound hold of every integer.
  End get _vacuous => this == lower ? negInf : posInf;

  /// The looser of two ends: the smaller for a lower bound, the larger for an upper.
  End _looserEnd(End a, End b) => this == lower ? a.min(b) : a.max(b);

  /// The looser of two constants.
  int _looser(int a, int b) => this == lower ? (a < b ? a : b) : (a > b ? a : b);

  /// The end of the interval hull on this side.
  End _hullEnd(IntervalSet ints) {
    final (lo, hi) = ints.bounds ?? (posInf, negInf);
    return this == lower ? lo : hi;
  }
}

/// A symbolic bound on one side: `min(floor, affine)` for a lower bound and `max(floor, affine)`
/// for an upper, where the floor is a number or, for a bound with none, the infinity `min` or
/// `max` ignores. The affine part has at least one symbol.
///
/// The floor is what a join with a number gives: a value in `[0]` or in `[1..=n]` is at most
/// `max(0, n)`, and not at most `n`, since `[1..=n]` is empty when `n < 0`.
final class Bound implements Comparable<Bound> {
  /// The affine part.
  final Affine affine;

  /// The floor.
  final End floor;

  const Bound(this.affine, this.floor);

  /// The bound's value at the given symbol values.
  BigInt _eval(Side side, int Function(Sym) at) {
    final a = affine.eval(at);
    return switch (floor) {
      Fin(:final v) when side == Side.lower => a < BigInt.from(v) ? a : BigInt.from(v),
      Fin(:final v) => a > BigInt.from(v) ? a : BigInt.from(v),
      _ => a,
    };
  }

  /// Whether `this` is at least as tight as `other` for every symbol value: the same terms,
  /// and a constant and a floor each at least as tight.
  bool _implies(Side side, Bound other) =>
      affine.terms == other.affine.terms &&
      side._looser(affine.constant, other.affine.constant) == other.affine.constant &&
      side._looserEnd(floor, other.floor) == other.floor;

  /// The bound both `this` and `other` imply; they have the same terms.
  Bound _loosen(Side side, Bound other) => Bound(
    Affine._(affine.terms, side._looser(affine.constant, other.affine.constant)),
    side._looserEnd(floor, other.floor),
  );

  /// The bound `this` and the number `end` both imply.
  Bound? _loosenEnd(Side side, End end) {
    final f = side._looserEnd(floor, end);
    return f == side._vacuous ? null : Bound(affine, f);
  }

  String _show(Side side) => switch ((floor, side)) {
    (Fin(:final v), Side.lower) => 'min($v, $affine)',
    (Fin(:final v), Side.upper) => 'max($v, $affine)',
    _ => '$affine',
  };

  @override
  int compareTo(Bound other) {
    final c = affine.compareTo(other.affine);
    return c != 0 ? c : floor.compareTo(other.floor);
  }

  @override
  bool operator ==(Object other) =>
      other is Bound && other.affine == affine && other.floor == floor;

  @override
  int get hashCode => Object.hash(affine, floor);

  @override
  String toString() => 'Bound($affine, $floor)';
}

/// The bounds of one side, grouped by their terms: a group is the bounds with one set of terms,
/// none implying another, in order. Finding the bounds with given terms is a lookup and not a
/// scan, so the operations on bounds over many symbols are `O(k log k)` and not `O(k²)`
/// (DESIGN.md Part G).
typedef _Groups = SplayTreeMap<Terms, List<Bound>>;

/// An interval union with symbolic bounds.
final class Bounds with Lattice<Bounds> {
  final IntervalSet _ints;
  final _Groups _lower, _upper;

  Bounds._(this._ints, this._lower, this._upper);

  /// No integer.
  static final bottom = Bounds._(const IntervalSet.empty(), _Groups(), _Groups());

  /// Every integer.
  static final top = Bounds.ints(IntervalSet.top());

  /// The integers in `ints`, with no symbolic bound.
  factory Bounds.ints(IntervalSet ints) => Bounds(ints, const [], const []);

  /// The integers in `ints` at or above each of `lower` and at or below each of `upper`.
  factory Bounds(IntervalSet ints, Iterable<Affine> lower, Iterable<Affine> upper) =>
      Bounds.fromBounds(
        ints,
        [for (final a in lower) Bound(a, Side.lower._none)],
        [for (final a in upper) Bound(a, Side.upper._none)],
      );

  /// The integers in `ints` within each of the given bounds.
  factory Bounds.fromBounds(IntervalSet ints, Iterable<Bound> lower, Iterable<Bound> upper) {
    final b = Bounds._(ints, _Groups(), _Groups());
    var meet = ints;
    for (final l in lower) {
      meet = b._add(Side.lower, l, meet);
    }
    for (final u in upper) {
      meet = b._add(Side.upper, u, meet);
    }
    return Bounds._(meet, b._lower, b._upper)._normal();
  }

  /// The range `lo..=hi` with affine ends, null meaning unbounded: `range(0, n - 1)` is
  /// `int[0..<n]`.
  factory Bounds.range(Affine? lo, Affine? hi) => Bounds(IntervalSet.top(), [?lo], [?hi]);

  /// The interval union, without the symbolic bounds.
  IntervalSet get concrete => _ints;

  /// The symbolic bounds on one side, in order.
  List<Bound> bounds(Side side) => [for (final g in _groups(side).values) ...g];

  _Groups _groups(Side side) => side == Side.lower ? _lower : _upper;

  bool get isBottom => _ints.isEmpty;

  /// Adds a bound and returns the union: one with no symbol meets the union; otherwise it is
  /// dropped when a bound already there implies it, and drops each bound already there that it
  /// implies.
  IntervalSet _add(Side side, Bound b, IntervalSet ints) {
    if (b.affine.isConstant) {
      final c = side._looserEnd(Fin(b.affine.constant), b.floor);
      return ints.meet(
        side == Side.lower ? IntervalSet.range(c, posInf) : IntervalSet.range(negInf, c),
      );
    }
    final group = _groups(side).putIfAbsent(b.affine.terms, () => []);
    if (group.any((o) => o._implies(side, b))) return ints;
    group.removeWhere((o) => b._implies(side, o));
    // A group is a few bounds, none implying another.
    final at = group.indexWhere((o) => o.compareTo(b) > 0);
    group.insert(at < 0 ? group.length : at, b);
    return ints;
  }

  /// Drops each bound the union implies, a floor at or past the union's end; and gives the
  /// bottom when the union is empty or a lower bound with no floor exceeds an upper one with
  /// the same terms and no floor.
  Bounds _normal() {
    for (final side in Side.values) {
      final end = side._hullEnd(_ints);
      final groups = _groups(side);
      for (final g in groups.values) {
        g.removeWhere((b) => side._looserEnd(b.floor, end) == b.floor);
      }
      groups.removeWhere((_, g) => g.isEmpty);
    }
    final crossed = _lower.entries.any(
      (e) => e.value.any(
        (l) =>
            l.floor == posInf &&
            (_upper[e.key] ?? const []).any(
              (u) => u.floor == negInf && l.affine.constant > u.affine.constant,
            ),
      ),
    );
    return _ints.isEmpty || crossed ? bottom : this;
  }

  /// Whether `v` is in the element at the given symbol values.
  bool contains(int v, int Function(Sym) at) {
    if (!_ints.contains(v)) return false;
    final x = BigInt.from(v);
    return _lower.values.every((g) => g.every((l) => l._eval(Side.lower, at) <= x)) &&
        _upper.values.every((g) => g.every((u) => x <= u._eval(Side.upper, at)));
  }

  /// The element shifted by `c`: `x + c` for each member `x`. A bound past the 64-bit range is
  /// dropped, which only widens the element.
  Bounds offset(int c) {
    List<Bound> shift(Side side, End Function(BigInt) end) => [
      for (final b in bounds(side))
        if (b.affine.plus(c) case final a?) Bound(a, _shiftEnd(b.floor, c, end)),
    ];
    final ints = _ints.lift1(
      (p) => [(_shiftEnd(p.$1, c, End.lower), _shiftEnd(p.$2, c, End.upper))],
    );
    return Bounds.fromBounds(ints, shift(Side.lower, End.lower), shift(Side.upper, End.upper));
  }

  /// The bounds on one side that every member of `a` or of `b` is within: for each pair with
  /// the same terms, the looser; and for each bound of one side, the looser of it and the other
  /// side's end.
  static List<Bound> _joined(Side side, Bounds a, Bounds b) {
    final (ga, gb) = (a._groups(side), b._groups(side));
    final (endA, endB) = (side._hullEnd(a._ints), side._hullEnd(b._ints));
    return [
      for (final MapEntry(key: terms, value: xs) in ga.entries)
        for (final x in xs)
          for (final y in gb[terms] ?? const <Bound>[]) x._loosen(side, y),
      for (final x in a.bounds(side)) ?x._loosenEnd(side, endB),
      for (final y in b.bounds(side)) ?y._loosenEnd(side, endA),
    ];
  }

  @override
  Bounds join(Bounds other) {
    if (isBottom) return other;
    if (other.isBottom) return this;
    return Bounds.fromBounds(
      _ints.join(other._ints),
      _joined(Side.lower, this, other),
      _joined(Side.upper, this, other),
    );
  }

  @override
  Bounds meet(Bounds other) => Bounds.fromBounds(
    _ints.meet(other._ints),
    [...bounds(Side.lower), ...other.bounds(Side.lower)],
    [...bounds(Side.upper), ...other.bounds(Side.upper)],
  );

  /// The union widens as in interval.dart, and a symbolic bound of `next` is kept only when
  /// `this` has it. So the bounds of a chain of widenings only shrink, and the chain is finite.
  @override
  Bounds widen(Bounds next, Landmarks marks) {
    if (isBottom) return next;
    List<Bound> kept(Side side) => [
      for (final b in next.bounds(side))
        if (_groups(side)[b.affine.terms]?.contains(b) ?? false) b,
    ];
    return Bounds.fromBounds(_ints.widen(next._ints, marks), kept(Side.lower), kept(Side.upper));
  }

  /// The union narrows as in interval.dart, and a side takes the symbolic bounds of `next` only
  /// while it has none: each side gains bounds at most once, so every chain of narrowings is
  /// finite.
  @override
  Bounds narrow(Bounds next, Landmarks marks) {
    List<Bound> side(Side s) => (_groups(s).isEmpty ? next : this).bounds(s);
    return Bounds.fromBounds(_ints.narrow(next._ints, marks), side(Side.lower), side(Side.upper));
  }

  /// Sound and not complete: each bound of `other` must be implied by a bound of `this` with
  /// the same terms, or by the end of `this`'s union.
  @override
  bool leq(Bounds other) {
    bool implied(Side side) {
      final end = side._hullEnd(_ints);
      return other
          .bounds(side)
          .every(
            (t) =>
                (_groups(side)[t.affine.terms] ?? const <Bound>[]).any(
                  (m) => m._implies(side, t),
                ) ||
                side._looserEnd(t.floor, end) == t.floor,
          );
    }

    return isBottom || (_ints.isSubset(other._ints) && implied(Side.lower) && implied(Side.upper));
  }

  @override
  bool operator ==(Object other) {
    if (other is! Bounds || other._ints != _ints) return false;
    for (final side in Side.values) {
      final (a, b) = (bounds(side), other.bounds(side));
      if (a.length != b.length) return false;
      for (var i = 0; i < a.length; i++) {
        if (a[i] != b[i]) return false;
      }
    }
    return true;
  }

  @override
  int get hashCode =>
      Object.hash(_ints, Object.hashAll(bounds(Side.lower)), Object.hashAll(bounds(Side.upper)));

  /// The design's form without the carrier: `[0..=n - 1]`, `[0..=max(0, n)]`, `[max(0, m)..]`,
  /// `[..=min(9, n)]`. A union of several pieces with symbolic bounds prints the two parts
  /// joined by `&`: `[0..=3, 5..] & [..=n]`.
  @override
  String toString() {
    if (_lower.isEmpty && _upper.isEmpty) return '$_ints';
    final out = StringBuffer();
    var (End lo, End hi) = (negInf, posInf);
    if (_ints.pieces case [final p]) {
      (lo, hi) = p;
    } else {
      out.write('$_ints & ');
    }
    String end(Side side, End num) {
      final items = [if (num case Fin(:final v)) '$v', for (final b in bounds(side)) b._show(side)];
      return switch (items) {
        [] => '',
        [final one] => one,
        _ => '${side == Side.lower ? 'max' : 'min'}(${items.join(', ')})',
      };
    }

    final (l, u) = (end(Side.lower, lo), end(Side.upper, hi));
    out.write(u.isEmpty ? '[$l..]' : '[$l..=$u]');
    return out.toString();
  }
}

/// `e + c`, rounded by `end` as a lower or an upper end.
End _shiftEnd(End e, int c, End Function(BigInt) end) => switch (e) {
  Fin(:final v) => end(BigInt.from(v) + BigInt.from(c)),
  _ => e,
};
