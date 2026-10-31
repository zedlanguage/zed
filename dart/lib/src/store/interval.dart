/// The interval domain: finite unions of integer intervals with infinite endpoints (DESIGN.md
/// sec:constraints, "Intervals"; widening fixed by step M0.5).
///
/// An element is a sorted list of disjoint pieces, each `lo..=hi`, with at least one integer
/// missing between two pieces, so that every set has exactly one representation and equality
/// of elements is equality of sets. The empty list is the empty set, the bottom of the lattice.
/// Meet and join are exact.
library;

import 'dart:collection';

import 'lattice.dart';

/// The least and the greatest 64-bit integer.
const minInt = -0x8000000000000000, maxInt = 0x7fffffffffffffff;

var _rounded = false;

/// Whether an end past the 64-bit integers was rounded outward since the last call. A set
/// built from a rounded end holds every integer it should, but may hold more: an end of
/// [maxInt] stands for every integer from there up, so `maxInt` and `maxInt + 1` are not told
/// apart. A transfer that claims its result is exact checks this first.
bool rounded() {
  final r = _rounded;
  _rounded = false;
  return r;
}

/// The Euclidean quotient: the remainder `x - q·y` is in `0..abs(y)`. `y` is not 0, and
/// `minInt` over `-1` is not asked for, since the quotient does not fit.
int divEuclid(int x, int y) {
  final q = x ~/ y;
  if (x < 0 && q * y != x) return y > 0 ? q - 1 : q + 1;
  return q;
}

/// An endpoint: an integer or one of the two infinities, ordered `-inf`, the integers, `inf`.
sealed class End implements Comparable<End> {
  const End();

  /// The endpoint for an exact result `x`, which may lie outside the 64-bit integers. A value
  /// that does not fit is replaced by the infinity on its side: this widens an interval it
  /// bounds above past [maxInt], or below past [minInt]; for the other two cases see
  /// [End.lower] and [End.upper].
  static End exact(BigInt x) {
    if (x.isValidInt) return Fin(x.toInt());
    _rounded = true;
    return x.isNegative ? negInf : posInf;
  }

  /// `x` as the lower end of an interval, rounded down. A set holds an integer past the 64-bit
  /// integers when it is unbounded on that side, so a lower end past [maxInt] is `maxInt`,
  /// whose interval holds every integer beyond it; the infinity would empty the interval.
  static End lower(BigInt x) {
    if (x > _maxBig) {
      _rounded = true;
      return const Fin(maxInt);
    }
    return exact(x);
  }

  /// `x` as the upper end of an interval, rounded up: [End.lower] mirrored.
  static End upper(BigInt x) {
    if (x < _minBig) {
      _rounded = true;
      return const Fin(minInt);
    }
    return exact(x);
  }

  /// The rank in the order: 0 for `-inf`, 1 for an integer, 2 for `inf`.
  int get _rank;

  @override
  int compareTo(End other) => switch ((this, other)) {
    (Fin(v: final a), Fin(v: final b)) => a.compareTo(b),
    _ => _rank.compareTo(other._rank),
  };

  bool operator <(End other) => compareTo(other) < 0;
  bool operator <=(End other) => compareTo(other) <= 0;
  bool operator >(End other) => compareTo(other) > 0;
  bool operator >=(End other) => compareTo(other) >= 0;

  /// The lesser of the two.
  End min(End other) => this <= other ? this : other;

  /// The greater of the two.
  End max(End other) => this >= other ? this : other;

  /// The negation, which swaps the infinities; `-minInt` does not fit and goes to `inf`. As
  /// an upper end this is exact; [negLower] gives the lower end.
  End operator -() => switch (this) {
    NegInf() => posInf,
    PosInf() => negInf,
    Fin(v: minInt) => exact(-_minBig),
    Fin(:final v) => Fin(-v),
  };

  /// `-this` as the lower end of an interval. [operator -] gives the upper end.
  End negLower() => switch (this) {
    Fin(v: minInt) => lower(-_minBig),
    final e => -e,
  };

  /// The next integer up; the infinities are fixed.
  End succ() => switch (this) {
    Fin(v: maxInt) => exact(_maxBig + BigInt.one),
    Fin(:final v) => Fin(v + 1),
    final e => e,
  };

  /// The next integer down; the infinities are fixed.
  End pred() => switch (this) {
    Fin(v: minInt) => exact(_minBig - BigInt.one),
    Fin(:final v) => Fin(v - 1),
    final e => e,
  };

  /// The sign: -1, 0 or 1.
  int get sign => switch (this) {
    NegInf() => -1,
    PosInf() => 1,
    Fin(:final v) => v.sign,
  };
}

final _minBig = BigInt.from(minInt), _maxBig = BigInt.from(maxInt);

/// Below every integer.
final class NegInf extends End {
  const NegInf._();

  @override
  int get _rank => 0;

  @override
  String toString() => '-inf';
}

/// An integer.
final class Fin extends End {
  final int v;

  const Fin(this.v);

  @override
  int get _rank => 1;

  @override
  bool operator ==(Object other) => other is Fin && other.v == v;

  @override
  int get hashCode => v.hashCode;

  @override
  String toString() => '$v';
}

/// Above every integer.
final class PosInf extends End {
  const PosInf._();

  @override
  int get _rank => 2;

  @override
  String toString() => 'inf';
}

const negInf = NegInf._(), posInf = PosInf._();

/// A piece `lo..=hi`.
typedef Piece = (End, End);

int _comparePieces(Piece a, Piece b) {
  final c = a.$1.compareTo(b.$1);
  return c != 0 ? c : a.$2.compareTo(b.$2);
}

/// A finite union of integer intervals.
final class IntervalSet with Lattice<IntervalSet> {
  final List<Piece> _pieces;

  const IntervalSet._(this._pieces);

  /// The empty set.
  const IntervalSet.empty() : _pieces = const [];

  /// Every integer.
  factory IntervalSet.top() => IntervalSet.range(negInf, posInf);

  /// The integers from `lo` to `hi`, both included; empty when `lo > hi`.
  factory IntervalSet.range(End lo, End hi) => IntervalSet.fromPieces([(lo, hi)]);

  /// The one integer `v`.
  factory IntervalSet.single(int v) => IntervalSet.range(Fin(v), Fin(v));

  /// The integers from `lo` to `hi`, both finite and included.
  factory IntervalSet.of(int lo, int hi) => IntervalSet.range(Fin(lo), Fin(hi));

  /// The union of the given pieces, in any order, overlapping or not. A piece whose lower
  /// endpoint is above its upper one, or which has an infinite endpoint on the wrong side, is
  /// empty and is dropped.
  factory IntervalSet.fromPieces(Iterable<Piece> pieces) {
    final sorted = [
      for (final p in pieces)
        if (p.$1 <= p.$2 && p.$1 is! PosInf && p.$2 is! NegInf) p,
    ]..sort(_comparePieces);
    final out = <Piece>[];
    for (final p in sorted) {
      // Overlapping or adjacent: no integer lies between, so the pieces are one.
      if (out.isNotEmpty && p.$1 <= out.last.$2.succ()) {
        out.last = (out.last.$1, out.last.$2.max(p.$2));
      } else {
        out.add(p);
      }
    }
    return IntervalSet._(out);
  }

  /// The pieces, in increasing order.
  List<Piece> get pieces => UnmodifiableListView(_pieces);

  /// Whether the set is empty.
  bool get isEmpty => _pieces.isEmpty;

  /// The least and the greatest endpoint, or null for the empty set.
  Piece? get bounds => isEmpty ? null : (_pieces.first.$1, _pieces.last.$2);

  /// The smallest single interval containing the set.
  IntervalSet hull() => switch (bounds) {
    (final lo, final hi) => IntervalSet.range(lo, hi),
    null => const IntervalSet.empty(),
  };

  /// Whether `v` is a member, by binary search of the pieces.
  bool contains(int v) {
    final x = Fin(v);
    final below = _partition(_pieces.length, (i) => _pieces[i].$1 <= x);
    return below > 0 && x <= _pieces[below - 1].$2;
  }

  /// The number of finite endpoints, lower and upper; the infinities are left out. Widening
  /// decreases it (see [widen]).
  int get finiteEndpoints =>
      _pieces.fold(0, (n, p) => n + (p.$1 is NegInf ? 0 : 1) + (p.$2 is PosInf ? 0 : 1));

  /// The union, by one merge of the two sorted lists of pieces.
  @override
  IntervalSet join(IntervalSet other) {
    final (a, b) = (_pieces, other._pieces);
    var (i, j) = (0, 0);
    final out = <Piece>[];
    while (i < a.length || j < b.length) {
      final Piece next;
      if (j == b.length || (i < a.length && _comparePieces(a[i], b[j]) <= 0)) {
        next = a[i++];
      } else {
        next = b[j++];
      }
      if (out.isNotEmpty && next.$1 <= out.last.$2.succ()) {
        out.last = (out.last.$1, out.last.$2.max(next.$2));
      } else {
        out.add(next);
      }
    }
    return IntervalSet._(out);
  }

  /// The intersection.
  @override
  IntervalSet meet(IntervalSet other) {
    var (i, j) = (0, 0);
    final out = <Piece>[];
    while (i < _pieces.length && j < other._pieces.length) {
      final (a, b) = (_pieces[i], other._pieces[j]);
      final (lo, hi) = (a.$1.max(b.$1), a.$2.min(b.$2));
      if (lo <= hi) out.add((lo, hi));
      if (a.$2 < b.$2) {
        i++;
      } else {
        j++;
      }
    }
    return IntervalSet._(out);
  }

  /// Whether every member of `this` is a member of `other`.
  bool isSubset(IntervalSet other) => meet(other) == this;

  /// The set with at most `limit` pieces: while it has more, the two neighboring pieces with
  /// the fewest integers between them merge into their hull, the lower pair on a tie
  /// (sec:constraints). This is not a join and need not be monotone; forward revision applies
  /// it to bound an image by its operands' pieces.
  IntervalSet cap(int limit) {
    if (limit < 1) limit = 1;
    final n = _pieces.length;
    if (n <= limit) return this;
    // The pieces as a linked list, so that a merge is O(1), and the gaps in an ordered set,
    // smallest first and the lower pair on a tie; a gap whose right piece has changed since
    // it was added is skipped when it comes up.
    final runs = [for (var i = 0; i < n; i++) _Run(i, _pieces[i].$1, _pieces[i].$2)];
    for (var i = 0; i + 1 < n; i++) {
      runs[i].next = runs[i + 1];
    }
    final gaps = SplayTreeSet<_Gap>(_Gap.compare)
      ..addAll([for (var i = 0; i + 1 < n; i++) _Gap.between(runs[i], runs[i + 1])]);
    for (var count = n; count > limit;) {
      final g = gaps.first;
      gaps.remove(g);
      final (left, right) = (g.left, g.left.next);
      if (!left.alive || right == null || right.lo != g.rightLo) continue;
      left.hi = right.hi;
      right.alive = false;
      left.next = right.next;
      if (left.next case final r?) gaps.add(_Gap.between(left, r));
      count--;
    }
    return IntervalSet._([
      for (final r in runs)
        if (r.alive) (r.lo, r.hi),
    ]);
  }

  /// The widening `this ∇ next` (step M0.5), for `next` the value that the join would give,
  /// which contains `this`.
  ///
  /// Each finite endpoint of `next` moves outward to the nearest target: an endpoint of
  /// `this`, of either role, or a landmark; with none on that side, to the infinity there.
  /// A lower endpoint moves down and an upper one up, so the result contains `next`, and
  /// pieces that then touch merge. An endpoint of `this` or a landmark stays where it is.
  ///
  /// So the finite endpoints of every element of an ascending chain of widenings lie in
  /// `K`, the first element's endpoints and the landmarks. An element whose endpoints lie in
  /// `K` is a union of some of the `2|K| + 1` parts into which `K` cuts the line (its points
  /// and the gaps between them), so the chain has at most `2|K| + 2` elements. No count of
  /// pieces or of steps enters. The bottom widens to `next` unchanged.
  @override
  IntervalSet widen(IntervalSet next, Landmarks marks) {
    if (isEmpty || next == this) return next;
    final ends = _finiteEnds();
    return IntervalSet.fromPieces([
      for (final (lo, hi) in next._pieces)
        (
          switch (lo) {
            Fin(:final v) => _below(ends, marks, v).asLower,
            final e => e,
          },
          switch (hi) {
            Fin(:final v) => _above(ends, marks, v).asUpper,
            final e => e,
          },
        ),
    ]);
  }

  /// The least set holding `this` whose finite ends are landmarks: each end of each piece
  /// moves out to the nearest landmark on its side, or to infinity when there is none. Its
  /// ends lie in a finite set, so there are finitely many results for one set of landmarks.
  IntervalSet snap(Landmarks marks) => IntervalSet.fromPieces([
    for (final (lo, hi) in _pieces)
      (
        switch (lo) {
          Fin(:final v) => marks.atOrBelow(v).asLower,
          final e => e,
        },
        switch (hi) {
          Fin(:final v) => marks.atOrAbove(v).asUpper,
          final e => e,
        },
      ),
  ]);

  /// The narrowing `this Δ next` (step M0.5), for `next ⊑ this`, the meet of `this` with its
  /// projection.
  ///
  /// Each finite endpoint of `next` moves outward to the nearest endpoint of `this` or
  /// landmark, and stays where it is when there is none on that side, which is when the
  /// piece of `this` that holds it runs to infinity there. The target is inside that piece
  /// of `this`, so the result lies between `next` and `this`. Its finite endpoints are
  /// endpoints of `this`, landmarks, or a bound that replaced an infinite one of `this`;
  /// the last happens at most once on each side. So the endpoints of every element of a
  /// descending chain of narrowings lie in a finite set, and the chain is finite by the
  /// argument of [widen].
  @override
  IntervalSet narrow(IntervalSet next, Landmarks marks) {
    final ends = _finiteEnds();
    return IntervalSet.fromPieces([
      for (final (lo, hi) in next._pieces)
        (
          switch (lo) {
            Fin(:final v) => Fin(_below(ends, marks, v) ?? v),
            final e => e,
          },
          switch (hi) {
            Fin(:final v) => Fin(_above(ends, marks, v) ?? v),
            final e => e,
          },
        ),
    ]);
  }

  /// The finite endpoints of `this`, of either role, in order (the pieces are disjoint and
  /// sorted).
  List<int> _finiteEnds() => [
    for (final (lo, hi) in _pieces) ...[if (lo case Fin(:final v)) v, if (hi case Fin(:final v)) v],
  ];

  /// The set of `-x` for each member `x`.
  IntervalSet neg() =>
      IntervalSet.fromPieces([for (final (lo, hi) in _pieces) (hi.negLower(), -lo)]);

  /// The image of each piece under `f`, joined.
  IntervalSet lift1(Iterable<Piece> Function(Piece) f) => IntervalSet.fromPieces(_pieces.expand(f));

  /// The pieces split at zero into negative, zero and positive parts, so that each part has
  /// one sign (step M0.5's sign-conditioned tonicity). The parts are listed, not merged.
  List<Piece> signParts() => [
    for (final part in [
      IntervalSet.range(negInf, const Fin(-1)),
      IntervalSet.single(0),
      IntervalSet.range(const Fin(1), posInf),
    ])
      ...meet(part)._pieces,
  ];

  /// The members of `within` that are not members of `this`.
  IntervalSet complementIn(IntervalSet within) {
    final gaps = <Piece>[];
    End from = negInf;
    for (final (lo, hi) in _pieces) {
      if (from is NegInf || from <= lo) gaps.add((from, lo.pred()));
      from = hi.succ();
    }
    if (isEmpty || _pieces.last.$2 is! PosInf) gaps.add((from, posInf));
    return IntervalSet.fromPieces(gaps).meet(within);
  }

  /// The lattice order, inclusion: negative when `this` is a proper subset of `other`, zero
  /// when they are equal, positive when it is a proper superset, and null when neither
  /// contains the other.
  int? compareByInclusion(IntervalSet other) => switch ((isSubset(other), other.isSubset(this))) {
    (true, true) => 0,
    (true, false) => -1,
    (false, true) => 1,
    (false, false) => null,
  };

  @override
  bool operator ==(Object other) {
    if (other is! IntervalSet || other._pieces.length != _pieces.length) return false;
    for (var i = 0; i < _pieces.length; i++) {
      if (_pieces[i] != other._pieces[i]) return false;
    }
    return true;
  }

  @override
  int get hashCode => Object.hashAll(_pieces);

  /// The form of the design's types, without `int`: `[0..=4]`, `[0..]`, `[..=-1, 1..]`, `[]`
  /// for the empty set and `[..]` for every integer.
  @override
  String toString() {
    final out = StringBuffer('[');
    for (var i = 0; i < _pieces.length; i++) {
      if (i > 0) out.write(', ');
      final (lo, hi) = _pieces[i];
      if (lo case Fin(:final v)) out.write(v);
      out.write(switch (hi) {
        Fin(:final v) => '..=$v',
        _ => '..',
      });
    }
    out.write(']');
    return out.toString();
  }
}

/// A piece of [IntervalSet.cap]'s list.
final class _Run {
  /// The place of the piece in the set, which orders the gaps on a tie.
  final int index;
  End lo, hi;
  _Run? next;
  bool alive = true;

  _Run(this.index, this.lo, this.hi);
}

/// A gap between two neighboring pieces of [IntervalSet.cap]'s list.
final class _Gap {
  /// The integers between the two pieces, as an unsigned 64-bit number: the difference of
  /// two finite ends can pass [maxInt], but never 2^64.
  final int width;
  final _Run left;

  /// The right piece's lower end when the gap was added.
  final End rightLo;

  _Gap.between(this.left, _Run right)
    : width = switch ((left.hi, right.lo)) {
        (Fin(v: final hi), Fin(v: final lo)) => lo - hi,
        _ => throw StateError('only the outer endpoints are infinite'),
      },
      rightLo = right.lo;

  static int compare(_Gap a, _Gap b) {
    // Flipping the sign bit orders unsigned numbers as signed ones.
    final c = (a.width ^ minInt).compareTo(b.width ^ minInt);
    if (c != 0) return c;
    final d = a.left.index.compareTo(b.left.index);
    return d != 0 ? d : a.rightLo.compareTo(b.rightLo);
  }
}

/// The least `i` in `0..n` for which `pred(i)` is false, for a `pred` true on a prefix.
int _partition(int n, bool Function(int) pred) {
  var (lo, hi) = (0, n);
  while (lo < hi) {
    final mid = lo + ((hi - lo) >> 1);
    if (pred(mid)) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return lo;
}

/// The greatest of `ends` and the landmarks at or below `v`: where a lower end moves. Two
/// searches, so a widening costs time logarithmic in the landmarks, not linear.
int? _below(List<int> ends, Landmarks marks, int v) {
  final i = _partition(ends.length, (k) => ends[k] <= v);
  final e = i > 0 ? ends[i - 1] : null;
  final m = marks.atOrBelow(v);
  if (e == null) return m;
  if (m == null) return e;
  return e > m ? e : m;
}

/// The least of `ends` and the landmarks at or above `v`: where an upper end moves.
int? _above(List<int> ends, Landmarks marks, int v) {
  final i = _partition(ends.length, (k) => ends[k] < v);
  final e = i < ends.length ? ends[i] : null;
  final m = marks.atOrAbove(v);
  if (e == null) return m;
  if (m == null) return e;
  return e < m ? e : m;
}

extension on int? {
  /// The finite lower end, or `-inf` for none.
  End get asLower => this == null ? negInf : Fin(this!);

  /// The finite upper end, or `inf` for none.
  End get asUpper => this == null ? posInf : Fin(this!);
}
