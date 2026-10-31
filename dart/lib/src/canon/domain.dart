/// Domain normal forms: the integer facts of a declaration (its interval, congruence and
/// finite-set facets) rewritten to the one representation of the set of integers they admit.
///
/// The set admitted is the meet of the three facts. Its normal form is an interval and a
/// congruence and no finite set: the congruence is the least class holding every member, and
/// the interval's pieces are the maximal runs of class members, each with both endpoints
/// members. A finite set is always expressible this way, so `int[0..=10]` with `1 mod 4`,
/// `int[1..=9]` with `1 mod 4` and the set `{1, 5, 9}` share one normal form.
library;

import '../store/interval.dart';
import '../store/lattice.dart';
import '../store/revision.dart';

/// The integer facts of a declaration.
final class Domain {
  final IntervalSet ints;
  final Congruence congruence;
  final FiniteSet<int> finite;

  const Domain(this.ints, this.congruence, this.finite);

  /// The facts `ints` alone.
  Domain.ints(this.ints) : congruence = Congruence.top, finite = const FiniteSet.top();

  /// Whether `v` is admitted by all three facts.
  bool contains(int v) =>
      ints.contains(v) && congruence.contains(v) && (finite.members?.contains(v) ?? true);

  /// The normal form of the facts. It admits the same integers, and two facts admitting the
  /// same integers have the same normal form.
  Domain normal() {
    // The finite set met into the interval, then the endpoints moved onto the class.
    final (ints, c) = reduceCongruence(reduceFinite(this.ints, finite).$1, congruence);
    if (ints.isEmpty || c.isBottom) {
      return const Domain(IntervalSet.empty(), Congruence.bottom, FiniteSet.top());
    }
    // A piece holding two members holds two that differ by the modulus, so the class is
    // already the least one; when every piece is one point the least class is the join of
    // the points.
    final points = ints.pieces.every((p) => p.$1 is Fin && p.$1 == p.$2);
    final least = points
        ? ints.pieces.fold(Congruence.bottom, (c, p) => c.join(Congruence.single((p.$1 as Fin).v)))
        : c;
    return Domain(_runs(ints, least), least, const FiniteSet.top());
  }

  /// The rank of the domain rule: 1 while the facts are not in normal form.
  int get rank => normal() == this ? 0 : 1;

  @override
  bool operator ==(Object other) =>
      other is Domain &&
      other.ints == ints &&
      other.congruence == congruence &&
      other.finite == finite;

  @override
  int get hashCode => Object.hash(ints, congruence, finite);

  @override
  String toString() => 'Domain($ints, $congruence, $finite)';
}

/// The pieces of `ints`, whose finite endpoints are members of `c`, joined wherever the gap
/// between two pieces holds no member: the next member after a piece's upper endpoint is the
/// following piece's lower endpoint.
IntervalSet _runs(IntervalSet ints, Congruence c) {
  final modulus = c.modulus;
  if (modulus == null) return const IntervalSet.empty();
  final out = <Piece>[];
  for (final (lo, hi) in ints.pieces) {
    if (out.isNotEmpty && modulus > 0 && _joins(out.last.$2, lo, modulus)) {
      out.last = (out.last.$1, hi);
    } else {
      out.add((lo, hi));
    }
  }
  return IntervalSet.fromPieces(out);
}

bool _joins(End hi, End lo, int modulus) => switch ((hi, lo)) {
  (Fin(v: final b), Fin(v: final c)) => BigInt.from(c) - BigInt.from(b) == BigInt.from(modulus),
  _ => false,
};
