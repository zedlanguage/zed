/// The tonicity table, the interval-revision (HC4) table and the reductions between domains
/// (DESIGN.md sec:domains and sec:constraints; written by step M0.5).
///
/// Forward transfer of an operator over intervals is computed from its tonicity: each operand
/// is split at zero into parts of one sign, on which the operator is monotone or antitone in
/// each argument, and the image of a box of such parts is the interval between two of its
/// corners. Backward transfer, the projection onto an operand of a demand on the result, is
/// one entry per operator and operand. Interval revision runs these two over a constraint's
/// tree, one pass up and one down (sec:constraints).
library;

import 'interval.dart';
import 'lattice.dart';

enum _Kind { add, sub, neg, mul, pow, div, mod, abs, min, max }

/// An integer operator of the revision table.
final class Op {
  final _Kind _kind;

  /// The constant exponent of [Op.pow], and 0 for the other operators.
  final int k;

  const Op._(this._kind) : k = 0;

  /// `x ** k` for a constant `k >= 0`.
  const Op.pow(this.k) : _kind = _Kind.pow;

  /// `x + y`.
  static const add = Op._(_Kind.add);

  /// `x - y`.
  static const sub = Op._(_Kind.sub);

  /// `-x`.
  static const neg = Op._(_Kind.neg);

  /// `x * y`.
  static const mul = Op._(_Kind.mul);

  /// `x div y`, Euclidean: the remainder is in `0..abs(y)`.
  static const div = Op._(_Kind.div);

  /// `x mod y`, Euclidean.
  static const mod = Op._(_Kind.mod);

  /// `abs(x)`.
  static const abs = Op._(_Kind.abs);

  /// `min(x, y)`.
  static const min = Op._(_Kind.min);

  /// `max(x, y)`.
  static const max = Op._(_Kind.max);

  /// The number of arguments.
  int get arity => switch (_kind) {
    _Kind.neg || _Kind.pow || _Kind.abs => 1,
    _ => 2,
  };

  @override
  bool operator ==(Object other) => other is Op && other._kind == _kind && other.k == k;

  @override
  int get hashCode => Object.hash(_kind, k);

  @override
  String toString() => _kind == _Kind.pow ? 'pow($k)' : _kind.name;
}

/// How an operator's result moves with one argument, the others fixed.
enum Tonicity {
  /// Monotone: ↑.
  up,

  /// Antitone: ↓.
  down,

  /// Constant.
  constant,

  /// ↑ where the other argument is at least 0, ↓ where it is at most 0.
  upWhereOtherNonneg,

  /// ↓ where the other argument is at least 0, ↑ where it is below 0.
  downWhereOtherNonneg,

  /// ↓ where this argument is at most 0, ↑ where it is at least 0.
  downThenUp,

  /// Neither, on any part of one sign: the operator has its own forward entry.
  none,
}

/// The tonicity table: the entry of operator `op` in argument `arg` (0 or 1).
Tonicity tonicity(Op op, int arg) => switch ((op._kind, arg)) {
  (_Kind.add || _Kind.min || _Kind.max, _) => Tonicity.up,
  (_Kind.sub, 0) => Tonicity.up,
  (_Kind.sub || _Kind.neg, _) => Tonicity.down,
  (_Kind.mul, _) => Tonicity.upWhereOtherNonneg,
  (_Kind.pow, _) when op.k == 0 => Tonicity.constant,
  (_Kind.pow, _) when op.k.isOdd => Tonicity.up,
  (_Kind.pow || _Kind.abs, _) => Tonicity.downThenUp,
  // Euclidean `x div y` rises with x where y > 0 and falls where y < 0; in y it falls where
  // x >= 0 and rises where x < 0, on either side of y = 0.
  (_Kind.div, 0) => Tonicity.upWhereOtherNonneg,
  (_Kind.div, _) => Tonicity.downWhereOtherNonneg,
  (_Kind.mod, _) => Tonicity.none,
};

/// The direction an endpoint is rounded in: down for a lower bound, up for an upper one.
enum _Dir { down, up }

const _zero = Fin(0);

/// The exact result `x` as an endpoint rounded in `dir`.
End _end(BigInt x, _Dir dir) => dir == _Dir.down ? End.lower(x) : End.upper(x);

/// The infinity of the sign, or 0.
End _inf(int sign) => sign < 0
    ? negInf
    : sign > 0
    ? posInf
    : _zero;

/// Whether the product of two such numbers fits in 64 bits.
bool _small(int x) => x > -0x80000000 && x < 0x80000000;

/// `x ** k` exactly, or, when it has more than 64 bits, a number of the same sign that also
/// has more, which rounds as it would.
BigInt _pow(int x, int k) {
  final b = BigInt.from(x);
  if (x.abs() <= 1 && x != minInt || k < 64) return b.pow(k);
  final big = BigInt.one << 64;
  return x < 0 && k.isOdd ? -big : big;
}

/// `op` at two endpoints, rounded outward in `dir` where the result is not an integer or not
/// defined by a limit, such as `inf - inf`.
End _at(Op op, End a, End b, _Dir dir) {
  final outward = dir == _Dir.down ? negInf : posInf;
  return switch ((op._kind, a, b)) {
    (_Kind.add, Fin(v: final x), Fin(v: final y)) => switch (x + y) {
      // Two's-complement overflow: the sum's sign differs from both operands'.
      final s when (x ^ s) & (y ^ s) < 0 => _end(BigInt.from(x) + BigInt.from(y), dir),
      final s => Fin(s),
    },
    (_Kind.add, NegInf(), PosInf()) || (_Kind.add, PosInf(), NegInf()) => outward,
    (_Kind.add, Fin(), final e) || (_Kind.add, final e, _) => e,
    (_Kind.sub, Fin(v: final x), Fin(v: final y)) => switch (x - y) {
      final s when (x ^ y) & (x ^ s) < 0 => _end(BigInt.from(x) - BigInt.from(y), dir),
      final s => Fin(s),
    },
    (_Kind.sub, _, _) => _at(Op.add, a, -b, dir),
    (_Kind.neg, Fin(v: final x), _) => _end(-BigInt.from(x), dir),
    (_Kind.neg, _, _) => -a,
    (_Kind.mul, Fin(v: final x), Fin(v: final y)) =>
      _small(x) && _small(y) ? Fin(x * y) : _end(BigInt.from(x) * BigInt.from(y), dir),
    // 0 times an unbounded operand: every product with a finite member is 0.
    (_Kind.mul, _, _) => _inf(a.sign * b.sign),
    (_Kind.pow, Fin(v: final x), _) => _end(_pow(x, op.k), dir),
    (_Kind.pow, _, _) when op.k == 0 => const Fin(1),
    (_Kind.pow, final e, _) => op.k.isEven ? posInf : e,
    (_Kind.abs, Fin(v: final x), _) => _end(BigInt.from(x).abs(), dir),
    (_Kind.abs, _, _) => a.sign < 0 ? -a : a,
    (_Kind.min, _, _) => a.min(b),
    (_Kind.max, _, _) => a.max(b),
    (_Kind.div, Fin(v: final x), Fin(v: final y)) when y != 0 =>
      x == minInt && y == -1 ? _end(-BigInt.from(x), dir) : Fin(divEuclid(x, y)),
    // A finite numerator over an unbounded divisor: the limit of the Euclidean quotient.
    (_Kind.div, Fin(v: final x), _) when b != _zero =>
      x >= 0
          ? _zero
          : b.sign > 0
          ? const Fin(-1)
          : const Fin(1),
    (_Kind.div, _, Fin(v: final y)) when y != 0 => _inf(a.sign * y.sign),
    _ => outward,
  };
}

/// The image of the box of two pieces, each of one sign, under an operator monotone or
/// antitone in each argument there: the interval between two corners.
Piece _corners(Op op, Piece a, Piece b) {
  bool nonneg(Piece p) => p.$1 >= _zero;
  Tonicity dir(int arg, Piece own, Piece other) => switch (tonicity(op, arg)) {
    Tonicity.upWhereOtherNonneg => nonneg(other) ? Tonicity.up : Tonicity.down,
    Tonicity.downWhereOtherNonneg => nonneg(other) ? Tonicity.down : Tonicity.up,
    Tonicity.downThenUp => nonneg(own) ? Tonicity.up : Tonicity.down,
    final t => t,
  };
  // The endpoint of a piece where the result is least, and where it is greatest.
  Piece pick(Tonicity t, Piece p) => t == Tonicity.down ? (p.$2, p.$1) : p;
  final (alo, ahi) = pick(dir(0, a, b), a);
  final (blo, bhi) = op.arity == 2 ? pick(dir(1, b, a), b) : (_zero, _zero);
  return (_at(op, alo, blo, _Dir.down), _at(op, ahi, bhi, _Dir.up));
}

/// Forward transfer: an interval containing `op` of every choice of members of the operands.
/// For every operator but `mod`, the hull of the result is the hull of the exact image when
/// each operand is one interval.
IntervalSet forward(Op op, IntervalSet x, IntervalSet y) {
  final xs = x.signParts();
  List<Piece> corners(Piece a, Piece b) => [_corners(op, a, b)];
  return switch (op._kind) {
    _Kind.mod => _map2(xs, y.pieces, _forwardMod),
    _Kind.div => _map2(xs, IntervalSet.single(0).complementIn(y).signParts(), corners),
    _ when op.arity == 1 => _map2(xs, const [(_zero, _zero)], corners),
    _ => _map2(xs, y.signParts(), corners),
  };
}

/// `x mod y` for one piece of each: `0..abs(y)`, or the piece of `x` itself shifted when one
/// constant divisor maps it without wrapping.
List<Piece> _forwardMod(Piece a, Piece b) {
  if (b == (_zero, _zero)) return const [];
  if ((a, b) case ((Fin(v: final lo), Fin(v: final hi)), (Fin(v: final c), final d))
      when b.$1 == d &&
          // hi - lo and abs(c) compared as unsigned numbers, which both are exactly.
          ((hi - lo) ^ minInt) < (c.abs() ^ minInt) &&
          lo % c <= hi % c) {
    return [(Fin(lo % c), Fin(hi % c))];
  }
  // The remainder is below the largest abs(y), and for x >= 0 at most x.
  var top = switch ((-b.$1).max(b.$2)) {
    Fin(:final v) => Fin(v - 1),
    final e => e,
  };
  if (a.$1 >= _zero) top = top.min(a.$2);
  return [(_zero, top)];
}

/// The sign region of a part: 0 negative, 1 zero, 2 positive.
int _region(Piece p) => p.$2 < _zero
    ? 0
    : p.$1 > _zero
    ? 2
    : 1;

/// The parts split at zero, grouped by sign region.
List<List<Piece>> _regions(Iterable<Piece> parts) {
  final out = [<Piece>[], <Piece>[], <Piece>[]];
  for (final p in IntervalSet.fromPieces(parts).signParts()) {
    out[_region(p)].add(p);
  }
  return out;
}

/// The image of each pair of parts under `f`, joined, with work linear in the operands and no
/// constant bound. The operand with fewer parts is first capped to `ceil((k + m) / k)` pieces
/// for `k >= m` parts, so the pairs are at most `k + m`; and each sign region of the image is
/// capped to the most pieces either operand has in one region, so no chain of operators
/// multiplies piece counts (the rule of low complexity, Part G). With one operand of one
/// piece, nothing is merged before the image is taken.
IntervalSet _map2(List<Piece> a, List<Piece> b, List<Piece> Function(Piece, Piece) f) {
  final (ra, rb) = (_regions(a), _regions(b));
  final most = [...ra, ...rb].fold(0, (m, r) => r.length > m ? r.length : m);
  List<Piece> shrink(List<List<Piece>> r, int big, int small) {
    final cap = (big + small + (big > 1 ? big : 1) - 1) ~/ (big > 1 ? big : 1);
    return IntervalSet.fromPieces(r.expand((p) => p)).cap(cap).signParts();
  }

  final (na, nb) = (a.length, b.length);
  final (pa, pb) = na >= nb
      ? ([...ra.expand((p) => p)], shrink(rb, na, nb))
      : (shrink(ra, nb, na), [...rb.expand((p) => p)]);
  final image = IntervalSet.fromPieces([
    for (final p in pa)
      for (final q in pb) ...f(p, q),
  ]);
  return IntervalSet.fromPieces([
    for (final ps in _regions(image.pieces))
      ...IntervalSet.fromPieces(ps).cap(most > 1 ? most : 1).pieces,
  ]);
}

/// The real quotient `z / y` at two endpoints, rounded outward in `dir`.
End _quotient(End z, End y, _Dir dir) {
  switch ((z, y)) {
    case (Fin(v: final n), Fin(v: final d)) when d != 0:
      // The real quotient's floor and ceiling; only minInt / -1 leaves 64 bits.
      if (n == minInt && d == -1) return _end(-BigInt.from(n), dir);
      final q = divEuclid(n, d), exact = n % d == 0;
      // Euclidean division rounds toward -inf for d > 0 and toward +inf for d < 0.
      final floor = !exact && d < 0 ? q - 1 : q;
      return Fin(dir == _Dir.down || exact ? floor : floor + 1);
    case (Fin(), _) when y != _zero:
      return _zero;
    case (_, Fin(v: final d)) when d != 0:
      return z.sign * d.sign > 0 ? posInf : negInf;
    default:
      return dir == _Dir.down ? negInf : posInf;
  }
}

/// Backward transfer: the members of operand `arg` (0 or 1) of `op` that can give a result in
/// `z` with the other operand in its interval. The result is contained in the operand's
/// interval, and contains every member that can give a result in `z`.
IntervalSet backward(Op op, int arg, IntervalSet x, IntervalSet y, IntervalSet z) {
  final (own, other) = arg == 0 ? (x, y) : (y, x);
  final narrowed = switch ((op._kind, arg)) {
    (_Kind.add, _) => forward(Op.sub, z, other),
    (_Kind.sub, 0) => forward(Op.add, z, y),
    (_Kind.sub, _) => forward(Op.sub, x, z),
    (_Kind.neg, _) => z.neg(),
    (_Kind.mul, _) when z.contains(0) && other.contains(0) => IntervalSet.top(),
    (_Kind.mul, _) => _map2(z.signParts(), IntervalSet.single(0).complementIn(other).signParts(), (
      zp,
      yp,
    ) {
      // z / y over a box of one sign in each: monotone in each argument, so its extremes
      // are among the four corners.
      final qs = [(zp.$1, yp.$1), (zp.$1, yp.$2), (zp.$2, yp.$1), (zp.$2, yp.$2)];
      return [
        (
          qs.map((q) => _quotient(q.$1, q.$2, _Dir.down)).reduce((m, e) => m.min(e)),
          qs.map((q) => _quotient(q.$1, q.$2, _Dir.up)).reduce((m, e) => m.max(e)),
        ),
      ];
    }),
    (_Kind.pow, _) when op.k == 0 => IntervalSet.top(),
    (_Kind.pow, _) => z.lift1((p) => _roots(op.k, p.$1, p.$2)),
    (_Kind.abs, _) => z.lift1((p) {
      final lo = p.$1.max(_zero);
      return [(p.$2.negLower(), -lo), (lo, p.$2)];
    }),
    (_Kind.min, _) => switch ((z.bounds, other.bounds)) {
      ((_, final zhi)?, (final olo, _)?) when olo > zhi => z,
      ((final zlo, _)?, _) => IntervalSet.range(zlo, posInf),
      (null, _) => const IntervalSet.empty(),
    },
    (_Kind.max, _) => switch ((z.bounds, other.bounds)) {
      ((final zlo, _)?, (_, final ohi)?) when ohi < zlo => z,
      ((_, final zhi)?, _) => IntervalSet.range(negInf, zhi),
      (null, _) => const IntervalSet.empty(),
    },
    // x = q * y + r with q in z and r in 0..abs(y).
    (_Kind.div, 0) => forward(
      Op.add,
      forward(Op.mul, z, y),
      IntervalSet.range(_zero, (forward(Op.abs, y, y).bounds?.$2 ?? _zero).pred()),
    ),
    // A remainder r needs abs(y) > r.
    (_Kind.mod, 1) => switch (z.bounds) {
      (Fin(v: final r), _)? when r >= 0 => IntervalSet.fromPieces([
        (negInf, Fin(-r - 1)),
        (End.lower(BigInt.from(r) + BigInt.one), posInf),
      ]),
      _? => IntervalSet.top(),
      null => const IntervalSet.empty(),
    },
    (_Kind.div || _Kind.mod, _) => IntervalSet.top(),
  };
  return own.meet(narrowed);
}

/// Whether `m ** k <= v`, for `m` and `v` not negative.
bool _powAtMost(int m, int k, int v) {
  var p = 1;
  for (var i = 0; i < k; i++) {
    if (m != 0 && p > v ~/ m) return false;
    p *= m;
  }
  return true;
}

/// The largest `r >= 0` with `r ** k <= v`, for `v >= 0` and `k >= 1`; `inf` for `v = inf`.
End _floorRoot(int k, End v) {
  if (v is! Fin) return posInf;
  var (lo, hi) = (0, v.v > 1 ? v.v : 1);
  while (lo < hi) {
    final mid = lo + ((hi - lo + 1) >> 1);
    if (_powAtMost(mid, k, v.v)) {
      lo = mid;
    } else {
      hi = mid - 1;
    }
  }
  return Fin(lo);
}

/// The least `r >= 0` with `r ** k >= v`, for `v >= 0` and `k >= 1`.
End _ceilRoot(int k, End v) {
  final r = _floorRoot(k, v);
  // The floor root `r` has `r ** k <= w`; it is the ceiling too when the power is `w`.
  if ((r, v) case (Fin(v: final r), Fin(v: final w)) when w > 0 && _powAtMost(r, k, w - 1)) {
    return Fin(r + 1);
  }
  return r;
}

/// The members of `x` with `x ** k` in `lo..=hi`, for `k >= 1`, as at most two pieces.
List<Piece> _roots(int k, End lo, End hi) {
  if (k.isOdd) {
    // Odd powers are increasing, and odd about 0.
    End up(End v) => v >= _zero ? _floorRoot(k, v) : -_ceilRoot(k, -v);
    End down(End v) => v >= _zero ? _ceilRoot(k, v) : -_floorRoot(k, -v);
    return [(down(lo), up(hi))];
  }
  if (hi < _zero) return const [];
  final (rLo, rHi) = (_ceilRoot(k, lo.max(_zero)), _floorRoot(k, hi));
  return [(rHi.negLower(), -rLo), (rLo, rHi)];
}

/// The reduction between an interval and a congruence (sec:constraints): each piece's
/// endpoints move inward to the nearest members of the class, and a single value fixes the
/// other domain.
(IntervalSet, Congruence) reduceCongruence(IntervalSet x, Congruence c) {
  final residue = c.residue;
  final IntervalSet reduced;
  switch (c.modulus) {
    case null:
      return (const IntervalSet.empty(), Congruence.bottom);
    case 0:
      reduced = x.meet(IntervalSet.single(residue));
    case 1:
      reduced = x;
    case final m:
      final (bm, br) = (BigInt.from(m), BigInt.from(residue));
      End up(End e) => switch (e) {
        Fin(:final v) => End.lower(BigInt.from(v) + (br - BigInt.from(v)) % bm),
        _ => e,
      };
      End down(End e) => switch (e) {
        Fin(:final v) => End.upper(BigInt.from(v) - (BigInt.from(v) - br) % bm),
        _ => e,
      };
      reduced = x.lift1((p) => [(up(p.$1), down(p.$2))]);
  }
  final fixed = switch (reduced.bounds) {
    null => Congruence.bottom,
    (Fin(v: final a), Fin(v: final b)) when a == b => c.meet(Congruence.single(a)),
    _ => c,
  };
  return (reduced, fixed);
}

/// The reduction between an interval and a finite set of integers: each is met with the
/// other.
(IntervalSet, FiniteSet<int>) reduceFinite(IntervalSet x, FiniteSet<int> s) {
  final members = s.members;
  if (members == null) return (x, s);
  final kept = FiniteSet.of(members.where(x.contains));
  final points = IntervalSet.fromPieces([for (final v in kept.members!) (Fin(v), Fin(v))]);
  return (x.meet(points), kept);
}
