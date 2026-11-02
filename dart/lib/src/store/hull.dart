/// The affine hull of a set of integer points (Karr's join, step L1.39): the affine equalities
/// that hold at every point, and the join that keeps the equalities two sets both satisfy.
///
/// The equalities are kept in reduced row echelon form over the rationals, each row scaled to
/// integers with no common factor and its first coefficient positive. No row mentions another
/// row's pivot. A new row's pivot is its atom the fewest rows mention, the first of them on a
/// tie, so that adding it rewrites as few rows as it can: rows `x1 - x2`, `x1 - x3`, … each take
/// their last atom and rewrite none, where taking `x1` would rewrite every row before. Two hulls
/// of one set may then have different rows. A row `t` means `t == 0`. The rows are in persistent
/// maps, so a hull made from another by a few changes shares the rest with it, and the join of
/// the two finds the rows that differ in time near their number.
library;

import '../kernel/pmap.dart';
import 'presburger.dart';

int _byAtom(Atom a, Atom b) => a.compareTo(b);

/// The affine hull of a set of points, as the equalities that hold on it.
final class Hull {
  /// The rows by their pivots.
  final PMap<Atom, Lin> _rows;

  /// The pivots of the rows that mention each atom other than their pivot.
  final PMap<Atom, PMap<Atom, bool>> _uses;

  /// Whether the set has no point.
  final bool isEmpty;

  const Hull._(this._rows, this._uses, this.isEmpty);

  /// The hull of every point: no equality.
  static const all = Hull._(PMap.empty(_byAtom), PMap.empty(_byAtom), false);

  /// The hull of the empty set.
  static const empty = Hull._(PMap.empty(_byAtom), PMap.empty(_byAtom), true);

  /// The hull of the points where each term of `terms` is zero.
  factory Hull.of(Iterable<Lin> terms) => terms.fold(all, (h, t) => h.and(t));

  /// The rows, in pivot order.
  Iterable<Lin> get rows => _rows.values;

  /// A constraint that holds at the same points of the hull as `c`, with each row's pivot
  /// replaced by the rest of its row: for a row `k * p + s` and `c` of `a * p + r`, the term
  /// `|k| * (a * p + r) - sign(k) * a * (k * p + s)`, which mentions no `p`. One pass suffices,
  /// since no row mentions another's pivot. The result's coefficients have no common factor: a
  /// `>=` constant is rounded down, and an equality whose constant the factor does not divide is
  /// `false`.
  Formula reduce(Con c) {
    var lin = c.lin;
    for (final a in c.lin.terms.keys) {
      if (_rows[a] case final t?) {
        final k = t.terms[a]!;
        lin = lin.times(k.abs()).minus(t.times(lin.terms[a]! * BigInt.from(k.sign)));
      }
    }
    final g = lin.terms.values.fold(BigInt.zero, (g, c) => g.gcd(c));
    final b = lin.constant;
    if (g == BigInt.zero) {
      return (c.rel == Rel.ge ? b >= BigInt.zero : b == BigInt.zero) ? Formula.top : Formula.bottom;
    }
    if (c.rel == Rel.eq && b % g != BigInt.zero) return Formula.bottom;
    // `%` is the Euclidean remainder, so this rounds down.
    return Con(lin.minus(Lin.constant(b % g)).over(g), c.rel);
  }

  /// The hull of the points of this one where `t` is zero.
  Hull and(Lin t) {
    if (isEmpty) return this;
    var r = t;
    for (final a in t.terms.keys) {
      if (_rows[a] case final p?) r = _eliminate(r, p, a);
    }
    if (r.terms.isEmpty) return r.constant == BigInt.zero ? this : empty;
    r = _primitive(r);
    var pivot = r.terms.firstKey()!;
    for (final a in r.terms.keys) {
      if ((_uses[a]?.length ?? 0) < (_uses[pivot]?.length ?? 0)) pivot = a;
    }
    var (rows, uses) = (_rows, _uses);
    for (final q in [...?_uses[pivot]?.keys]) {
      final old = rows[q]!, now = _eliminate(old, r, pivot);
      uses = _use(_use(uses, old, q, false), now, q, true);
      rows = rows.put(q, now);
    }
    return Hull._(rows.put(pivot, r), _use(uses, r, pivot, true), false);
  }

  /// The hull of the union of the two sets: the equalities both hold. The rows the two have in
  /// common are kept, and the rest are intersected. The rows both span are the common rows
  /// plus what the rest of each span in common, since neither rest mentions a common row's
  /// pivot; so a join of hulls that differ in a few rows costs near the rows that differ.
  Hull join(Hull other) {
    if (isEmpty) return other;
    if (other.isEmpty) return this;
    final a = <Lin>[], b = <Lin>[];
    var out = this;
    for (final p in _rows.diff(other._rows)) {
      final (s, t) = (_rows[p], other._rows[p]);
      if (s == t) continue;
      if (s != null) {
        a.add(s);
        out = Hull._(out._rows.remove(p), _use(out._uses, s, p, false), false);
      }
      if (t != null) b.add(t);
    }
    // The common rows are reduced against each other already.
    return _intersect(a, b).fold(out, (h, t) => h.and(t));
  }

  @override
  String toString() => isEmpty ? 'empty' : [for (final t in rows) '$t == 0'].join(', ');

  /// `uses` with the row `t` at `pivot` added or removed.
  static PMap<Atom, PMap<Atom, bool>> _use(
    PMap<Atom, PMap<Atom, bool>> uses,
    Lin t,
    Atom pivot,
    bool add,
  ) {
    for (final a in t.terms.keys) {
      if (a == pivot) continue;
      final m = uses[a] ?? const PMap.empty(_byAtom);
      final m2 = add ? m.put(pivot, true) : m.remove(pivot);
      uses = m2.isEmpty ? uses.remove(a) : uses.put(a, m2);
    }
    return uses;
  }

  /// `r` with the atom `a` removed by adding a multiple of `p`, whose coefficient of `a` is
  /// positive.
  static Lin _eliminate(Lin r, Lin p, Atom a) {
    final c = r.terms[a];
    return c == null ? r : _primitive(r.times(p.terms[a]!).minus(p.times(c)));
  }

  /// `t` divided by the gcd of its coefficients and constant, its first coefficient positive.
  static Lin _primitive(Lin t) {
    var g = t.terms.values.fold(t.constant, (g, c) => g.gcd(c));
    if (g == BigInt.zero) return t;
    if (t.terms.isNotEmpty && t.terms.values.first.isNegative) g = -g;
    return g == BigInt.one ? t : t.over(g);
  }

  /// Terms spanning the terms both `a` and `b` span (Zassenhaus): each term `t` of `a` enters
  /// as the pair `(t, t)` and each of `b` as `(t, 0)`, and the pairs are brought to echelon form
  /// on their first halves; the second half of a pair whose first half becomes zero is a sum of
  /// terms of `a` that is also a sum of terms of `b`.
  static List<Lin> _intersect(List<Lin> a, List<Lin> b) {
    if (a.isEmpty || b.isEmpty) return const [];
    // The pairs by the first atom of their first half; null for a first half that is a constant.
    final pivots = <Atom?, (Lin, Lin)>{};
    final out = <Lin>[];
    for (var (l, r) in [for (final t in a) (t, t), for (final t in b) (t, Lin.zero)]) {
      while (true) {
        if (l.terms.isEmpty && l.constant == BigInt.zero) {
          out.add(r);
          break;
        }
        final k = l.terms.isEmpty ? null : l.terms.firstKey();
        final p = pivots[k];
        if (p == null) {
          pivots[k] = (l, r);
          break;
        }
        final (pl, pr) = p;
        final (c, cp) = k == null ? (l.constant, pl.constant) : (l.terms[k]!, pl.terms[k]!);
        (l, r) = _pairPrimitive(l.times(cp).minus(pl.times(c)), r.times(cp).minus(pr.times(c)));
      }
    }
    return out;
  }

  /// The pair divided by the gcd of all its coefficients and constants.
  static (Lin, Lin) _pairPrimitive(Lin l, Lin r) {
    BigInt content(Lin t) => t.terms.values.fold(t.constant, (g, c) => g.gcd(c));
    final g = content(l).gcd(content(r));
    return g <= BigInt.one ? (l, r) : (l.over(g), r.over(g));
  }
}
