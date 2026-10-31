//! The interval domain: finite unions of integer intervals with infinite endpoints (DESIGN.md
//! sec:constraints, "Intervals"; widening fixed by step M0.5).
//!
//! An element is a sorted list of disjoint pieces, each `lo..=hi`, with at least one integer
//! missing between two pieces, so that every set has exactly one representation and equality
//! of elements is equality of sets. The empty list is the empty set, the bottom of the lattice.
//! Meet and join are exact.

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;
use std::ops::Neg;

use super::lattice::Landmarks;

/// An endpoint: an integer or one of the two infinities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum End {
    /// Below every integer.
    NegInf,
    /// An integer.
    Fin(i64),
    /// Above every integer.
    PosInf,
}

use End::{Fin, NegInf, PosInf};

impl End {
    /// The endpoint for an exact result `x`, which may lie outside `i64`. A value that does not
    /// fit is replaced by the infinity on its side, which only widens the interval it bounds.
    pub fn from_i128(x: i128) -> End {
        match i64::try_from(x) {
            Ok(v) => Fin(v),
            Err(_) if x < 0 => NegInf,
            Err(_) => PosInf,
        }
    }

    /// The next integer up; the infinities are fixed.
    pub fn succ(self) -> End {
        match self {
            Fin(v) => End::from_i128(v as i128 + 1),
            e => e,
        }
    }

    /// The next integer down; the infinities are fixed.
    pub fn pred(self) -> End {
        match self {
            Fin(v) => End::from_i128(v as i128 - 1),
            e => e,
        }
    }

    /// The sign: -1, 0 or 1.
    pub fn signum(self) -> i8 {
        match self {
            NegInf => -1,
            PosInf => 1,
            Fin(v) => v.signum() as i8,
        }
    }
}

impl Neg for End {
    type Output = End;
    /// The negation, which swaps the infinities.
    fn neg(self) -> End {
        match self {
            NegInf => PosInf,
            PosInf => NegInf,
            Fin(v) => End::from_i128(-(v as i128)),
        }
    }
}

impl fmt::Display for End {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NegInf => write!(f, "-inf"),
            PosInf => write!(f, "inf"),
            Fin(v) => write!(f, "{v}"),
        }
    }
}

/// A finite union of integer intervals.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct IntervalSet {
    pieces: Vec<(End, End)>,
}

impl IntervalSet {
    /// The empty set.
    pub fn empty() -> Self {
        IntervalSet { pieces: Vec::new() }
    }

    /// Every integer.
    pub fn top() -> Self {
        IntervalSet::range(NegInf, PosInf)
    }

    /// The integers from `lo` to `hi`, both included; empty when `lo > hi`.
    pub fn range(lo: End, hi: End) -> Self {
        IntervalSet::from_pieces(vec![(lo, hi)])
    }

    /// The one integer `v`.
    pub fn single(v: i64) -> Self {
        IntervalSet::range(Fin(v), Fin(v))
    }

    /// The integers from `lo` to `hi`, both finite and included.
    pub fn of(lo: i64, hi: i64) -> Self {
        IntervalSet::range(Fin(lo), Fin(hi))
    }

    /// The union of the given pieces, in any order, overlapping or not. A piece whose lower
    /// endpoint is above its upper one, or which has an infinite endpoint on the wrong side, is
    /// empty and is dropped.
    pub fn from_pieces(mut pieces: Vec<(End, End)>) -> Self {
        pieces.retain(|&(lo, hi)| lo <= hi && lo != PosInf && hi != NegInf);
        pieces.sort();
        let mut out: Vec<(End, End)> = Vec::with_capacity(pieces.len());
        for (lo, hi) in pieces {
            match out.last_mut() {
                // Overlapping or adjacent: no integer lies between, so the pieces are one.
                Some(last) if lo <= last.1.succ() => last.1 = last.1.max(hi),
                _ => out.push((lo, hi)),
            }
        }
        IntervalSet { pieces: out }
    }

    /// The pieces, in increasing order.
    pub fn pieces(&self) -> &[(End, End)] {
        &self.pieces
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.pieces.is_empty()
    }

    /// The least and the greatest endpoint, or `None` for the empty set.
    pub fn bounds(&self) -> Option<(End, End)> {
        Some((self.pieces.first()?.0, self.pieces.last()?.1))
    }

    /// The smallest single interval containing the set.
    pub fn hull(&self) -> Self {
        match self.bounds() {
            Some((lo, hi)) => IntervalSet::range(lo, hi),
            None => IntervalSet::empty(),
        }
    }

    /// Whether `v` is a member, by binary search of the pieces.
    pub fn contains(&self, v: i64) -> bool {
        let below = self.pieces.partition_point(|&(lo, _)| lo <= Fin(v));
        below > 0 && Fin(v) <= self.pieces[below - 1].1
    }

    /// The finite endpoints, each with whether it is a lower one; the infinities are left out.
    /// Widening decreases their number (see [`IntervalSet::widen`]).
    pub fn finite_endpoints(&self) -> usize {
        self.pieces
            .iter()
            .map(|&(lo, hi)| usize::from(lo != NegInf) + usize::from(hi != PosInf))
            .sum()
    }

    /// The union, by one merge of the two sorted lists of pieces.
    pub fn join(&self, other: &Self) -> Self {
        let (a, b) = (&self.pieces, &other.pieces);
        let (mut i, mut j) = (0, 0);
        let mut out: Vec<(End, End)> = Vec::with_capacity(a.len() + b.len());
        while i < a.len() || j < b.len() {
            let next = if j == b.len() || (i < a.len() && a[i] <= b[j]) {
                i += 1;
                a[i - 1]
            } else {
                j += 1;
                b[j - 1]
            };
            match out.last_mut() {
                Some(last) if next.0 <= last.1.succ() => last.1 = last.1.max(next.1),
                _ => out.push(next),
            }
        }
        IntervalSet { pieces: out }
    }

    /// The intersection.
    pub fn meet(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::new();
        while i < self.pieces.len() && j < other.pieces.len() {
            let (a, b) = (self.pieces[i], other.pieces[j]);
            let (lo, hi) = (a.0.max(b.0), a.1.min(b.1));
            if lo <= hi {
                out.push((lo, hi));
            }
            if a.1 < b.1 { i += 1 } else { j += 1 }
        }
        IntervalSet { pieces: out }
    }

    /// Whether every member of `self` is a member of `other`.
    pub fn is_subset(&self, other: &Self) -> bool {
        &self.meet(other) == self
    }

    /// The set with at most `limit` pieces: while it has more, the two neighboring pieces with
    /// the fewest integers between them merge into their hull, the lower pair on a tie
    /// (sec:constraints). This is not a join and need not be monotone; forward revision applies
    /// it to bound an image by its operands' pieces.
    pub fn cap(&self, limit: usize) -> Self {
        use std::cmp::Reverse;
        use std::collections::BinaryHeap;
        let limit = limit.max(1);
        let n = self.pieces.len();
        if n <= limit {
            return self.clone();
        }
        // The pieces as a list linked by index, so that a merge is O(1), and the gaps in a
        // heap, smallest first and the lower pair on a tie; a gap whose pieces have changed
        // since it was pushed is skipped when it comes up.
        let mut pieces = self.pieces.clone();
        let mut next: Vec<usize> = (1..=n).collect();
        let mut alive = vec![true; n];
        let gap = |left: (End, End), right: (End, End)| match (left.1, right.0) {
            (Fin(hi), Fin(lo)) => lo as i128 - hi as i128,
            _ => unreachable!("only the outer endpoints are infinite"),
        };
        let mut heap: BinaryHeap<Reverse<(i128, usize, End)>> = (0..n - 1)
            .map(|i| Reverse((gap(pieces[i], pieces[i + 1]), i, pieces[i + 1].0)))
            .collect();
        let mut count = n;
        while count > limit {
            let Reverse((_, at, right_lo)) = heap.pop().expect("a gap for each pair");
            let right = next[at];
            if !alive[at] || right >= n || pieces[right].0 != right_lo {
                continue;
            }
            pieces[at].1 = pieces[right].1;
            alive[right] = false;
            next[at] = next[right];
            if next[at] < n {
                let r = next[at];
                heap.push(Reverse((gap(pieces[at], pieces[r]), at, pieces[r].0)));
            }
            count -= 1;
        }
        IntervalSet {
            pieces: (0..n).filter(|&i| alive[i]).map(|i| pieces[i]).collect(),
        }
    }

    /// The widening `self ∇ next` (step M0.5), for `next` the value that the join would give,
    /// which contains `self`.
    ///
    /// Each finite endpoint of `next` moves outward to the nearest target: an endpoint of
    /// `self`, of either role, or a landmark; with none on that side, to the infinity there.
    /// A lower endpoint moves down and an upper one up, so the result contains `next`, and
    /// pieces that then touch merge. An endpoint of `self` or a landmark stays where it is.
    ///
    /// So the finite endpoints of every element of an ascending chain of widenings lie in
    /// `K`, the first element's endpoints and the landmarks. An element whose endpoints lie in
    /// `K` is a union of some of the `2|K| + 1` parts into which `K` cuts the line (its points
    /// and the gaps between them), so the chain has at most `2|K| + 2` elements. No count of
    /// pieces or of steps enters. The bottom widens to `next` unchanged.
    pub fn widen(&self, next: &Self, marks: &Landmarks) -> Self {
        if self.is_empty() || next == self {
            return next.clone();
        }
        let targets = self.targets(marks);
        let out = next
            .pieces
            .iter()
            .map(|&(lo, hi)| {
                let lo = match lo {
                    Fin(v) => targets.range(..=v).next_back().map_or(NegInf, |&t| Fin(t)),
                    e => e,
                };
                let hi = match hi {
                    Fin(v) => targets.range(v..).next().map_or(PosInf, |&t| Fin(t)),
                    e => e,
                };
                (lo, hi)
            })
            .collect();
        IntervalSet::from_pieces(out)
    }

    /// The narrowing `self Δ next` (step M0.5), for `next ⊑ self`, the meet of `self` with
    /// its projection.
    ///
    /// Each finite endpoint of `next` moves outward to the nearest endpoint of `self` or
    /// landmark, and stays where it is when there is none on that side, which is when the
    /// piece of `self` that holds it runs to infinity there. The target is inside that piece
    /// of `self`, so the result lies between `next` and `self`. Its finite endpoints are
    /// endpoints of `self`, landmarks, or a bound that replaced an infinite one of `self`;
    /// the last happens at most once on each side. So the endpoints of every element of a
    /// descending chain of narrowings lie in a finite set, and the chain is finite by the
    /// argument of [`IntervalSet::widen`].
    pub fn narrow(&self, next: &Self, marks: &Landmarks) -> Self {
        let targets = self.targets(marks);
        let out = next
            .pieces
            .iter()
            .map(|&(lo, hi)| {
                let lo = match lo {
                    Fin(v) => Fin(targets.range(..=v).next_back().map_or(v, |&t| t)),
                    e => e,
                };
                let hi = match hi {
                    Fin(v) => Fin(targets.range(v..).next().map_or(v, |&t| t)),
                    e => e,
                };
                (lo, hi)
            })
            .collect();
        IntervalSet::from_pieces(out)
    }

    /// The finite endpoints of `self`, of either role, and the landmarks.
    fn targets(&self, marks: &Landmarks) -> BTreeSet<i64> {
        let mut t = marks.ints().clone();
        for &(lo, hi) in &self.pieces {
            t.extend([lo, hi].into_iter().filter_map(|e| match e {
                Fin(v) => Some(v),
                _ => None,
            }));
        }
        t
    }

    /// The set of `-x` for each member `x`.
    pub fn neg(&self) -> Self {
        IntervalSet::from_pieces(
            self.pieces
                .iter()
                .map(|&(lo, hi)| (hi.neg(), lo.neg()))
                .collect(),
        )
    }

    /// The image of each piece under `f`, joined.
    pub fn lift1(&self, f: impl Fn((End, End)) -> Vec<(End, End)>) -> Self {
        IntervalSet::from_pieces(self.pieces.iter().flat_map(|&a| f(a)).collect())
    }

    /// The pieces split at zero into negative, zero and positive parts, so that each part has
    /// one sign (step M0.5's sign-conditioned tonicity). The parts are listed, not merged.
    pub fn sign_parts(&self) -> Vec<(End, End)> {
        [
            IntervalSet::range(NegInf, Fin(-1)),
            IntervalSet::single(0),
            IntervalSet::range(Fin(1), PosInf),
        ]
        .iter()
        .flat_map(|part| self.meet(part).pieces)
        .collect()
    }
}

impl PartialOrd for IntervalSet {
    /// The lattice order, inclusion; two sets neither of which contains the other are
    /// unordered.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self.is_subset(other), other.is_subset(self)) {
            (true, true) => Some(Ordering::Equal),
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => None,
        }
    }
}

impl fmt::Display for IntervalSet {
    /// The form of the design's types, without `int`: `[0..=4]`, `[0..]`, `[..=-1, 1..]`,
    /// `[]` for the empty set and `[..]` for every integer.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, &(lo, hi)) in self.pieces.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if let Fin(v) = lo {
                write!(f, "{v}")?;
            }
            match hi {
                Fin(v) => write!(f, "..={v}")?,
                _ => write!(f, "..")?,
            }
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(pieces: &[(i64, i64)]) -> IntervalSet {
        IntervalSet::from_pieces(pieces.iter().map(|&(a, b)| (Fin(a), Fin(b))).collect())
    }

    #[test]
    fn normalization_merges_overlapping_and_adjacent_pieces() {
        assert_eq!(set(&[(5, 7), (0, 2), (3, 3)]), set(&[(0, 3), (5, 7)]));
        assert_eq!(set(&[(0, 2), (1, 9)]).pieces(), &[(Fin(0), Fin(9))]);
        assert!(set(&[(3, 2)]).is_empty());
        assert_eq!(IntervalSet::range(Fin(i64::MAX), PosInf).pieces().len(), 1);
    }

    #[test]
    fn display_uses_the_type_syntax() {
        assert_eq!(set(&[(0, 4)]).to_string(), "[0..=4]");
        assert_eq!(IntervalSet::range(Fin(0), PosInf).to_string(), "[0..]");
        assert_eq!(IntervalSet::top().to_string(), "[..]");
        assert_eq!(
            IntervalSet::from_pieces(vec![(NegInf, Fin(-1)), (Fin(1), PosInf)]).to_string(),
            "[..=-1, 1..]"
        );
        assert_eq!(IntervalSet::empty().to_string(), "[]");
    }

    #[test]
    fn meet_and_join_are_exact_on_small_sets() {
        // Every pair of subsets of 0..6 given as unions: meet and join agree with set algebra.
        let members = |s: &IntervalSet| (0..6).filter(|&v| s.contains(v)).collect::<Vec<_>>();
        let sets: Vec<IntervalSet> = (0u32..64)
            .map(|mask| {
                IntervalSet::from_pieces(
                    (0..6)
                        .filter(|i| mask & (1 << i) != 0)
                        .map(|i| (Fin(i), Fin(i)))
                        .collect(),
                )
            })
            .collect();
        for a in &sets {
            for b in &sets {
                let both: Vec<i64> = members(a).into_iter().filter(|&v| b.contains(v)).collect();
                assert_eq!(members(&a.meet(b)), both);
                let either: Vec<i64> = (0..6).filter(|&v| a.contains(v) || b.contains(v)).collect();
                assert_eq!(members(&a.join(b)), either);
            }
        }
    }

    #[test]
    fn cap_merges_the_smallest_gap_and_the_lower_pair_on_a_tie() {
        let s = set(&[(0, 0), (2, 2), (4, 4), (10, 10)]);
        assert_eq!(s.cap(3), set(&[(0, 2), (4, 4), (10, 10)]));
        assert_eq!(s.cap(2), set(&[(0, 4), (10, 10)]));
        assert_eq!(s.cap(1), set(&[(0, 10)]));
    }

    #[test]
    fn widening_sends_moved_outer_endpoints_to_infinity() {
        let none = Landmarks::none();
        let a = set(&[(0, 2)]);
        assert_eq!(
            a.widen(&set(&[(0, 3)]), &none),
            IntervalSet::range(Fin(0), PosInf)
        );
        assert_eq!(
            a.widen(&set(&[(-1, 2)]), &none),
            IntervalSet::range(NegInf, Fin(2))
        );
        assert_eq!(a.widen(&a, &none), a);
        assert_eq!(IntervalSet::empty().widen(&a, &none), a);
    }

    #[test]
    fn widening_fills_a_gap_that_a_new_inner_endpoint_opens() {
        let none = Landmarks::none();
        // A new piece between two old ones: both of its endpoints are new, so the gaps on both
        // sides are filled.
        let a = set(&[(0, 0), (10, 10)]);
        assert_eq!(
            a.widen(&set(&[(0, 0), (5, 5), (10, 10)]), &none),
            set(&[(0, 10)])
        );
        // An inner endpoint that moves down joins its piece to the one below.
        let a = set(&[(0, 0), (10, 20)]);
        assert_eq!(a.widen(&set(&[(0, 0), (9, 20)]), &none), set(&[(0, 20)]));
    }
}
