//! The interval domain: finite unions of integer intervals with infinite endpoints (DESIGN.md
//! sec:constraints, "Intervals"; widening fixed by step M0.5).
//!
//! An element is a sorted list of disjoint pieces, each `lo..=hi`, with at least one integer
//! missing between two pieces, so that every set has exactly one representation and equality
//! of elements is equality of sets. The empty list is the empty set, the bottom of the lattice.
//! Meet and join are exact.
//!
//! An end is an unbounded integer ([`Num`]): one machine word while it fits in `i64`, a
//! `BigInt` past it. No end is rounded or dropped at any magnitude, since `int` is unbounded.

use std::cmp::Ordering;
use std::fmt;
use std::ops::Neg;

use zed_kernel::{Prim, Value};

pub use super::int::Num;
use super::lattice::Landmarks;

/// An endpoint: an integer or one of the two infinities.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum End {
    /// Below every integer.
    NegInf,
    /// An integer.
    Fin(Num),
    /// Above every integer.
    PosInf,
}

use End::{Fin, NegInf, PosInf};

impl From<i64> for End {
    fn from(v: i64) -> End {
        Fin(Num::from(v))
    }
}

impl From<i128> for End {
    fn from(v: i128) -> End {
        Fin(Num::from(v))
    }
}

impl End {
    /// The integer `v`.
    pub fn of(v: i64) -> End {
        Fin(Num::from(v))
    }

    /// The integer, when the end is finite and fits in `i64`.
    pub fn to_i64(&self) -> Option<i64> {
        match self {
            Fin(v) => v.to_i64(),
            _ => None,
        }
    }

    /// The next integer up; the infinities are fixed.
    pub fn succ(&self) -> End {
        match self {
            Fin(v) => Fin(v + &Num::ONE),
            e => e.clone(),
        }
    }

    /// Whether `self <= other.succ()`, without expanding a kept power ([`Num::at_most_succ`]).
    pub fn at_most_succ(&self, other: &End) -> bool {
        match (self, other) {
            (Fin(a), Fin(b)) => a.at_most_succ(b),
            _ => *self <= other.succ(),
        }
    }

    /// The next integer down; the infinities are fixed.
    pub fn pred(&self) -> End {
        match self {
            Fin(v) => Fin(v - &Num::ONE),
            e => e.clone(),
        }
    }

    /// The sign: -1, 0 or 1.
    pub fn signum(&self) -> i8 {
        match self {
            NegInf => -1,
            PosInf => 1,
            Fin(v) => v.signum(),
        }
    }
}

impl Neg for &End {
    type Output = End;
    /// The negation, which swaps the infinities.
    fn neg(self) -> End {
        match self {
            NegInf => PosInf,
            PosInf => NegInf,
            Fin(v) => Fin(-v),
        }
    }
}

impl Neg for End {
    type Output = End;
    fn neg(self) -> End {
        -&self
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
        IntervalSet::range(End::of(v), End::of(v))
    }

    /// The one integer `v`, of any size.
    pub fn point(v: Num) -> Self {
        IntervalSet::range(Fin(v.clone()), Fin(v))
    }

    /// The integers from `lo` to `hi`, both finite and included.
    pub fn of(lo: i64, hi: i64) -> Self {
        IntervalSet::range(End::of(lo), End::of(hi))
    }

    /// The union of the given pieces, in any order, overlapping or not. A piece whose lower
    /// endpoint is above its upper one, or which has an infinite endpoint on the wrong side, is
    /// empty and is dropped.
    pub fn from_pieces(mut pieces: Vec<(End, End)>) -> Self {
        pieces.retain(|(lo, hi)| lo <= hi && *lo != PosInf && *hi != NegInf);
        pieces.sort();
        let mut out: Vec<(End, End)> = Vec::with_capacity(pieces.len());
        for (lo, hi) in pieces {
            push_merged(&mut out, lo, hi);
        }
        IntervalSet { pieces: out }
    }

    /// The pieces, in increasing order.
    pub fn pieces(&self) -> &[(End, End)] {
        &self.pieces
    }

    /// The pieces, in increasing order, taken by value.
    pub fn into_pieces(self) -> Vec<(End, End)> {
        self.pieces
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.pieces.is_empty()
    }

    /// The least and the greatest endpoint, or `None` for the empty set.
    pub fn bounds(&self) -> Option<(&End, &End)> {
        Some((&self.pieces.first()?.0, &self.pieces.last()?.1))
    }

    /// The smallest single interval containing the set.
    pub fn hull(&self) -> Self {
        match self.bounds() {
            Some((lo, hi)) => IntervalSet::range(lo.clone(), hi.clone()),
            None => IntervalSet::empty(),
        }
    }

    /// Whether `v` is a member, by binary search of the pieces.
    pub fn contains(&self, v: i64) -> bool {
        self.contains_end(&End::of(v))
    }

    /// Whether the finite end `v` is a member, by binary search of the pieces.
    pub fn contains_end(&self, v: &End) -> bool {
        let below = self.pieces.partition_point(|(lo, _)| lo <= v);
        below > 0 && *v <= self.pieces[below - 1].1
    }

    /// The finite endpoints, each with whether it is a lower one; the infinities are left out.
    /// Widening decreases their number (see [`IntervalSet::widen`]).
    pub fn finite_endpoints(&self) -> usize {
        self.pieces
            .iter()
            .map(|(lo, hi)| usize::from(*lo != NegInf) + usize::from(*hi != PosInf))
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
                &a[i - 1]
            } else {
                j += 1;
                &b[j - 1]
            };
            push_merged(&mut out, next.0.clone(), next.1.clone());
        }
        IntervalSet { pieces: out }
    }

    /// The intersection.
    pub fn meet(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::new();
        while i < self.pieces.len() && j < other.pieces.len() {
            let (a, b) = (&self.pieces[i], &other.pieces[j]);
            let (lo, hi) = ((&a.0).max(&b.0), (&a.1).min(&b.1));
            if lo <= hi {
                out.push((lo.clone(), hi.clone()));
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
        // since it was pushed is skipped when it comes up. A piece's lower end never changes,
        // so the heap holds the index of the right piece, not its end.
        let mut pieces = self.pieces.clone();
        let mut next: Vec<usize> = (1..=n).collect();
        let mut alive = vec![true; n];
        let gap = |left: &(End, End), right: &(End, End)| match (&left.1, &right.0) {
            (Fin(hi), Fin(lo)) => lo - hi,
            _ => unreachable!("only the outer endpoints are infinite"),
        };
        let mut heap: BinaryHeap<Reverse<(Num, usize, usize)>> = (0..n - 1)
            .map(|i| Reverse((gap(&pieces[i], &pieces[i + 1]), i, i + 1)))
            .collect();
        let mut count = n;
        while count > limit {
            let Reverse((_, at, right_was)) = heap.pop().expect("a gap for each pair");
            let right = next[at];
            if !alive[at] || right >= n || right != right_was {
                continue;
            }
            pieces[at].1 = std::mem::replace(&mut pieces[right].1, NegInf);
            alive[right] = false;
            next[at] = next[right];
            if next[at] < n {
                let r = next[at];
                heap.push(Reverse((gap(&pieces[at], &pieces[r]), at, r)));
            }
            count -= 1;
        }
        IntervalSet {
            pieces: pieces
                .into_iter()
                .zip(alive)
                .filter_map(|(p, a)| a.then_some(p))
                .collect(),
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
    ///
    /// Complexity tradeoff: an end that grows past the old ends and the landmarks goes to the
    /// next landmark or to infinity, so a loop's bound that no literal names is lost (a
    /// growing buffer length gets `0..`). Why: the lattice has infinite
    /// ascending chains, so a fixpoint without widening need not be reached; with it a head is
    /// evaluated O(|K|) times. Trigger: a loop whose bound is not among the program's integer
    /// literals plus or minus one. Tests:
    /// `m0_05_widening_and_iteration::widening::a_moved_endpoint_goes_to_the_next_landmark_or_infinity`,
    /// `m0_05_widening_and_iteration::widening::interval_widening_chains_stay_on_the_first_ends_and_the_landmarks`.
    /// COMPLEXITY.md row S13. Narrowing ([`IntervalSet::narrow`]) and the symbolic bounds
    /// (`affine`) recover part of what is lost. A complete solution would solve the loop's
    /// recurrence exactly (acceleration), which is possible for affine loops only and
    /// undecidable in general.
    pub fn widen(&self, next: &Self, marks: &Landmarks) -> Self {
        if self.is_empty() || next == self {
            return next.clone();
        }
        let ends = self.finite_ends();
        let out = next
            .pieces
            .iter()
            .map(|(lo, hi)| {
                let lo = match lo {
                    Fin(v) => below(&ends, marks, v).map_or(NegInf, Fin),
                    e => e.clone(),
                };
                let hi = match hi {
                    Fin(v) => above(&ends, marks, v).map_or(PosInf, Fin),
                    e => e.clone(),
                };
                (lo, hi)
            })
            .collect();
        IntervalSet::from_pieces(out)
    }

    /// The least set holding `self` whose finite ends are landmarks: each end of each piece
    /// moves out to the nearest landmark on its side, or to infinity when there is none. Its
    /// ends lie in a finite set, so there are finitely many results for one set of landmarks.
    pub fn snap(&self, marks: &Landmarks) -> Self {
        let out = self
            .pieces
            .iter()
            .map(|(lo, hi)| {
                let lo = match lo {
                    Fin(v) => landmark_below(marks, v).map_or(NegInf, Fin),
                    e => e.clone(),
                };
                let hi = match hi {
                    Fin(v) => landmark_above(marks, v).map_or(PosInf, Fin),
                    e => e.clone(),
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
    ///
    /// Complexity tradeoff: a finite end of `next` moves back out to the nearest end of `self`
    /// or landmark on its side, so a tighter bound that a loop shows between landmarks is lost
    /// (`0..=99` narrowed by `5..=50` stays `0..=99`). Why: interval sets have infinite
    /// descending chains (`0..=99`, `0..=98`, …), so taking the meet at each step need not
    /// end; with this rule a chain of narrowings has O(|K|) elements. Trigger: a finite end of
    /// `next` with an end of `self` or a landmark beyond it on its side. Tests:
    /// `m0_05_widening_and_iteration::widening::a_narrowing_keeps_old_ends_and_takes_a_bound_for_an_infinite_one`,
    /// `m0_05_widening_and_iteration::widening::interval_narrowing_chains_stay_on_the_first_ends_and_the_landmarks`.
    /// COMPLEXITY.md row C8 (S13 measures the widening phase). A complete solution
    /// would compute the greatest fixpoint below the widened one, which needs the loop's
    /// recurrence solved exactly (acceleration): possible for affine loops only, undecidable
    /// in general.
    pub fn narrow(&self, next: &Self, marks: &Landmarks) -> Self {
        let ends = self.finite_ends();
        let out = next
            .pieces
            .iter()
            .map(|(lo, hi)| {
                let lo = match lo {
                    Fin(v) => Fin(below(&ends, marks, v).unwrap_or_else(|| v.clone())),
                    e => e.clone(),
                };
                let hi = match hi {
                    Fin(v) => Fin(above(&ends, marks, v).unwrap_or_else(|| v.clone())),
                    e => e.clone(),
                };
                (lo, hi)
            })
            .collect();
        IntervalSet::from_pieces(out)
    }

    /// The finite endpoints of `self`, of either role, in order (the pieces are disjoint and
    /// sorted).
    fn finite_ends(&self) -> Vec<&Num> {
        self.pieces
            .iter()
            .flat_map(|(lo, hi)| [lo, hi])
            .filter_map(|e| match e {
                Fin(v) => Some(v),
                _ => None,
            })
            .collect()
    }

    /// The set of `-x` for each member `x`.
    pub fn neg(&self) -> Self {
        IntervalSet::from_pieces(self.pieces.iter().map(|(lo, hi)| (-hi, -lo)).collect())
    }

    /// The image of each piece under `f`, joined.
    pub fn lift1(&self, f: impl Fn(&(End, End)) -> Vec<(End, End)>) -> Self {
        IntervalSet::from_pieces(self.pieces.iter().flat_map(f).collect())
    }

    /// The pieces split at zero into negative, zero and positive parts, so that each part has
    /// one sign (step M0.5's sign-conditioned tonicity). The parts are listed, not merged.
    pub fn sign_parts(&self) -> Vec<(End, End)> {
        [
            IntervalSet::range(NegInf, End::of(-1)),
            IntervalSet::single(0),
            IntervalSet::range(End::of(1), PosInf),
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
        for (i, (lo, hi)) in self.pieces.iter().enumerate() {
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

/// Appends the piece `lo..=hi` to `out`, whose pieces are sorted and end at or before `lo`'s
/// piece starts, merging it into the last piece when the two overlap or touch.
fn push_merged(out: &mut Vec<(End, End)>, lo: End, hi: End) {
    match out.last_mut() {
        // Overlapping or adjacent: no integer lies between, so the pieces are one.
        Some(last) if lo.at_most_succ(&last.1) => {
            if hi > last.1 {
                last.1 = hi;
            }
        }
        _ => out.push((lo, hi)),
    }
}

/// The greatest landmark at or below `v`.
fn landmark_below(marks: &Landmarks, v: &Num) -> Option<Num> {
    marks.ints().range(..=v).next_back().cloned()
}

/// The least landmark at or above `v`: [`landmark_below`] mirrored.
fn landmark_above(marks: &Landmarks, v: &Num) -> Option<Num> {
    marks.ints().range(v..).next().cloned()
}

/// The greatest of `ends` and the landmarks at or below `v`: where a lower end moves. Two
/// searches, so a widening costs time logarithmic in the landmarks, not linear.
fn below(ends: &[&Num], marks: &Landmarks, v: &Num) -> Option<Num> {
    let e = ends[..ends.partition_point(|&t| t <= v)].last().copied();
    let m = landmark_below(marks, v);
    match (e, m) {
        (Some(a), Some(b)) => Some(a.max(&b).clone()),
        (Some(a), None) => Some(a.clone()),
        (None, b) => b,
    }
}

/// The least of `ends` and the landmarks at or above `v`: where an upper end moves.
fn above(ends: &[&Num], marks: &Landmarks, v: &Num) -> Option<Num> {
    let e = ends.get(ends.partition_point(|&t| t < v)).copied();
    let m = landmark_above(marks, v);
    match (e, m) {
        (Some(a), Some(b)) => Some(a.min(&b).clone()),
        (Some(a), None) => Some(a.clone()),
        (None, b) => b,
    }
}

/// The binary digits of a non-negative `n`: the least `b` with `n < 2^b`.
fn digits(n: &Num) -> Num {
    n.bits()
}

/// `2^e - 1` for `e >= 0`: the largest value of `e` binary digits.
fn ones(e: &Num) -> Num {
    &Num::pow2(e) - &Num::ONE
}

/// The finite value of an end known to be finite.
fn fin(e: &End) -> &Num {
    match e {
        Fin(v) => v,
        _ => unreachable!("a bound of a non-negative operand is finite below"),
    }
}

/// Forward transfer of a bit word (step L1.39a, DESIGN.md sec:domains) on the intervals of its
/// int operands, in parameter order with the width last: a set holding `p(args)` for every
/// tuple of members on which `p` is defined. Each operand is first met with its domain,
/// `int[0..]` for every one but the `x` of `shl` and `shr`, and the `x` of a word with a width
/// with `int[0..<2 ** w]` for the largest `w`; an operand left empty gives the empty set, and
/// operands that are each one integer give the word's value. Every end is exact at any size.
///
/// `bitAnd` lies in `0..=min(hi_a, hi_b)`, `bitOr` and `bitXor` below the least power of two
/// above the larger upper bound (`bitOr` from the larger lower bound), `bitNot` in
/// `2^w - 1 - x` over the corners, `popCount` in `0..=digits(hi_x)` (from 1 when 0 is not a
/// member), `leadingZeros` in `w - digits(x)` over the corners, `trailingZeros` in `w` when `x`
/// is 0 and in `0..digits(hi_x)` otherwise, and `rotl` and `rotr` below `2^w`, 0 exactly when
/// `x` is. `shl` and `shr` are the product and the floor quotient by `2^k`, monotone in `x` and,
/// on each sign of `x`, in `k`, so each sign part of each piece of `x` maps by its corners; a
/// shift right by at least the digits of `x` gives 0 or -1, so `k` is read up to those digits.
/// `f64Bits` is in `int[0..<2 ** 64]`.
///
/// Complexity tradeoff: every operand but the `x` of `shl` and `shr` is read by its hull, and
/// the result is at most two intervals, so a hole in an operand is not carried through and the
/// digit-wise words are bounded by their operands' digits, not by the digits they share. Why:
/// these words are not monotone, so an exact image of unions of pieces is a search over the
/// pieces' digits, and the hull rule is O(1) per word; `shl` and `shr` are monotone on each
/// sign and keep their `x` pieces at O(pieces). Trigger: an operand of more than one piece,
/// or of more than one value for `bitAnd`, `bitOr` and `bitXor`. Tests:
/// `l01_39a_bit_words::transfer`. A complete solution would add the known-bits domain of step
/// L1.40a, which carries the digits fixed in every member. COMPLEXITY.md row C25.
pub fn bit_word(p: Prim, args: &[IntervalSet]) -> IntervalSet {
    let nonneg = IntervalSet::range(End::of(0), PosInf);
    if p == Prim::F64Bits {
        return IntervalSet::range(End::of(0), Fin(ones(&Num::from(64))));
    }
    let shift = matches!(p, Prim::Shl | Prim::Shr);
    let mut xs: Vec<IntervalSet> = args
        .iter()
        .enumerate()
        .map(|(i, a)| match shift && i == 0 {
            true => a.clone(),
            false => a.meet(&nonneg),
        })
        .collect();
    let width = matches!(
        p,
        Prim::BitNot | Prim::LeadingZeros | Prim::TrailingZeros | Prim::Rotl | Prim::Rotr
    );
    if width && let Some((_, Fin(wh))) = xs.last().and_then(IntervalSet::bounds) {
        let within = IntervalSet::range(End::of(0), Fin(ones(wh)));
        xs[0] = xs[0].meet(&within);
    }
    if xs.iter().any(IntervalSet::is_empty) {
        return IntervalSet::empty();
    }
    let one = |s: &IntervalSet| match s.bounds() {
        Some((Fin(a), Fin(b))) if a == b => Some(Value::from(a)),
        _ => None,
    };
    if let Some(vs) = xs.iter().map(one).collect::<Option<Vec<Value>>>() {
        match zed_kernel::bits::word(p, &vs) {
            Ok(Value::Int(v)) => return IntervalSet::single(v),
            Ok(Value::Big(v)) => return IntervalSet::point(Num::from(&*v)),
            Err(zed_kernel::KernelError::Type(_)) => return IntervalSet::empty(),
            // A value the system could not build: the rules below.
            _ => {}
        }
    }
    let b = |i: usize| xs[i].bounds().expect("not empty");
    let mask = |h: &End| match h {
        Fin(v) => Fin(ones(&digits(v))),
        e => e.clone(),
    };
    let (x_lo, x_hi) = b(0);
    match p {
        Prim::BitAnd => IntervalSet::range(End::of(0), x_hi.min(b(1).1).clone()),
        Prim::BitOr => IntervalSet::range(x_lo.max(b(1).0).clone(), mask(x_hi.max(b(1).1))),
        Prim::BitXor => IntervalSet::range(End::of(0), mask(x_hi.max(b(1).1))),
        Prim::PopCount => IntervalSet::range(
            End::of(i64::from(fin(x_lo).signum() > 0)),
            match x_hi {
                Fin(v) => Fin(digits(v)),
                e => e.clone(),
            },
        ),
        Prim::BitNot => {
            let (w_lo, w_hi) = b(1);
            let lo = match x_hi {
                Fin(x) => Fin((&ones(fin(w_lo)) - x).max(Num::ZERO)),
                _ => End::of(0),
            };
            let hi = match w_hi {
                Fin(w) => Fin(&ones(w) - fin(x_lo)),
                e => e.clone(),
            };
            IntervalSet::range(lo, hi)
        }
        Prim::LeadingZeros => {
            let (w_lo, w_hi) = b(1);
            let lo = match x_hi {
                Fin(x) => Fin((fin(w_lo) - &digits(x)).max(Num::ZERO)),
                _ => End::of(0),
            };
            let hi = match w_hi {
                Fin(w) => Fin(w - &digits(fin(x_lo))),
                e => e.clone(),
            };
            IntervalSet::range(lo, hi)
        }
        Prim::TrailingZeros => {
            let (w_lo, w_hi) = b(1);
            let mut pieces = Vec::new();
            if fin(x_lo).is_zero() {
                pieces.push((w_lo.clone(), w_hi.clone()));
            }
            let positive = xs[0].meet(&IntervalSet::range(End::of(1), PosInf));
            match positive.bounds() {
                Some((Fin(a), Fin(z))) if a == z => {
                    let t = Fin(a.trailing_zeros());
                    pieces.push((t.clone(), t));
                }
                Some((_, Fin(z))) => {
                    pieces.push((End::of(0), Fin(&digits(z) - &Num::ONE).min(w_hi.clone())))
                }
                Some((_, hi)) => pieces.push((End::of(0), hi.clone().min(w_hi.clone()))),
                None => {}
            }
            IntervalSet::from_pieces(pieces)
        }
        Prim::Rotl | Prim::Rotr => {
            if *x_hi == End::of(0) {
                return IntervalSet::single(0);
            }
            let hi = match b(2).1 {
                Fin(w) => Fin(ones(w)),
                e => e.clone(),
            };
            IntervalSet::range(End::of(i64::from(fin(x_lo).signum() > 0)), hi)
        }
        Prim::Shl => {
            let (k_lo, k_hi) = b(1);
            let k_lo = Num::pow2(fin(k_lo));
            let k_hi = match k_hi {
                Fin(k) => Some(Num::pow2(k)),
                _ => None,
            };
            xs[0].lift1(|piece| {
                IntervalSet::from_pieces(vec![piece.clone()])
                    .sign_parts()
                    .into_iter()
                    .map(|(lo, hi)| match lo.signum() {
                        0 => (End::of(0), End::of(0)),
                        1 => (
                            Fin(fin(&lo) * &k_lo),
                            match (&hi, &k_hi) {
                                (Fin(h), Some(k)) => Fin(h * k),
                                _ => PosInf,
                            },
                        ),
                        _ => (
                            match (&lo, &k_hi) {
                                (Fin(l), Some(k)) => Fin(l * k),
                                _ => NegInf,
                            },
                            Fin(fin(&hi) * &k_lo),
                        ),
                    })
                    .collect()
            })
        }
        _ => {
            // `shr`: the floor quotient by `2^k`; a shift by at least the digits of `x` gives
            // 0 or -1, as the shift by those digits does, so `k` is read up to them.
            let (k_lo, k_hi) = b(1);
            let shr = |x: &Num, k: Option<&Num>| -> Num {
                let d = digits(x);
                let k = match k {
                    Some(k) if *k < d => k,
                    _ => &d,
                };
                x.div_floor(&Num::pow2(k))
            };
            let k_lo = fin(k_lo);
            let k_hi = match k_hi {
                Fin(k) => Some(k),
                _ => None,
            };
            xs[0].lift1(|piece| {
                IntervalSet::from_pieces(vec![piece.clone()])
                    .sign_parts()
                    .into_iter()
                    .map(|(lo, hi)| match lo.signum() {
                        0 => (End::of(0), End::of(0)),
                        1 => (
                            Fin(shr(fin(&lo), k_hi)),
                            match &hi {
                                Fin(h) => Fin(shr(h, Some(k_lo))),
                                e => e.clone(),
                            },
                        ),
                        _ => (
                            match &lo {
                                Fin(l) => Fin(shr(l, Some(k_lo))),
                                e => e.clone(),
                            },
                            Fin(shr(fin(&hi), k_hi)),
                        ),
                    })
                    .collect()
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(pieces: &[(i64, i64)]) -> IntervalSet {
        IntervalSet::from_pieces(
            pieces
                .iter()
                .map(|&(a, b)| (End::of(a), End::of(b)))
                .collect(),
        )
    }

    #[test]
    fn normalization_merges_overlapping_and_adjacent_pieces() {
        assert_eq!(set(&[(5, 7), (0, 2), (3, 3)]), set(&[(0, 3), (5, 7)]));
        assert_eq!(set(&[(0, 2), (1, 9)]).pieces(), &[(End::of(0), End::of(9))]);
        assert!(set(&[(3, 2)]).is_empty());
        assert_eq!(
            IntervalSet::range(End::of(i64::MAX), PosInf).pieces().len(),
            1
        );
    }

    #[test]
    fn display_uses_the_type_syntax() {
        assert_eq!(set(&[(0, 4)]).to_string(), "[0..=4]");
        assert_eq!(IntervalSet::range(End::of(0), PosInf).to_string(), "[0..]");
        assert_eq!(IntervalSet::top().to_string(), "[..]");
        assert_eq!(
            IntervalSet::from_pieces(vec![(NegInf, End::of(-1)), (End::of(1), PosInf)]).to_string(),
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
                        .map(|i| (End::of(i), End::of(i)))
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
            IntervalSet::range(End::of(0), PosInf)
        );
        assert_eq!(
            a.widen(&set(&[(-1, 2)]), &none),
            IntervalSet::range(NegInf, End::of(2))
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
