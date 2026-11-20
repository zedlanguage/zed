//! Sorted lists of disjoint closed intervals of integers (DRY-sorted-structures-2): built from
//! intervals in any order ([`coalesce`]), grown at the end ([`push`]), and their union
//! ([`union`]), meet ([`intersect`]), difference ([`minus`]) and complement ([`complement`],
//! [`complement_spans`]).
//!
//! A list is *normal* when its intervals are non-empty, sorted, disjoint and not adjacent: no
//! integer lies outside all of them between two of them. Every function here returns a normal
//! list. Three forms of interval implement [`Interval`]: `(T, T)`, both ends held, for a
//! [`Discrete`] `T`; `(Option<T>, Option<T>)`, where an absent end is unbounded on its side; and,
//! in zedc-lattice, its `(End, End)` with the two infinities as ends.

use std::cmp::Ordering;

/// An integer type: each value has a next and a previous value, except at the type's ends.
pub trait Discrete: Ord + Clone {
    /// `self + 1`, `None` when `self` is the greatest value of the type.
    fn succ(&self) -> Option<Self>;

    /// `self - 1`, `None` when `self` is the least value of the type.
    fn pred(&self) -> Option<Self>;

    /// Whether `self <= other + 1`: whether an interval starting at `self` touches or overlaps
    /// one ending at `other`. A type that can answer without forming `other + 1` overrides it.
    fn at_most_succ(&self, other: &Self) -> bool {
        other.succ().is_none_or(|s| *self <= s)
    }
}

macro_rules! discrete_primitive {
    ($($t:ty),*) => {$(
        impl Discrete for $t {
            #[inline]
            fn succ(&self) -> Option<Self> {
                self.checked_add(1)
            }

            #[inline]
            fn pred(&self) -> Option<Self> {
                self.checked_sub(1)
            }
        }
    )*};
}

discrete_primitive!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);

/// A closed interval of integers, as the functions of this module read it.
pub trait Interval: Sized {
    /// Whether the interval holds no integer.
    fn is_empty(&self) -> bool;

    /// The order of the lower ends of `self` and `other`.
    fn cmp_lo(&self, other: &Self) -> Ordering;

    /// Whether the upper end of `self` is at or below that of `other`.
    fn ends_by(&self, other: &Self) -> bool;

    /// The integers in both `self` and `other`, `None` when there are none.
    fn meet(&self, other: &Self) -> Option<Self>;

    /// `next`, non-empty, whose lower end is at or above that of `self`, non-empty, joined to
    /// `self` when the two overlap or touch (`self` becomes their union, and `None` is
    /// returned); otherwise `next` is given back and `self` is unchanged.
    fn absorb(&mut self, next: Self) -> Option<Self>;
}

impl<T: Discrete> Interval for (T, T) {
    #[inline]
    fn is_empty(&self) -> bool {
        self.0 > self.1
    }

    #[inline]
    fn cmp_lo(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }

    #[inline]
    fn ends_by(&self, other: &Self) -> bool {
        self.1 <= other.1
    }

    fn meet(&self, other: &Self) -> Option<Self> {
        let lo = (&self.0).max(&other.0);
        let hi = (&self.1).min(&other.1);
        (lo <= hi).then(|| (lo.clone(), hi.clone()))
    }

    fn absorb(&mut self, next: Self) -> Option<Self> {
        if !next.0.at_most_succ(&self.1) {
            return Some(next);
        }
        if next.1 > self.1 {
            self.1 = next.1;
        }
        None
    }
}

/// `(lo, hi)` with `None` for an end unbounded on its side: `None` is below every lower end and
/// above every upper end.
impl<T: Discrete> Interval for (Option<T>, Option<T>) {
    #[inline]
    fn is_empty(&self) -> bool {
        matches!(self, (Some(l), Some(h)) if l > h)
    }

    #[inline]
    fn cmp_lo(&self, other: &Self) -> Ordering {
        // `Option`'s order puts `None` first, as an unbounded lower end must be.
        self.0.cmp(&other.0)
    }

    #[inline]
    fn ends_by(&self, other: &Self) -> bool {
        match (&self.1, &other.1) {
            (Some(a), Some(b)) => a <= b,
            (_, None) => true,
            (None, Some(_)) => false,
        }
    }

    fn meet(&self, other: &Self) -> Option<Self> {
        let lo = match (&self.0, &other.0) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, b) => a.as_ref().or(b.as_ref()),
        };
        let hi = match (&self.1, &other.1) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.as_ref().or(b.as_ref()),
        };
        let s = (lo.cloned(), hi.cloned());
        (!s.is_empty()).then_some(s)
    }

    fn absorb(&mut self, next: Self) -> Option<Self> {
        let joins = match (&self.1, &next.0) {
            (None, _) | (_, None) => true,
            (Some(h), Some(l)) => l.at_most_succ(h),
        };
        if !joins {
            return Some(next);
        }
        match (&self.1, next.1) {
            (None, _) => {}
            (_, None) => self.1 = None,
            (Some(h), Some(n)) if n > *h => self.1 = Some(n),
            (Some(_), Some(_)) => {}
        }
        None
    }
}

/// Appends `r` to the normal list `out`, keeping it normal: an empty `r` is dropped, and one
/// that overlaps or touches the last interval is joined to it. `r`'s lower end must be at or
/// above the lower end of every interval of `out`. O(1).
///
/// # Panics
///
/// In a build with debug assertions, when `r` is non-empty and its lower end is below that of
/// the last interval of `out`: `absorb` would join it to that interval, or append it out of
/// order, and give a list that is not normal with no error (TEST-dry-shared-units). Since
/// `out` is normal, its last interval has the greatest lower end, so one comparison checks
/// the whole precondition.
pub fn push<I: Interval>(out: &mut Vec<I>, r: I) {
    if r.is_empty() {
        return;
    }
    debug_assert!(
        out.last().is_none_or(|last| last.cmp_lo(&r).is_le()),
        "intervals::push: an interval whose lower end is below that of the last interval"
    );
    let r = match out.last_mut() {
        Some(last) => match last.absorb(r) {
            None => return,
            Some(r) => r,
        },
        None => r,
    };
    out.push(r);
}

/// The union of `v`'s intervals, in any order, overlapping or not, as a normal list. O(n log n)
/// for the sort by lower end, then one pass: each interval either joins the last one kept, which
/// holds the greatest upper end so far, or starts after it with a gap.
pub fn coalesce<I: Interval>(mut v: Vec<I>) -> Vec<I> {
    v.retain(|r| !r.is_empty());
    // Intervals of one lower end overlap, so the order among them does not change the union.
    v.sort_unstable_by(I::cmp_lo);
    let mut out = Vec::with_capacity(v.len());
    for r in v {
        push(&mut out, r);
    }
    out
}

/// The union of `a` and `b`, each sorted by lower end (normal lists are), as a normal list.
/// One merge by lower end, O(|a| + |b|); the naive way, the two joined and coalesced, sorts
/// them again in O(n log n).
pub fn union<I: Interval + Clone>(a: &[I], b: &[I]) -> Vec<I> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        let take_a = match (a.get(i), b.get(j)) {
            (Some(x), Some(y)) => x.cmp_lo(y).is_le(),
            (x, _) => x.is_some(),
        };
        if take_a {
            push(&mut out, a[i].clone());
            i += 1;
        } else {
            push(&mut out, b[j].clone());
            j += 1;
        }
    }
    out
}

/// The integers in both `a` and `b`, normal lists, as a normal list. O(|a| + |b|): the interval
/// that ends first meets nothing after the other's current one, so it is passed over. A meet of
/// `a[i]` with `b[j]` and one with `b[j + 1]` lie on two sides of the gap between those two, and
/// likewise for `a`, so the result is not adjacent anywhere.
pub fn intersect<I: Interval>(a: &[I], b: &[I]) -> Vec<I> {
    let mut out = Vec::new();
    let (mut i, mut j) = (0, 0);
    while let (Some(x), Some(y)) = (a.get(i), b.get(j)) {
        if let Some(m) = x.meet(y) {
            out.push(m);
        }
        if x.ends_by(y) {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

/// The integers of `a` outside `b`, normal lists, as a normal list. O(|a| + |b|): the
/// intervals of `b` that end before an interval of `a` starts are passed over once, and those
/// that meet it are read in turn.
pub fn minus<T: Discrete>(a: &[(T, T)], b: &[(T, T)]) -> Vec<(T, T)> {
    let mut out = Vec::new();
    let mut j = 0;
    for (lo, hi) in a {
        while b.get(j).is_some_and(|(_, e)| e < lo) {
            j += 1;
        }
        // `lo` is the least integer of `a`'s interval not yet decided.
        let mut lo = lo.clone();
        let mut k = j;
        loop {
            let Some((s, e)) = b.get(k).filter(|(s, _)| s <= hi) else {
                out.push((lo, hi.clone()));
                break;
            };
            if *s > lo {
                let before = s.pred().expect("s > lo, so s is not the least value");
                out.push((lo.clone(), before));
            }
            // The rest of `a`'s interval starts after `e`; nothing is left when `e >= hi`.
            match e.succ() {
                Some(next) if next <= *hi => lo = lo.max(next),
                _ => break,
            }
            k += 1;
        }
    }
    out
}

/// The integers of `lo..=hi` outside the intervals of `list`, sorted by lower end (they may
/// overlap or nest; an empty one is skipped), as a normal list; empty where `lo > hi`.
/// O(|list|).
///
/// The end so far is the greatest upper end read, not the last one: an interval nested in an
/// earlier one, as `(2, 3)` after `(0, 5)`, must not bring it back (DRY-sorted-structures D2,
/// where two of the three copies kept the last).
///
/// An empty interval is skipped, as [`complement_spans`] skips one. Until TEST-dry-shared-units
/// the list had to hold none, unchecked: `(5, 2)` in `0..=9` gave `[(0, 4), (3, 9)]`, two
/// intervals that overlap, since its lower end opened a gap and its upper end closed one.
///
/// # Panics
///
/// In a build with debug assertions, when the lower ends of `list` decrease: the gap before
/// an interval is read from the end so far, which an earlier lower end would put wrong.
pub fn complement<T: Discrete>(list: &[(T, T)], lo: T, hi: T) -> Vec<(T, T)> {
    let mut out = Vec::with_capacity(list.len() + 1);
    // The least integer of `lo..=hi` that no interval read so far holds.
    let mut next = lo;
    for (k, (l, h)) in list.iter().enumerate() {
        debug_assert!(
            k == 0 || list[k - 1].0 <= *l,
            "intervals::complement: intervals not sorted by lower end"
        );
        if l > h {
            continue;
        }
        if next > hi || *l > hi {
            break;
        }
        if *l > next {
            let before = l.pred().expect("l > next, so l is not the least value");
            out.push((next.clone(), before));
        }
        if *h >= next {
            match h.succ() {
                Some(s) => next = s,
                None => return out,
            }
        }
    }
    if next <= hi {
        out.push((next, hi));
    }
    out
}

/// The integers outside the intervals of `list`, sorted by lower end (they may overlap or nest),
/// as a normal list; `None` for an unbounded end, in both. O(|list|).
pub fn complement_spans<T: Discrete>(
    list: &[(Option<T>, Option<T>)],
) -> Vec<(Option<T>, Option<T>)> {
    let mut out = Vec::with_capacity(list.len() + 1);
    // The least integer no interval read so far holds; `None` is below every integer, before
    // any interval is read.
    let mut next: Option<T> = None;
    for span in list {
        if span.is_empty() {
            continue;
        }
        let (l, h) = span;
        // Before any interval is read (`next` is `None`), the gap below `l` is empty when `l` is
        // the least value of the type; after, `l > next` gives `l` a previous value.
        if let Some(l) = l
            && next.as_ref().is_none_or(|n| l > n)
            && let Some(before) = l.pred()
        {
            out.push((next.clone(), Some(before)));
        }
        let Some(h) = h else {
            return out;
        };
        if next.as_ref().is_none_or(|n| h >= n) {
            match h.succ() {
                Some(s) => next = Some(s),
                None => return out,
            }
        }
    }
    out.push((next, None));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The members of the subset `bits` of `0..8`.
    fn set(bits: u32) -> Vec<u8> {
        (0..8).filter(|i| bits >> i & 1 == 1).collect()
    }

    /// The normal list of the members of `bits`.
    fn runs(bits: u32) -> Vec<(u8, u8)> {
        coalesce(set(bits).into_iter().map(|v| (v, v)).collect())
    }

    /// The members of a list of intervals of `0..8`.
    fn bits_of(list: &[(u8, u8)]) -> u32 {
        list.iter()
            .flat_map(|&(l, h)| l..=h)
            .fold(0, |m, v| m | 1 << v)
    }

    fn is_normal(list: &[(u8, u8)]) -> bool {
        list.iter().all(|(l, h)| l <= h) && list.windows(2).all(|w| w[0].1 + 1 < w[1].0)
    }

    /// Every pair of subsets of `0..8`: each operation against the same one on bit sets, and
    /// each result normal.
    #[test]
    fn operations_match_bit_sets() {
        for x in 0..256u32 {
            let a = runs(x);
            assert!(is_normal(&a));
            assert_eq!(bits_of(&a), x);
            assert_eq!(complement(&a, 0, 7), runs(!x & 0xff));
            assert_eq!(complement(&a, 2, 5), runs(!x & 0b0011_1100));
            for y in 0..256u32 {
                let b = runs(y);
                assert_eq!(union(&a, &b), runs(x | y));
                assert_eq!(intersect(&a, &b), runs(x & y));
                assert_eq!(minus(&a, &b), runs(x & !y));
            }
        }
    }

    /// Intervals that overlap, nest and touch, in any order.
    #[test]
    fn coalesce_and_complement_take_overlapping_intervals() {
        let v = vec![(5u8, 6), (0, 5), (2, 3), (9, 9), (7, 7), (4, 2)];
        assert_eq!(coalesce(v), [(0, 7), (9, 9)]);
        // Nested after an outer one: the gap starts after the outer one (D2).
        assert_eq!(complement(&[(0u8, 5), (2, 3)], 0, 9), [(6, 9)]);
        assert_eq!(complement::<u8>(&[], 0, 2), [(0, 2)]);
        assert_eq!(complement(&[(0u8, 255)], 0, 255), []);
        assert_eq!(complement(&[(250u8, 255)], 0, 255), [(0, 249)]);
        assert_eq!(complement(&[(0u8, 3)], 5, 9), [(5, 9)]);
        assert_eq!(complement(&[(7u8, 12)], 5, 9), [(5, 6)]);
    }

    /// The ends of the type: no overflow at `u8::MAX` or `u8::MIN`.
    #[test]
    fn ends_of_the_type() {
        assert_eq!(coalesce(vec![(255u8, 255), (0, 254)]), [(0, 255)]);
        assert_eq!(minus(&[(0u8, 255)], &[(255, 255)]), [(0, 254)]);
        assert_eq!(minus(&[(0u8, 255)], &[(0, 0)]), [(1, 255)]);
        assert_eq!(minus(&[(0u8, 255)], &[(0, 255)]), []);
    }

    /// The members of an unbounded list within `-4..=4`, for comparison with bit sets; the
    /// ends outside stand for the unbounded ones.
    fn clip(list: &[(Option<i8>, Option<i8>)]) -> u32 {
        list.iter()
            .flat_map(|(l, h)| l.unwrap_or(-4).max(-4)..=h.unwrap_or(4).min(4))
            .fold(0, |m, v| m | 1 << (v + 4))
    }

    /// Unbounded spans: every list of up to two spans with ends in `-3..=3` or unbounded, against
    /// the same operations on the members within `-4..=4`.
    #[test]
    fn unbounded_spans_match_bit_sets() {
        let ends: Vec<Option<i8>> = std::iter::once(None).chain((-3..=3).map(Some)).collect();
        let mut spans = Vec::new();
        for l in &ends {
            for h in &ends {
                spans.push((*l, *h));
            }
        }
        let all = 0x1ff;
        for p in &spans {
            for q in &spans {
                let a = coalesce(vec![*p, *q]);
                assert_eq!(clip(&a), clip(&[*p, *q]));
                assert!(
                    a.windows(2)
                        .all(|w| w[0].1.zip(w[1].0).is_some_and(|(h, l)| h + 1 < l))
                );
                // Within `-4..=4` the complement holds the members the list does not, plus `-4`
                // or `4` when the list leaves an unbounded end free.
                assert_eq!(
                    clip(&complement_spans(&a)) & 0b0_1111_1110,
                    !clip(&a) & 0b0_1111_1110
                );
                for r in &spans {
                    let b = coalesce(vec![*r]);
                    assert_eq!(clip(&intersect(&a, &b)), clip(&a) & clip(&b));
                    assert_eq!(clip(&union(&a, &b)), (clip(&a) | clip(&b)) & all);
                }
            }
        }
        assert_eq!(complement_spans::<i8>(&[]), [(None, None)]);
        assert_eq!(complement_spans(&[(None, Some(2i8)), (Some(1), None)]), []);
        assert_eq!(
            complement_spans(&[(Some(0i8), Some(5)), (Some(2), Some(3))]),
            [(None, Some(-1)), (Some(6), None)]
        );
        // A first span from the least value of the type leaves no gap below it, and one to the
        // greatest leaves none above.
        assert_eq!(
            complement_spans(&[(Some(i8::MIN), Some(0))]),
            [(Some(1), None)]
        );
        assert_eq!(
            complement_spans(&[(Some(0), Some(i8::MAX))]),
            [(None, Some(-1))]
        );
    }

    // Random lists over windows of integers at the ends of each type, against their members
    // (TEST-dry-shared-units). The tests above reach `0..8` and `-4..=4`; these reach the least
    // and greatest value of `u8`, `i8`, `i128`, `u64` and `usize`, where the copies the module
    // replaced overflowed.

    use crate::seed::Rng;
    use std::fmt::Debug;

    /// The members of `list`, intervals of a window of `w` integers of `T`, one `bool` each at
    /// its place `off(v)`; an empty interval holds none.
    fn members<T: Discrete + Copy>(
        list: &[(T, T)],
        w: usize,
        off: &impl Fn(T) -> usize,
    ) -> Vec<bool> {
        let mut m = vec![false; w];
        for &(l, h) in list {
            if l <= h {
                m[off(l)..=off(h)].fill(true);
            }
        }
        m
    }

    /// The normal list of the members `m` of a window: its maximal runs.
    fn runs_of<T: Copy>(m: &[bool], at: &impl Fn(usize) -> T) -> Vec<(T, T)> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < m.len() {
            if m[i] {
                let start = i;
                while i + 1 < m.len() && m[i + 1] {
                    i += 1;
                }
                out.push((at(start), at(i)));
            }
            i += 1;
        }
        out
    }

    /// Whether `list` is normal, read through `Discrete` alone, so at every width.
    fn normal<T: Discrete>(list: &[(T, T)]) -> bool {
        list.iter().all(|(l, h)| l <= h) && list.windows(2).all(|w| !w[1].0.at_most_succ(&w[0].1))
    }

    /// Up to 6 intervals of a window of `w`: mostly short, one in eight to the window's end,
    /// one in eight from its start, one in eight empty.
    fn draw<T: Copy>(rng: &mut Rng, w: usize, at: &impl Fn(usize) -> T) -> Vec<(T, T)> {
        (0..rng.below(7))
            .map(|_| {
                let l = if rng.below(8) == 0 { 0 } else { rng.below(w) };
                let h = match rng.below(8) {
                    0 if l > 0 => l - 1 - rng.below(l.min(3)),
                    1 => w - 1,
                    _ => (l + rng.below(6)).min(w - 1),
                };
                (at(l), at(h))
            })
            .collect()
    }

    /// `coalesce` keeping the last upper end, not the greatest: the D2 fault, the negative
    /// control of the coalesce check.
    fn coalesce_keeping_the_last_end<T: Discrete + Copy>(mut v: Vec<(T, T)>) -> Vec<(T, T)> {
        v.retain(|(l, h)| l <= h);
        v.sort_by_key(|r| r.0);
        let mut out: Vec<(T, T)> = Vec::new();
        for r in v {
            match out.last_mut() {
                Some(last) if r.0.at_most_succ(&last.1) => last.1 = r.1,
                _ => out.push(r),
            }
        }
        out
    }

    /// `intersect` passing over the interval that ends last, not first: the negative control of
    /// the intersect check.
    fn intersect_passing_the_wrong_one<T: Discrete + Copy>(
        a: &[(T, T)],
        b: &[(T, T)],
    ) -> Vec<(T, T)> {
        let mut out = Vec::new();
        let (mut i, mut j) = (0, 0);
        while let (Some(x), Some(y)) = (a.get(i), b.get(j)) {
            if let Some(m) = x.meet(y) {
                out.push(m);
            }
            if x.ends_by(y) {
                j += 1;
            } else {
                i += 1;
            }
        }
        out
    }

    /// `minus` taking away from each interval of `a` only the first interval of `b` that meets
    /// it: the negative control of the minus check.
    fn minus_first_only<T: Discrete + Copy>(a: &[(T, T)], b: &[(T, T)]) -> Vec<(T, T)> {
        a.iter()
            .flat_map(|x| {
                let first: Vec<(T, T)> = b.iter().filter_map(|y| x.meet(y)).take(1).collect();
                minus(&[*x], &first)
            })
            .collect()
    }

    /// The `complement` of the copies D2 fixed (modular.rs `res_complement`, preimage.rs
    /// `ranges_complement`): the end so far is the last upper end read, not the greatest. The
    /// regression control of D2 and the negative control of the complement check.
    fn complement_keeping_the_last_end<T: Discrete + Copy>(
        list: &[(T, T)],
        lo: T,
        hi: T,
    ) -> Vec<(T, T)> {
        let mut out = Vec::new();
        let mut next = lo;
        for &(l, h) in list {
            if next > hi || l > hi {
                break;
            }
            if l > next {
                out.push((next, l.pred().expect("l > next")));
            }
            match h.succ() {
                Some(s) => next = s,
                None => return out,
            }
        }
        if next <= hi {
            out.push((next, hi));
        }
        out
    }

    /// Random lists in a window of `w` integers of `T` (`at` the integer at a place, `off` the
    /// place of an integer) against the same operations on their members, each result normal;
    /// and a faulty form of each operation, its negative control, caught by the same check on
    /// some draw.
    fn window_matches_members<T: Discrete + Copy + Debug>(
        rng: &mut Rng,
        w: usize,
        at: impl Fn(usize) -> T,
        off: impl Fn(T) -> usize,
    ) {
        let mut caught = [false; 5];
        for round in 0..400 {
            let (ra, rb) = (draw(rng, w, &at), draw(rng, w, &at));
            let (ma, mb) = (members(&ra, w, &off), members(&rb, w, &off));
            let a = coalesce(ra.clone());
            assert_eq!(a, runs_of(&ma, &at), "round {round}: coalesce {ra:?}");
            assert!(normal(&a), "round {round}: {a:?}");
            caught[0] |= coalesce_keeping_the_last_end(ra.clone()) != a;
            let b = coalesce(rb.clone());
            // Pushed in the order of their lower ends, the intervals give what coalesce gives.
            let mut sorted = ra.clone();
            sorted.sort_by_key(|r| r.0);
            let mut pushed = Vec::new();
            for &r in &sorted {
                push(&mut pushed, r);
            }
            assert_eq!(pushed, a, "round {round}: push {sorted:?}");
            let by = |f: fn(bool, bool) -> bool| -> Vec<(T, T)> {
                let m: Vec<bool> = ma.iter().zip(&mb).map(|(&x, &y)| f(x, y)).collect();
                runs_of(&m, &at)
            };
            let u = union(&a, &b);
            assert_eq!(u, by(|x, y| x || y), "round {round}: union {a:?} {b:?}");
            caught[1] |= a.iter().chain(&b).copied().collect::<Vec<_>>() != u;
            let m = intersect(&a, &b);
            assert_eq!(m, by(|x, y| x && y), "round {round}: intersect {a:?} {b:?}");
            caught[2] |= intersect_passing_the_wrong_one(&a, &b) != m;
            let d = minus(&a, &b);
            assert_eq!(d, by(|x, y| x && !y), "round {round}: minus {a:?} {b:?}");
            caught[3] |= minus_first_only(&a, &b) != d;
            // The complement of the raw list sorted (overlapping, nested and empty intervals
            // in it) over a random range, `lo > hi` included, or over the whole window.
            let (lo, hi) = match rng.below(4) {
                0 => (0, w - 1),
                _ => (rng.below(w), rng.below(w)),
            };
            let want: Vec<bool> = (0..w).map(|i| lo <= i && i <= hi && !ma[i]).collect();
            let c = complement(&sorted, at(lo), at(hi));
            assert_eq!(
                c,
                runs_of(&want, &at),
                "round {round}: complement {sorted:?} {lo} {hi}"
            );
            let non_empty: Vec<(T, T)> = sorted.iter().copied().filter(|(l, h)| l <= h).collect();
            caught[4] |= complement_keeping_the_last_end(&non_empty, at(lo), at(hi)) != c;
        }
        let names = ["coalesce", "union", "intersect", "minus", "complement"];
        for (name, caught) in names.iter().zip(caught) {
            assert!(caught, "the negative control of {name} was never caught");
        }
    }

    /// Windows of 64 at each end of `i128`, `u64` and `usize` and around 0, and the whole of
    /// `u8` and `i8`.
    #[test]
    fn random_lists_match_their_members_at_the_ends_of_each_type() {
        let (mut rng, _) = Rng::fresh("random_lists_match_their_members_at_the_ends_of_each_type");
        window_matches_members(&mut rng, 256, |i| i as u8, usize::from);
        window_matches_members(
            &mut rng,
            256,
            |i| (i as i16 - 128) as i8,
            |v| (i16::from(v) + 128) as usize,
        );
        for base in [i128::MIN, -32, i128::MAX - 63] {
            window_matches_members(&mut rng, 64, |i| base + i as i128, |v| (v - base) as usize);
        }
        for base in [0, u64::MAX - 63] {
            window_matches_members(&mut rng, 64, |i| base + i as u64, |v| (v - base) as usize);
        }
        let base = usize::MAX - 63;
        window_matches_members(&mut rng, 64, |i| base + i, |v| v - base);
    }

    /// Regressions of the copies DRY-sorted-structures-2 job 1 replaced (6da69df6f), each old
    /// form written out beside the shared one, with `wrapping_add` and `wrapping_sub` for the
    /// `+ 1` and `- 1` the old forms wrote: in a build with overflow checks they panicked there,
    /// and in one without they wrapped to the wrong answer shown.
    #[test]
    fn the_copies_replaced_overflowed_at_the_ends_of_the_type() {
        // presburger.rs `cells_join`: an interval joined the last when `l <= last.1 + 1`.
        let old_join = |v: &[(usize, usize)]| {
            let mut out: Vec<(usize, usize)> = Vec::new();
            for &(l, h) in v {
                match out.last_mut() {
                    Some(last) if l <= last.1.wrapping_add(1) => last.1 = last.1.max(h),
                    _ => out.push((l, h)),
                }
            }
            out
        };
        let v = [(0, usize::MAX), (3, 4)];
        assert_eq!(old_join(&v), [(0, usize::MAX), (3, 4)], "not normal");
        assert_eq!(coalesce(v.to_vec()), [(0, usize::MAX)]);
        // presburger.rs `cells_minus`: the rest after `b[k]` started at `b[k].1 + 1`.
        let rest_after = |e: usize| e.wrapping_add(1);
        assert_eq!(rest_after(usize::MAX), 0, "the rest would start again at 0");
        assert_eq!(minus(&[(0, usize::MAX)], &[(5, usize::MAX)]), [(0, 4)]);
        assert_eq!(
            minus(&[(7, usize::MAX)], &[(0, 3), (9, usize::MAX)]),
            [(7, 8)]
        );
        // two_pins.rs `merge_runs`: runs joined when `e >= l - 1`, which at `l == i128::MIN`
        // compared `e` with `i128::MAX`.
        let old_joins = |e: i128, l: i128| e >= l.wrapping_sub(1);
        assert!(!old_joins(5, i128::MIN), "two overlapping runs kept apart");
        assert_eq!(
            coalesce(vec![(i128::MIN, 5), (i128::MIN, i128::MIN)]),
            [(i128::MIN, 5)]
        );
        // residues.rs `complement` did not clip an interval past `m - 1`: within `0..=9`, the
        // interval `(7, 12)` leaves `0..=6`.
        assert_eq!(complement(&[(7u64, 12)], 0, 9), [(0, 6)]);
        assert_eq!(
            complement(&[(0u64, 3), (5, u64::MAX)], 0, u64::MAX),
            [(4, 4)]
        );
    }

    /// `complement_spans` keeping the last upper end read, not the greatest: the negative
    /// control of the spans check.
    fn complement_spans_keeping_the_last_end(
        list: &[(Option<i8>, Option<i8>)],
    ) -> Vec<(Option<i8>, Option<i8>)> {
        let mut out = Vec::new();
        let mut next: Option<i8> = None;
        for &(l, h) in list.iter().filter(|s| !s.is_empty()) {
            if let Some(l) = l
                && next.is_none_or(|n| l > n)
                && let Some(before) = l.pred()
            {
                out.push((next, Some(before)));
            }
            match h.map(|h| h.succ()) {
                None | Some(None) => return out,
                Some(s) => next = s,
            }
        }
        out.push((next, None));
        out
    }

    /// Random lists of spans of `i8`, an end unbounded one time in four, against their members
    /// as 256 `bool`s: an unbounded end reaches the end of the type, so the members are exact.
    /// The results are compared by their members, since a bounded end at the type's end and an
    /// unbounded one hold the same integers.
    #[test]
    fn random_spans_of_i8_match_their_members() {
        type Span = (Option<i8>, Option<i8>);
        let (mut rng, _) = Rng::fresh("random_spans_of_i8_match_their_members");
        let off = |v: i8| (i16::from(v) + 128) as usize;
        let of = |list: &[Span]| {
            let mut m = [false; 256];
            for (l, h) in list {
                let (l, h) = (l.map_or(0, off), h.map_or(255, off));
                if l <= h {
                    m[l..=h].fill(true);
                }
            }
            m
        };
        let spans_normal = |list: &[Span]| {
            list.iter().all(|s| !s.is_empty())
                && list.iter().skip(1).all(|s| s.0.is_some())
                && list.iter().rev().skip(1).all(|s| s.1.is_some())
                && list.windows(2).all(|w| match (w[0].1, w[1].0) {
                    (Some(h), Some(l)) => !l.at_most_succ(&h),
                    _ => false,
                })
        };
        fn end(rng: &mut Rng) -> Option<i8> {
            (rng.below(4) != 0).then(|| rng.int(-128, 127) as i8)
        }
        fn draw(rng: &mut Rng) -> Vec<Span> {
            (0..rng.below(6)).map(|_| (end(rng), end(rng))).collect()
        }
        let mut caught = false;
        for round in 0..2000 {
            let (ra, rb) = (draw(&mut rng), draw(&mut rng));
            let (a, b) = (coalesce(ra.clone()), coalesce(rb.clone()));
            assert_eq!(of(&a), of(&ra), "round {round}: coalesce {ra:?}");
            assert!(spans_normal(&a), "round {round}: {a:?}");
            let (ma, mb) = (of(&a), of(&b));
            let u = union(&a, &b);
            assert!(spans_normal(&u), "round {round}: {u:?}");
            let m = intersect(&a, &b);
            assert!(spans_normal(&m), "round {round}: {m:?}");
            let mut sorted = ra.clone();
            sorted.sort_by_key(|s| s.0);
            let c = complement_spans(&sorted);
            assert!(
                spans_normal(&c),
                "round {round}: complement {sorted:?} = {c:?}"
            );
            let (mu, mm, mc) = (of(&u), of(&m), of(&c));
            for i in 0..256 {
                assert_eq!(mu[i], ma[i] || mb[i], "round {round}: union at {i}");
                assert_eq!(mm[i], ma[i] && mb[i], "round {round}: meet at {i}");
                assert_eq!(mc[i], !ma[i], "round {round}: complement at {i}");
            }
            caught |= of(&complement_spans_keeping_the_last_end(&sorted)) != of(&c);
        }
        assert!(
            caught,
            "the negative control of complement_spans was never caught"
        );
    }

    /// D2: the complement after a nested interval, against the old copies' form.
    #[test]
    fn the_complement_after_a_nested_interval_starts_after_the_outer_one() {
        let list = [(0u8, 5), (2, 3)];
        assert_eq!(complement_keeping_the_last_end(&list, 0, 9), [(4, 9)]);
        assert_eq!(complement(&list, 0, 9), [(6, 9)]);
        assert_eq!(coalesce_keeping_the_last_end(list.to_vec()), [(0, 3)]);
        assert_eq!(coalesce(list.to_vec()), [(0, 5)]);
    }

    /// An empty interval in the list of `complement` is skipped; before TEST-dry-shared-units it
    /// opened a gap at its lower end and closed one at its upper end.
    #[test]
    fn complement_skips_an_empty_interval() {
        assert_eq!(complement(&[(5u8, 2)], 0, 9), [(0, 9)]);
        assert_eq!(
            complement(&[(1u8, 1), (5, 2), (7, 8)], 0, 9),
            [(0, 0), (2, 6), (9, 9)]
        );
        assert_eq!(complement(&[(1u8, 1)], 5, 2), [], "lo > hi is empty");
        assert_eq!(complement::<u8>(&[], 9, 9), [(9, 9)]);
    }

    /// The text of the panic of `f`, which must panic.
    fn panic_text(f: impl FnOnce() + std::panic::UnwindSafe) -> String {
        let p = std::panic::catch_unwind(f).expect_err("it panics");
        p.downcast_ref::<&str>()
            .map(|s| s.to_string())
            .or_else(|| p.downcast_ref::<String>().cloned())
            .expect("a text message")
    }

    /// Each precondition broken, in a build with debug assertions (the test builds are).
    #[test]
    fn a_broken_precondition_panics_in_a_debug_build() {
        if !cfg!(debug_assertions) {
            return;
        }
        let text = panic_text(|| {
            let mut out = vec![(5u8, 6)];
            push(&mut out, (0, 1));
        });
        assert_eq!(
            text,
            "intervals::push: an interval whose lower end is below that of the last interval"
        );
        let text = panic_text(|| {
            let mut out = vec![(Some(0i8), Some(1))];
            push(&mut out, (None, Some(5)));
        });
        assert!(text.starts_with("intervals::push"), "{text}");
        // An empty interval is dropped before the check: it adds no integer.
        let mut out = vec![(5u8, 6)];
        push(&mut out, (3, 0));
        assert_eq!(out, [(5, 6)]);
        let text = panic_text(|| {
            complement(&[(5u8, 6), (0, 1)], 0, 9);
        });
        assert_eq!(
            text,
            "intervals::complement: intervals not sorted by lower end"
        );
    }
}
