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
pub fn push<I: Interval>(out: &mut Vec<I>, r: I) {
    if r.is_empty() {
        return;
    }
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

/// The integers of `lo..=hi` outside the intervals of `list`, non-empty and sorted by lower end
/// (they may overlap or nest), as a normal list. O(|list|).
///
/// The end so far is the greatest upper end read, not the last one: an interval nested in an
/// earlier one, as `(2, 3)` after `(0, 5)`, must not bring it back (DRY-sorted-structures D2,
/// where two of the three copies kept the last).
pub fn complement<T: Discrete>(list: &[(T, T)], lo: T, hi: T) -> Vec<(T, T)> {
    let mut out = Vec::with_capacity(list.len() + 1);
    // The least integer of `lo..=hi` that no interval read so far holds.
    let mut next = lo;
    for (l, h) in list {
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
}
