//! Sorted lists: sorting with duplicates removed ([`sort_dedup`], [`sort_dedup_by_key`],
//! [`sort_dedup_by`]), the walk
//! of two sorted lists side by side ([`merge_join`]), and their union in one merge ([`merge_into`],
//! [`merge`], [`union_all`]), and the lookup of a key in a sorted list of pairs ([`sorted_get`]).

use std::borrow::Borrow;
use std::cmp::Ordering;

/// `v` sorted, each run of equal items kept once. O(n log n) comparisons, no allocation.
///
/// `sort_unstable` (pattern-defeating quicksort, O(n log n), in place) is enough: items that the
/// order calls equal are equal (`Ord` agrees with `Eq`), so it does not matter which of them
/// `dedup` keeps. Where only a key decides, so that equal keys can hold unequal items, use
/// [`sort_dedup_by_key`], which says which item it keeps.
pub fn sort_dedup<T: Ord>(v: &mut Vec<T>) {
    v.sort_unstable();
    v.dedup();
}

/// `v` sorted by `key`, keeping of each key only its first item in `v`'s order. O(n log n)
/// comparisons and calls of `key`.
///
/// The stable sort keeps items of one key in their order in `v`, so the item kept is the first
/// one, whatever the sort does with the others; an unstable sort would keep an arbitrary one.
pub fn sort_dedup_by_key<T, K: Ord>(v: &mut Vec<T>, mut key: impl FnMut(&T) -> K) {
    v.sort_by_key(&mut key);
    v.dedup_by(|x, y| key(x) == key(y));
}

/// `v` sorted stably by `cmp`, an order coarser than equality, with every item equal to an
/// earlier item of `v` removed. Of the items `cmp` calls equal, the ones kept stay in their order
/// in `v`. O(n log n) comparisons; one list of n (position, item) pairs.
///
/// Complexity tradeoff: `v.sort_by(cmp); v.dedup()` is one sort, but `dedup` removes only
/// adjacent copies, so where `cmp` calls unequal items equal a copy apart from its first by
/// another item of its key stays: `(1, 'a'), (1, 'b'), (1, 'a')` by the first field
/// (DEDUP-keyed-sort-interleaved). Removing each copy within its run of `cmp` by a scan of the
/// items kept is O(r²) for a run of r. Here two sorts, both O(n log n): by the full order with
/// the position as tie-break, so the copies of an item are adjacent and the first stands first
/// and is kept; then by `cmp` with the position as tie-break, which is the stable order.
pub fn sort_dedup_by<T: Ord>(v: &mut Vec<T>, mut cmp: impl FnMut(&T, &T) -> Ordering) {
    let mut tagged: Vec<(usize, T)> = std::mem::take(v).into_iter().enumerate().collect();
    tagged.sort_unstable_by(|(i, x), (j, y)| x.cmp(y).then(i.cmp(j)));
    tagged.dedup_by(|(_, later), (_, first)| later == first);
    tagged.sort_unstable_by(|(i, x), (j, y)| cmp(x, y).then(i.cmp(j)));
    v.extend(tagged.into_iter().map(|(_, x)| x));
}

/// The value paired with `key` in `pairs`, a list of pairs sorted strictly increasing by their
/// first item, or `None` where no pair has that key. O(log n) comparisons. `key` may be any form
/// the keys borrow as, so a list keyed by `Rc<str>` is searched with a `&str`.
pub fn sorted_get<'a, K: Borrow<Q>, Q: Ord + ?Sized, V>(
    pairs: &'a [(K, V)],
    key: &Q,
) -> Option<&'a V> {
    let i = pairs.binary_search_by(|(k, _)| k.borrow().cmp(key)).ok()?;
    Some(&pairs[i].1)
}

/// One step of [`merge_join`]: an item of the first list only, of the second only, or one of each
/// that compare equal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Joined<A, B> {
    /// An item of the first list that the second does not hold.
    Left(A),
    /// An item of the second list that the first does not hold.
    Right(B),
    /// An item of each list, equal under the order.
    Both(A, B),
}

/// The iterator of [`merge_join`].
pub struct MergeJoin<'a, A, B, F> {
    a: &'a [A],
    b: &'a [B],
    cmp: F,
}

impl<'a, A, B, F: FnMut(&A, &B) -> Ordering> Iterator for MergeJoin<'a, A, B, F> {
    type Item = Joined<&'a A, &'a B>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match (self.a.split_first(), self.b.split_first()) {
            (Some((x, ra)), Some((y, rb))) => Some(match (self.cmp)(x, y) {
                Ordering::Less => {
                    self.a = ra;
                    Joined::Left(x)
                }
                Ordering::Greater => {
                    self.b = rb;
                    Joined::Right(y)
                }
                Ordering::Equal => {
                    (self.a, self.b) = (ra, rb);
                    Joined::Both(x, y)
                }
            }),
            (Some((x, ra)), None) => {
                self.a = ra;
                Some(Joined::Left(x))
            }
            (None, Some((y, rb))) => {
                self.b = rb;
                Some(Joined::Right(y))
            }
            (None, None) => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (a, b) = (self.a.len(), self.b.len());
        (a.max(b), Some(a + b))
    }
}

/// The items of `a` and `b`, both sorted increasing under `cmp`, side by side in that order: an
/// item met in one list only comes alone, and an item of each that `cmp` calls equal come
/// together. Each list is read once, O(|a| + |b|) comparisons, no allocation. Where a list holds
/// one item twice, each copy is met in turn: the first is paired with the other list's equal
/// item, the second comes alone.
pub fn merge_join<'a, A, B, F: FnMut(&A, &B) -> Ordering>(
    a: &'a [A],
    b: &'a [B],
    cmp: F,
) -> MergeJoin<'a, A, B, F> {
    MergeJoin { a, b, cmp }
}

/// The union of `a` and `b`, both strictly increasing, written to `out` (cleared first), strictly
/// increasing, keeping only the items `keep` keeps; `out` may be kept from one call to the next,
/// so the merge allocates only when it outgrows it.
///
/// One merge, O(|a| + |b|) comparisons; the naive way, the two joined, sorted and deduplicated, is
/// O((|a| + |b|) log(|a| + |b|)): `sort_unstable` does not see the two runs.
pub fn merge_into<T: Ord + Clone>(
    a: &[T],
    b: &[T],
    mut keep: impl FnMut(&T) -> bool,
    out: &mut Vec<T>,
) {
    out.clear();
    out.reserve(a.len().max(b.len()));
    for j in merge_join(a, b, T::cmp) {
        let (Joined::Left(x) | Joined::Right(x) | Joined::Both(x, _)) = j;
        if keep(x) {
            out.push(x.clone());
        }
    }
}

/// The union of `a` and `b`, both strictly increasing, strictly increasing: [`merge_into`] keeping
/// every item.
pub fn merge<T: Ord + Clone>(a: &[T], b: &[T]) -> Vec<T> {
    let mut out = Vec::new();
    merge_into(a, b, |_| true, &mut out);
    out
}

/// The union of `lists`, each strictly increasing, strictly increasing. The lists are merged in
/// pairs, round after round, as merge sort merges its runs, so each of the `N` items is read in
/// O(log k) rounds of `k` lists: O(N log k) comparisons and clones, against O(N log N) for the
/// lists joined and sorted (an unstable sort does not see the runs; the stable sort finds only
/// runs longer than about the square root of `N`, so it does not promise O(N log k) for many short
/// lists). Where cloning an item is costly, give it references and clone the result once.
pub fn union_all<T: Ord + Clone>(mut lists: Vec<Vec<T>>) -> Vec<T> {
    while lists.len() > 1 {
        let mut next = Vec::with_capacity(lists.len().div_ceil(2));
        let mut it = lists.into_iter();
        while let Some(a) = it.next() {
            next.push(match it.next() {
                Some(b) => merge(&a, &b),
                None => a,
            });
        }
        lists = next;
    }
    lists.pop().unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The members of the subset `bits` of `0..6`, increasing.
    fn members(bits: u32) -> Vec<u32> {
        (0..6).filter(|i| bits >> i & 1 == 1).collect()
    }

    /// Every pair of subsets of `0..6`: the merge, the join and the union of many against a
    /// sort of the items joined.
    #[test]
    fn merges_match_a_sort() {
        for x in 0..64 {
            for y in 0..64 {
                let (a, b) = (members(x), members(y));
                let mut want: Vec<u32> = a.iter().chain(&b).copied().collect();
                sort_dedup(&mut want);
                assert_eq!(merge(&a, &b), want);
                let mut odd = Vec::new();
                merge_into(&a, &b, |v| v % 2 == 1, &mut odd);
                let want_odd: Vec<u32> = want.iter().copied().filter(|v| v % 2 == 1).collect();
                assert_eq!(odd, want_odd);
                let both: Vec<u32> = merge_join(&a, &b, u32::cmp)
                    .filter_map(|j| match j {
                        Joined::Both(p, q) => {
                            assert_eq!(p, q);
                            Some(*p)
                        }
                        _ => None,
                    })
                    .collect();
                let meet: Vec<u32> = a.iter().copied().filter(|v| b.contains(v)).collect();
                assert_eq!(both, meet);
                let lists = vec![
                    a.clone(),
                    b.clone(),
                    members(x ^ y),
                    Vec::new(),
                    members(x & 7),
                ];
                let mut all: Vec<u32> = lists.iter().flatten().copied().collect();
                sort_dedup(&mut all);
                assert_eq!(union_all(lists), all);
            }
        }
        assert_eq!(union_all::<u32>(Vec::new()), Vec::<u32>::new());
    }

    /// Of the items of one key, the first in the input is kept.
    #[test]
    fn by_key_keeps_the_first() {
        let mut v = vec![(2, 'a'), (1, 'b'), (2, 'c'), (1, 'd'), (0, 'e')];
        sort_dedup_by_key(&mut v, |&(k, _)| k);
        assert_eq!(v, [(0, 'e'), (1, 'b'), (2, 'a')]);
    }

    /// A copy apart from its first by another item of its key is removed, which a sort by the
    /// key and a `dedup` leave; every list of up to 5 pairs of `0..2 × 0..2` against a scan that
    /// keeps the first of each item, in the stable order of the key.
    #[test]
    fn by_order_removes_copies_apart() {
        let by_key = |a: &(u32, u32), b: &(u32, u32)| a.0.cmp(&b.0);
        let mut v = vec![(1, 0), (1, 1), (1, 0), (0, 1)];
        let mut old = v.clone();
        old.sort_by(by_key);
        old.dedup();
        assert_eq!(old, [(0, 1), (1, 0), (1, 1), (1, 0)]);
        sort_dedup_by(&mut v, by_key);
        assert_eq!(v, [(0, 1), (1, 0), (1, 1)]);
        for len in 0..=5u32 {
            for code in 0..4u32.pow(len) {
                let items: Vec<(u32, u32)> = (0..len)
                    .map(|i| code / 4u32.pow(i) % 4)
                    .map(|d| (d / 2, d % 2))
                    .collect();
                let mut want: Vec<(u32, u32)> = Vec::new();
                for x in &items {
                    if !want.contains(x) {
                        want.push(*x);
                    }
                }
                want.sort_by(by_key);
                let mut got = items.clone();
                sort_dedup_by(&mut got, by_key);
                assert_eq!(got, want, "{items:?}");
            }
        }
    }

    /// Every key below, between, at and above the keys of a list, against a scan; and a list
    /// keyed by `String` searched with a `&str`.
    #[test]
    fn sorted_get_matches_a_scan() {
        for bits in 0..64 {
            let pairs: Vec<(u32, u32)> = members(bits).into_iter().map(|k| (k, 10 * k)).collect();
            for k in 0..8 {
                let want = pairs.iter().find(|p| p.0 == k).map(|p| &p.1);
                assert_eq!(sorted_get(&pairs, &k), want, "{bits} {k}");
            }
        }
        let named = [("a".to_string(), 1), ("c".to_string(), 3)];
        assert_eq!(sorted_get(&named, "c"), Some(&3));
        assert_eq!(sorted_get(&named, "b"), None);
        assert_eq!(sorted_get::<u32, u32, u32>(&[], &0), None);
        let ends = [(u64::MIN, 'a'), (u64::MAX, 'z')];
        assert_eq!(sorted_get(&ends, &u64::MAX), Some(&'z'));
        assert_eq!(sorted_get(&ends, &u64::MIN), Some(&'a'));
        assert_eq!(sorted_get(&ends, &1), None);
    }

    // Random lists against naive references (TEST-dry-shared-units), each with a faulty form as
    // its negative control, caught by the same check on some draw.

    use crate::seed::Rng;

    /// A strictly increasing list of up to `n` items of `lo..lo + w`, `lo` drawn near either end
    /// of `u64` or near 0.
    fn increasing(rng: &mut Rng, n: usize, w: u64) -> Vec<u64> {
        let lo = rng.pick(&[0, u64::MAX - w + 1, 1 << 40]);
        let mut v: Vec<u64> = (0..rng.below(n + 1))
            .map(|_| lo + rng.below_u64(w))
            .collect();
        v.sort_unstable();
        v.dedup();
        v
    }

    /// The three sorts with duplicates removed against a scan that keeps the first of each,
    /// on lists with many repeats; the faulty form of `sort_dedup_by`, one sort by the order
    /// and a `dedup` (DEDUP-keyed-sort-interleaved), is caught.
    #[test]
    fn sorts_with_duplicates_removed_match_a_scan() {
        let (mut rng, _) = Rng::fresh("sorts_with_duplicates_removed_match_a_scan");
        let mut caught = false;
        for round in 0..2000 {
            let n = rng.below(40);
            let v: Vec<(u8, u8)> = (0..n)
                .map(|_| (rng.below(4) as u8, rng.below(3) as u8))
                .collect();
            let mut first: Vec<(u8, u8)> = Vec::new();
            for x in &v {
                if !first.contains(x) {
                    first.push(*x);
                }
            }
            let mut want = first.clone();
            want.sort();
            let mut got = v.clone();
            sort_dedup(&mut got);
            assert_eq!(got, want, "round {round}: sort_dedup {v:?}");
            // By the key: the first item of each key in `v`, in the order of the keys.
            let mut want: Vec<(u8, u8)> = Vec::new();
            for x in &v {
                if !want.iter().any(|y| y.0 == x.0) {
                    want.push(*x);
                }
            }
            want.sort_by_key(|x| x.0);
            let mut got = v.clone();
            sort_dedup_by_key(&mut got, |x| x.0);
            assert_eq!(got, want, "round {round}: sort_dedup_by_key {v:?}");
            // By an order coarser than equality: each item once, at its first place, in the
            // stable order of the key.
            let mut want = first.clone();
            want.sort_by_key(|x| x.0);
            let mut got = v.clone();
            sort_dedup_by(&mut got, |x, y| x.0.cmp(&y.0));
            assert_eq!(got, want, "round {round}: sort_dedup_by {v:?}");
            let mut old = v.clone();
            old.sort_by_key(|x| x.0);
            old.dedup();
            caught |= old != want;
        }
        assert!(
            caught,
            "the negative control of sort_dedup_by was never caught"
        );
        let mut empty: Vec<u8> = Vec::new();
        sort_dedup(&mut empty);
        sort_dedup_by(&mut empty, u8::cmp);
        sort_dedup_by_key(&mut empty, |&x| x);
        assert!(empty.is_empty());
    }

    /// `merge`, `merge_into` and `union_all` against a sort of the items joined, on lists near
    /// the ends of `u64`; `merge_into` with an `out` that holds items from a call before; the
    /// faulty union of many lists, the lists joined unsorted, is caught.
    #[test]
    fn unions_of_random_lists_match_a_sort() {
        let (mut rng, _) = Rng::fresh("unions_of_random_lists_match_a_sort");
        let mut out = vec![7u64; 5];
        let mut caught = false;
        for round in 0..2000 {
            let (a, b) = (increasing(&mut rng, 30, 64), increasing(&mut rng, 30, 64));
            let mut want: Vec<u64> = a.iter().chain(&b).copied().collect();
            sort_dedup(&mut want);
            assert_eq!(merge(&a, &b), want, "round {round}: {a:?} {b:?}");
            let keep = |x: &u64| x % 3 != 0;
            merge_into(&a, &b, keep, &mut out);
            let kept: Vec<u64> = want.iter().copied().filter(keep).collect();
            assert_eq!(out, kept, "round {round}: merge_into {a:?} {b:?}");
            let lists: Vec<Vec<u64>> = (0..rng.below(9))
                .map(|_| increasing(&mut rng, 8, 64))
                .collect();
            let mut want: Vec<u64> = lists.iter().flatten().copied().collect();
            sort_dedup(&mut want);
            let joined: Vec<u64> = lists.iter().flatten().copied().collect();
            caught |= joined != want;
            assert_eq!(union_all(lists.clone()), want, "round {round}: {lists:?}");
        }
        assert!(caught, "the negative control of union_all was never caught");
        assert_eq!(union_all(vec![vec![3u8, 9]]), [3, 9]);
        assert_eq!(union_all(vec![Vec::<u8>::new(); 7]), Vec::<u8>::new());
        assert_eq!(merge::<u8>(&[], &[]), Vec::<u8>::new());
    }

    /// `merge_join` against a scan of the two lists, with repeats in each list (the documented
    /// form: a first copy is paired, a second comes alone), and its `size_hint` checked at each
    /// step against the steps left; the faulty join that pairs nothing is caught.
    #[test]
    fn merge_join_matches_a_scan_with_repeats() {
        let (mut rng, _) = Rng::fresh("merge_join_matches_a_scan_with_repeats");
        let mut caught = false;
        for round in 0..2000 {
            let draw = |rng: &mut Rng| {
                let mut v: Vec<u8> = (0..rng.below(12)).map(|_| rng.below(6) as u8).collect();
                v.sort_unstable();
                v
            };
            let (a, b) = (draw(&mut rng), draw(&mut rng));
            // The scan: the same walk written with indices.
            let mut want: Vec<Joined<u8, u8>> = Vec::new();
            let (mut i, mut j) = (0, 0);
            while i < a.len() || j < b.len() {
                if j == b.len() || (i < a.len() && a[i] < b[j]) {
                    want.push(Joined::Left(a[i]));
                    i += 1;
                } else if i == a.len() || b[j] < a[i] {
                    want.push(Joined::Right(b[j]));
                    j += 1;
                } else {
                    want.push(Joined::Both(a[i], b[j]));
                    (i, j) = (i + 1, j + 1);
                }
            }
            let mut it = merge_join(&a, &b, u8::cmp);
            let mut got = Vec::new();
            loop {
                let (low, high) = it.size_hint();
                let left = want.len() - got.len();
                assert!(low <= left && Some(left) <= high, "round {round}: hint");
                let Some(step) = it.next() else { break };
                got.push(match step {
                    Joined::Left(x) => Joined::Left(*x),
                    Joined::Right(y) => Joined::Right(*y),
                    Joined::Both(x, y) => Joined::Both(*x, *y),
                });
            }
            assert_eq!(got, want, "round {round}: {a:?} {b:?}");
            // Every item of each list is met once, in its order.
            let lefts: Vec<u8> = got
                .iter()
                .filter_map(|j| match j {
                    Joined::Left(x) | Joined::Both(x, _) => Some(*x),
                    Joined::Right(_) => None,
                })
                .collect();
            assert_eq!(lefts, a, "round {round}");
            let unpaired: Vec<Joined<u8, u8>> = a
                .iter()
                .map(|&x| Joined::Left(x))
                .chain(b.iter().map(|&y| Joined::Right(y)))
                .collect();
            caught |= unpaired != want;
        }
        assert!(
            caught,
            "the negative control of merge_join was never caught"
        );
        let a = [1u8, 1, 2];
        let b = [1u8];
        let j: Vec<_> = merge_join(&a, &b, u8::cmp).collect();
        assert_eq!(
            j,
            [Joined::Both(&1, &1), Joined::Left(&1), Joined::Left(&2)]
        );
    }

    /// `sorted_get` on random keys near the ends of `u64` against a scan; the faulty lookup by
    /// a search for the first key at or above, which finds a neighbor, is caught.
    #[test]
    fn sorted_get_matches_a_scan_on_random_keys() {
        let (mut rng, _) = Rng::fresh("sorted_get_matches_a_scan_on_random_keys");
        let mut caught = false;
        for round in 0..2000 {
            let keys = increasing(&mut rng, 20, 40);
            let pairs: Vec<(u64, usize)> = keys.iter().copied().zip(0..).collect();
            let at = keys.first().copied().unwrap_or(0);
            let k = at.wrapping_add(rng.below_u64(48)).wrapping_sub(4);
            let want = pairs.iter().find(|p| p.0 == k).map(|p| &p.1);
            assert_eq!(
                sorted_get(&pairs, &k),
                want,
                "round {round}: {k} in {keys:?}"
            );
            let near = pairs.get(pairs.partition_point(|p| p.0 < k)).map(|p| &p.1);
            caught |= near != want;
        }
        assert!(
            caught,
            "the negative control of sorted_get was never caught"
        );
    }
}
