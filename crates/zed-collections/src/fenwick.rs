//! A Fenwick tree (binary indexed tree; Fenwick 1994, "A new data structure for cumulative
//! frequency tables") over the items `0..n` (DRY-sorted-structures-2): a change at one item and
//! a fold over the items below a place, each O(log n) steps, and the descent that finds the
//! longest prefix whose fold keeps a property, O(log n) steps as well.
//!
//! The tree is generic over what a node holds and how two are combined, so the one structure
//! serves prefix sums of integers and prefix maxima under an order of the caller's. Node `r`
//! (counting from 1) holds the combination of the items `r - lowbit(r) .. r`, where
//! `lowbit(r)` is the lowest set bit of `r`; it is stored at `r - 1`.
//!
//! A change must be one each node can take without knowing the item's old value: an addition
//! for sums, but for maxima only a raise. A lowered item would leave its old value in the nodes
//! above it, so maxima of items that can fall need another structure.

// Source: P. M. Fenwick, "A new data structure for cumulative frequency tables", Software:
// Practice and Experience 24(3):327-336, 1994, doi:10.1002/spe.4380240306 (checked on Crossref
// 2026-11-20). Not read: no free copy was found. The scheme above (node `r` covers `lowbit(r)`
// items ending at `r`; an update adds `lowbit` to climb, a prefix clears it to descend; a
// search for a cumulative value halves a power-of-two step) is the paper's as it is commonly
// described, recalled from memory, not checked against the text. Departure: nodes hold any
// combination with an identity, not only frequencies, which is sound for any associative
// combination in `prefix` and `descend`, and for `update` only when the change distributes
// over the combination (an addition over sums, a raise over maxima). Test:
// `tests::prefixes_and_descents_match_an_array`, sums and maxima of every prefix and every
// descent against a plain array after each of 3n random changes, for every n up to 33; it
// raises maxima only, and it does not measure the O(log n) cost.

/// A Fenwick tree over `n` items, each node a `T`.
#[derive(Clone, Debug)]
pub struct Fenwick<T> {
    nodes: Vec<T>,
}

impl<T: Clone> Fenwick<T> {
    /// A tree over `n` items whose every node is `empty`, the identity of the combination the
    /// caller uses (0 for sums, `None` for maxima).
    pub fn new(n: usize, empty: T) -> Self {
        Fenwick {
            nodes: vec![empty; n],
        }
    }
}

impl<T> Fenwick<T> {
    /// The number of items.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the tree has no items.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Calls `f` on each node that covers item `i`, O(log n) of them, lowest first: the change
    /// of item `i` made in every node that combines it, as `+= d` for sums.
    pub fn update(&mut self, i: usize, mut f: impl FnMut(&mut T)) {
        let mut r = i + 1;
        while r <= self.nodes.len() {
            f(&mut self.nodes[r - 1]);
            r += r.isolate_lowest_one();
        }
    }

    /// The fold of `f` from `init` over nodes that together cover the items `0..i` once each,
    /// O(log n) of them: for sums, the sum of the first `i` items. `i` at most [`Self::len`].
    pub fn prefix<A>(&self, i: usize, init: A, mut f: impl FnMut(A, &T) -> A) -> A {
        let (mut r, mut acc) = (i, init);
        while r > 0 {
            acc = f(acc, &self.nodes[r - 1]);
            r &= r - 1;
        }
        acc
    }

    /// The longest prefix `0..i` whose fold keeps a property, and its fold: from `init` for the
    /// empty prefix, `f(acc, node)` gives the fold of the prefix extended by a node's items, or
    /// `None` where the extended prefix loses the property. The property must hold on every
    /// shorter prefix of one it holds on (for sums of items at least 0, "below a target"), so
    /// the answer is found by one descent from the highest power of 2, O(log n) calls of `f`.
    pub fn descend<A>(&self, init: A, mut f: impl FnMut(&A, &T) -> Option<A>) -> (usize, A) {
        let n = self.nodes.len();
        let (mut i, mut acc) = (0, init);
        if n == 0 {
            return (i, acc);
        }
        let mut step = 1usize << n.ilog2();
        while step > 0 {
            if i + step <= n
                && let Some(next) = f(&acc, &self.nodes[i + step - 1])
            {
                (i, acc) = (i + step, next);
            }
            step >>= 1;
        }
        (i, acc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sums and maxima of every prefix after each change, and the descent, against a plain
    /// array, for every length up to 33.
    #[test]
    fn prefixes_and_descents_match_an_array() {
        let (mut rng, _) = crate::seed::Rng::fresh("prefixes_and_descents_match_an_array");
        let mut next = move |m: u64| rng.below_u64(m);
        for n in 0..=33usize {
            let mut sums = Fenwick::new(n, 0i64);
            let mut maxs = Fenwick::new(n, None::<u64>);
            let mut items = vec![0i64; n];
            let mut tops = vec![None::<u64>; n];
            for _ in 0..3 * n {
                let i = next(n as u64) as usize;
                let d = next(5) as i64;
                items[i] += d;
                sums.update(i, |s| *s += d);
                let v = next(100);
                tops[i] = tops[i].max(Some(v));
                maxs.update(i, |m| *m = (*m).max(Some(v)));
                for j in 0..=n {
                    let want: i64 = items[..j].iter().sum();
                    assert_eq!(sums.prefix(j, 0, |a, s| a + s), want);
                    let top = tops[..j].iter().copied().max().flatten();
                    assert_eq!(maxs.prefix(j, None, |a, m| a.max(*m)), top);
                }
                let total: i64 = items.iter().sum();
                for target in 0..=total + 1 {
                    let got = sums.descend(0, |a, s| (a + s < target).then_some(a + s));
                    let mut want = (0, 0);
                    while want.0 < n && want.1 + items[want.0] < target {
                        want = (want.0 + 1, want.1 + items[want.0]);
                    }
                    assert_eq!(got, want, "n={n} target={target}");
                }
            }
        }
    }
}
