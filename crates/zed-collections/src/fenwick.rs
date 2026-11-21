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
// 2026-11-20). Read 2026-11-21 (PDF, LibGen, verification only; title, author and the page
// range 327-336 checked on the copy's first page). The scheme above is the paper's. P. 328:
// "if the index contains a '2 bit' we include two frequencies, if it has an '8 bit' we
// include 8 frequencies"; element 4 holds frequencies 1 to 4 and element 6 frequencies 5 and
// 6, so element `r` holds the `lowbit(r)` items ending at `r`; a prefix is read by "stripping
// the least-significant 1 from the old index, and repeating this operation until the index is
// zero" (11, 10, 8, 0), which sums disjoint ranges that tile 1..11. P. 330: the AND of a
// number and its two's complement "isolates the least significant one bit". P. 331
// (Figure 5): an update, "instead of stripping off the least-significant 1 bit ..., we now
// add it on at each stage to get the next entry to adjust" (5, 6, 8), which visits exactly
// the elements whose ranges cover the item. P. 333 (Figure 8): the search for a cumulative
// value starts with a mask at the table's midpoint, moves the base up by the mask when the
// target is at least the node there, subtracting that node, and halves the mask; it is
// correct because the node at `base + mask` holds exactly the items between `base` and
// `base + mask` while `mask` is below `lowbit(base)`. Departures: the paper's element 0 is a
// separate frequency and its indices count from 1; here items count from 0 and node `r` is
// stored at `r - 1`. Nodes hold any combination with an identity, not only frequencies,
// which is sound for any associative combination in `prefix` and `descend`, and for
// `update` only when the change distributes over the combination (an addition over sums, a
// raise over maxima). Test:
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
    ///
    /// # Panics
    ///
    /// When `i` is not below [`Self::len`], with the message "Fenwick::update of item {i} in a
    /// tree of {n} items". Until TEST-dry-shared-units such a change was dropped with no
    /// error: node `i + 1` and every node above it lie past the end, so the loop below ran
    /// no step (and `i + 1` overflowed at `usize::MAX`).
    #[track_caller]
    pub fn update(&mut self, i: usize, mut f: impl FnMut(&mut T)) {
        let n = self.nodes.len();
        assert!(i < n, "Fenwick::update of item {i} in a tree of {n} items");
        let mut r = i + 1;
        while r <= self.nodes.len() {
            f(&mut self.nodes[r - 1]);
            r += r.isolate_lowest_one();
        }
    }

    /// The fold of `f` from `init` over nodes that together cover the items `0..i` once each,
    /// O(log n) of them: for sums, the sum of the first `i` items. `i` at most [`Self::len`].
    ///
    /// # Panics
    ///
    /// When `i` is past [`Self::len`], with the message "Fenwick::prefix of {i} items in a tree
    /// of {n} items". Without the check the first step indexes node `i - 1`, past the end, and
    /// panics with the index of a node, not the prefix asked for.
    #[track_caller]
    pub fn prefix<A>(&self, i: usize, init: A, mut f: impl FnMut(A, &T) -> A) -> A {
        let n = self.nodes.len();
        assert!(
            i <= n,
            "Fenwick::prefix of {i} items in a tree of {n} items"
        );
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

    // Longer trees, the ends, and the preconditions (TEST-dry-shared-units).

    use crate::seed::Rng;

    /// Random lengths up to 3000, against an array: prefix sums of random places after random
    /// changes, sums near `i64::MAX` taken by wrapping so no step overflows, and the count of
    /// nodes each update and prefix reads, at most `floor(log2 n) + 1`. The faulty update that
    /// changes only the item's own node, its negative control, is caught by the same sums.
    #[test]
    fn long_trees_match_an_array() {
        let (mut rng, _) = Rng::fresh("long_trees_match_an_array");
        let mut caught = false;
        for round in 0..60 {
            let n = 1 + rng.below(3000);
            let bound = n.ilog2() + 1;
            let mut tree = Fenwick::new(n, 0u64);
            let mut faulty = Fenwick::new(n, 0u64);
            let mut items = vec![0u64; n];
            for _ in 0..200 {
                let i = rng.below(n);
                let small = rng.below_u64(1000);
                let d = rng.pick(&[1, u64::MAX, u64::MAX / 3, small]);
                items[i] = items[i].wrapping_add(d);
                let mut read = 0;
                tree.update(i, |s| {
                    read += 1;
                    *s = s.wrapping_add(d);
                });
                assert!(
                    read <= bound,
                    "round {round}: update read {read} nodes of {n}"
                );
                faulty.nodes[i] = faulty.nodes[i].wrapping_add(d);
                let j = rng.below(n + 1);
                let want = items[..j].iter().fold(0u64, |a, x| a.wrapping_add(*x));
                let mut read = 0;
                let got = tree.prefix(j, 0u64, |a, s| {
                    read += 1;
                    a.wrapping_add(*s)
                });
                assert_eq!(got, want, "round {round}: prefix {j} of {n}");
                assert!(
                    read <= bound,
                    "round {round}: prefix read {read} nodes of {n}"
                );
                caught |= faulty.prefix(j, 0u64, |a, s| a.wrapping_add(*s)) != want;
            }
        }
        assert!(caught, "the negative control of update was never caught");
    }

    /// An empty tree: no prefix but the empty one, and the descent stops at once.
    #[test]
    fn an_empty_tree() {
        let t: Fenwick<i32> = Fenwick::new(0, 0);
        assert!(t.is_empty());
        assert_eq!(t.len(), 0);
        assert_eq!(t.prefix(0, 7, |a, s| a + s), 7);
        assert_eq!(t.descend(5, |_, _| unreachable!()), (0, 5));
        let one = {
            let mut t = Fenwick::new(1, 0i32);
            t.update(0, |s| *s += 4);
            t
        };
        assert_eq!(one.prefix(1, 0, |a, s| a + s), 4);
        assert_eq!(one.descend(0, |a, s| (a + s < 5).then_some(a + s)), (1, 4));
        assert_eq!(one.descend(0, |a, s| (a + s < 4).then_some(a + s)), (0, 0));
    }

    /// The text of the panic of `f`, which must panic.
    fn panic_text(f: impl FnOnce() + std::panic::UnwindSafe) -> String {
        let p = std::panic::catch_unwind(f).expect_err("it panics");
        p.downcast_ref::<String>()
            .cloned()
            .expect("a formatted message")
    }

    /// An item past the end, for an update, and a prefix past the end.
    #[test]
    fn places_past_the_end_are_refused() {
        assert_eq!(
            panic_text(|| Fenwick::new(3, 0i32).update(3, |s| *s += 1)),
            "Fenwick::update of item 3 in a tree of 3 items"
        );
        assert_eq!(
            panic_text(|| Fenwick::new(0, 0i32).update(usize::MAX, |s| *s += 1)),
            format!(
                "Fenwick::update of item {} in a tree of 0 items",
                usize::MAX
            )
        );
        assert_eq!(
            panic_text(|| {
                Fenwick::new(3, 0i32).prefix(4, 0, |a, s| a + s);
            }),
            "Fenwick::prefix of 4 items in a tree of 3 items"
        );
        // At the end itself both are kept.
        let mut t = Fenwick::new(3, 0i32);
        t.update(2, |s| *s += 1);
        assert_eq!(t.prefix(3, 0, |a, s| a + s), 1);
    }
}
