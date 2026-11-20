//! A tree over the items `0..n`, each an integer, all 0 at the start: an addition to every item
//! of a range, and the search for the first item at or after a place whose value is at most a
//! bound, each O(log n) steps (PERF-sweep-bounded-wide-interval). The one user so far is
//! `zedc-presburger`'s `sweep_bounded`, which keeps for each residue modulo `q` the number of
//! conditions that forbid it, and asks for the first residue no condition forbids.
//!
//! The structure is the segment tree with range additions kept at the nodes and not pushed down
//! ("non-propagating lazy" updates): node `v` covers a range of items, `add[v]` is the sum of
//! the additions made to the whole of its range, and `min[v]` is the least value over its range
//! of the additions made at `v` and below it. So the value of item `i` is the sum of `add` over
//! the nodes on the path from the root to the leaf of `i`, and the least value over the range of
//! `v` is `min[v]` plus the sum of `add` over the strict ancestors of `v`.
//!
//! Source: J. L. Bentley, "Solutions to Klee's rectangle problems", Carnegie Mellon University,
//! 1977 (the segment tree; no DOI, not on Crossref, checked 2026-11-20; not read here, the
//! scheme recalled from memory as `zedc-preimage` recalls it). The additions kept at the nodes
//! are the usual variant, checked here by its own proof below, not against a text. Test:
//! `tests::additions_and_searches_match_an_array`.
//!
//! Proof of `add`: a node wholly inside the range takes the addition in `add` and `min`; a node
//! that meets the range only in part passes it to its children and sets `min` again from theirs
//! (`min[v] = min(min[l], min[r]) + add[v]`), which holds by induction from the leaves, since
//! each item of `v`'s range lies in exactly one child's. A node outside the range is unchanged.
//! The nodes reached are those on the two paths to the ends of the range and their children:
//! O(log n).
//!
//! Proof of `first_at_most`: the search carries `bound` less the `add` of the strict ancestors,
//! so at node `v` it compares the least value over `v`'s range with the bound exactly when it
//! compares `min[v]` with what it carries. A node that ends before `from`, or whose least value
//! is above the bound, holds no answer and is left at once. Otherwise the left child is tried
//! first and then the right one, so the first answer found is the least. Cost: a node that lies
//! wholly at or after `from` and whose least value is at most the bound holds an answer, and
//! from it the search goes down one path, since at each step the left child either holds an
//! answer (and is taken) or is left at once. The nodes that hold `from` strictly inside their
//! range lie on the one path to the leaf of `from`. So the search visits O(log n) nodes: that
//! path, one child of each node on it left at once, and one path down.
//!
//! Complexity tradeoff: the naive way keeps the values in an array: an addition to a range of
//! `k` items costs O(k), and a search O(n). Used: the tree, O(log n) each, and O(n) space (4n
//! nodes of two `i64` each), built in O(n).

/// The tree: `n` items, node 1 the root, node `v`'s children `2v` and `2v + 1`.
#[derive(Clone, Debug)]
pub struct MinAdd {
    n: usize,
    min: Vec<i64>,
    add: Vec<i64>,
}

impl MinAdd {
    /// `n` items, each 0.
    pub fn new(n: usize) -> Self {
        let nodes = if n == 0 { 0 } else { 4 * n };
        MinAdd {
            n,
            min: vec![0; nodes],
            add: vec![0; nodes],
        }
    }

    /// The number of items.
    pub fn len(&self) -> usize {
        self.n
    }

    /// Whether the tree has no items.
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    /// Adds `d` to each item of `lo..=hi`; nothing when `lo > hi`.
    ///
    /// # Panics
    ///
    /// When `lo <= hi` and `hi` is not below [`Self::len`], with the message "MinAdd::add to
    /// items {lo}..={hi} of a tree of {n} items".
    #[track_caller]
    pub fn add(&mut self, lo: usize, hi: usize, d: i64) {
        if lo > hi {
            return;
        }
        let n = self.n;
        assert!(
            hi < n,
            "MinAdd::add to items {lo}..={hi} of a tree of {n} items"
        );
        self.add_at(1, 0, n - 1, lo, hi, d);
    }

    fn add_at(&mut self, v: usize, nl: usize, nr: usize, lo: usize, hi: usize, d: i64) {
        if hi < nl || nr < lo {
            return;
        }
        if lo <= nl && nr <= hi {
            self.min[v] += d;
            self.add[v] += d;
            return;
        }
        let mid = nl + (nr - nl) / 2;
        self.add_at(2 * v, nl, mid, lo, hi, d);
        self.add_at(2 * v + 1, mid + 1, nr, lo, hi, d);
        self.min[v] = self.min[2 * v].min(self.min[2 * v + 1]) + self.add[v];
    }

    /// The least item at or after `from` whose value is at most `bound`, or `None`.
    pub fn first_at_most(&self, from: usize, bound: i64) -> Option<usize> {
        if from >= self.n {
            return None;
        }
        self.first_at(1, 0, self.n - 1, from, bound)
    }

    fn first_at(&self, v: usize, nl: usize, nr: usize, from: usize, bound: i64) -> Option<usize> {
        if nr < from || self.min[v] > bound {
            return None;
        }
        if nl == nr {
            return Some(nl);
        }
        // Saturated, a bound past `i64`'s range stays past every value an item can hold, so
        // no comparison changes, and an extreme `bound` does not overflow.
        let below = bound.saturating_sub(self.add[v]);
        let mid = nl + (nr - nl) / 2;
        self.first_at(2 * v, nl, mid, from, below)
            .or_else(|| self.first_at(2 * v + 1, mid + 1, nr, from, below))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// After each of 4n random additions to random ranges, by -2 to 2, every search from every
    /// place, at bounds -1, 0 and 1, gives what a scan of a plain array gives, for every n up
    /// to 40.
    #[test]
    fn additions_and_searches_match_an_array() {
        let (mut rng, _) = crate::seed::Rng::fresh("additions_and_searches_match_an_array");
        let mut next = move |m: u64| rng.below_u64(m);
        for n in 0..=40usize {
            let mut tree = MinAdd::new(n);
            let mut items = vec![0i64; n];
            for _ in 0..4 * n {
                let a = next(n as u64) as usize;
                let b = next(n as u64) as usize;
                let (lo, hi) = (a.min(b), a.max(b));
                let d = next(5) as i64 - 2;
                tree.add(lo, hi, d);
                for x in &mut items[lo..=hi] {
                    *x += d;
                }
                for from in 0..=n {
                    for bound in -1..=1 {
                        let want = (from..n).find(|&i| items[i] <= bound);
                        assert_eq!(
                            tree.first_at_most(from, bound),
                            want,
                            "n {n} from {from} bound {bound} items {items:?}"
                        );
                    }
                }
            }
            assert_eq!(tree.first_at_most(0, i64::MAX), (n > 0).then_some(0));
        }
    }

    /// An empty range adds nothing, and a range past the end is refused with its message.
    #[test]
    fn an_empty_range_adds_nothing_and_one_past_the_end_panics() {
        let mut tree = MinAdd::new(3);
        tree.add(2, 1, 5);
        assert_eq!(tree.first_at_most(0, 0), Some(0));
        let refused = std::panic::catch_unwind(move || tree.add(1, 3, 1));
        let msg = refused.expect_err("a range past the end was taken");
        let text = msg.downcast_ref::<String>().cloned().unwrap_or_default();
        assert_eq!(text, "MinAdd::add to items 1..=3 of a tree of 3 items");
    }
}
