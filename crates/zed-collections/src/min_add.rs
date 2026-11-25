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
//! Source: J. L. Bentley and D. Wood, "An optimal worst case algorithm for reporting
//! intersections of rectangles", IEEE Trans. Computers C-29(7), 1980, pp. 571-577,
//! doi:10.1109/TC.1980.1675628, sec. IV "The segment tree", pp. 573-575, read 2026-11-20 in
//! full (a copy kept outside the repository). P. 574: "We "mark" with an X every node in the
//! tree whose interval is contained in X, on the condition that that node's father is not also
//! contained in X. We call this the canonical covering of X in the tree", and "the algorithm
//! visits at most four nodes and marks at most two nodes on each of the lg m + 1 levels of the
//! tree when representing any segment". The nodes that take an addition in `add` below are
//! exactly the canonical covering of the range, so `add` is their insertion with a number in
//! place of the segment's name, and its O(log n) bound is theirs. Departures: they keep at a
//! node the list of segments that mark it and answer which segments cover a point; this tree
//! keeps the sum of the additions and the least value over the node's range (`min`), and
//! answers the first item at most a bound, which the paper does not do, so `min` and
//! `first_at_most` rest on the proofs below, not on the paper. The paper credits "a very
//! similar structure" to J. L. Bentley, "Algorithms for Klee's rectangle problems",
//! unpublished notes, Carnegie-Mellon Univ., 1977 (its reference 2); J. van Leeuwen and D.
//! Wood, "The measure problem for rectangular ranges in d-space", Utrecht Univ. report
//! RUU-CS-79-06, 1979, <https://dspace.library.uu.nl/handle/1874/15897>, p. 20, reference 1
//! (read 2026-11-20), cite the same notes as "Solutions to Klee's rectangle problems". The
//! notes are not read: searched under both titles on 2026-11-21 through every rung of the
//! allpapers ladder, none with a copy: paperclip (keyword, semantic, and grep of both result
//! sets: only citing papers), allpapers-locate (Unpaywall, OpenAlex, CORE; no record; the
//! notes have no DOI and are not on Crossref), Google Scholar (citation stubs only, no
//! version with a file), Google web search through agy (only citing works), dblp (bot check,
//! both mirrors), the CMU SCS report archive (lists start at 1985), KiltHub (no match),
//! archive.org full-text search (68 books and reports quote the reference line, none is the
//! notes; its DTIC scans hold other 1977-1983 Bentley reports), the Wayback Machine (no
//! snapshot), HathiTrust (Cloudflare block), LibGen by title (0 hits), Anna's Archive
//! (DDoS-Guard block), welib (captcha); Sci-Hub and Sci-Net need a DOI. Searched again
//! 2026-11-21 (CITE-unfound-four), no copy found: KiltHub and all of figshare through its
//! search API (no match under either title; "rectangle problems" gives later work only),
//! LibGen "Klee rectangle" (0 hits), bitsavers' file index (no match; its Xerox PARC
//! CSL-80-9 is a later report), DTIC's PDF of the 1981 CMU report ADA106552 (403), a web
//! search (citing works only), a grounded agy search (timed out at 300 s). Nothing here
//! rests on the notes: the canonical covering and its bound are Bentley and Wood's, read
//! above.
//! Test:
//! `tests::additions_and_searches_match_an_array`; it compares with an array on random
//! operations for n from 0 to 40, so it cannot catch a cost above O(log n) that still gives
//! right answers.
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
        self.first_at(1, 0, self.n - 1, from, i128::from(bound))
    }

    fn first_at(&self, v: usize, nl: usize, nr: usize, from: usize, bound: i128) -> Option<usize> {
        if nr < from || i128::from(self.min[v]) > bound {
            return None;
        }
        if nl == nr {
            return Some(nl);
        }
        // A later addition can bring a bound outside the i64 range back into it.
        let below = bound - i128::from(self.add[v]);
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

    #[test]
    fn opposite_additions_keep_an_extreme_bound_exact() {
        let mut tree = MinAdd::new(4);
        tree.add(0, 3, -1);
        tree.add(1, 1, i64::MAX);
        tree.add(0, 1, 1);

        assert_eq!(tree.first_at_most(1, i64::MAX), Some(1));
        assert_eq!(tree.first_at_most(1, i64::MAX - 1), Some(2));
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
