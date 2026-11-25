//! The tuples of [`super`], each held as one id: a hash-consed binary tree of fixed shape over the
//! coordinates (PERIOD-B-P1-intern-rest, XR-presburger4 META4 order 8). A tuple is the root of a
//! tree whose leaves are its values; each inner node is interned by its pair of children, so
//! equal subtrees share one id, and two tuples are equal exactly when their roots are (by
//! induction on the shape, which is fixed, so a node's place in it says what its children are).
//! A block that moves the coordinates `mv` reads them, and builds a tuple that differs from one
//! held only in them, by visiting the union of the paths from the root to their leaves: the
//! nodes off those paths are kept by their ids, not copied.
//!
//! Why a tree and not "the moved coordinates, the rest one id": the rest changes with the block,
//! so a rest interned for one block must be taken apart for the next. Interning, for each
//! coordinate, only the blocks between the first and the last that move it still holds every
//! coordinate whose first and last movers lie far apart: with the blocks in a fixed order
//! (here the order of their moduli), some family has `Θ(k)` such coordinates over `Θ(k)` blocks,
//! `Θ(k²)` words (b22-presburger6; `tests::spanning_rows`). The tree's cost per block does not
//! depend on the order of the blocks.
//!
//! Prior work: Laarman, van de Pol and Weber, "Parallel Recursive State Compression for Free"
//! (SPIN 2011, arXiv:1104.3119), store the state vectors of a model checker the same way, "a
//! balanced binary tree of tables" (Section 3.1), and update a state from its predecessor
//! along the changed paths only (Section 3.4): "For a state vector of size `k`, the number of
//! table accesses can be brought down to `log_2(k)` (the height of the tree) assuming only one
//! slot changed. When `c` slots change, the maximum number of accesses is `c × log_2(k)`, but
//! likely fewer if the slots are close to each other in the tree (due to shared paths to the
//! root)." (arXiv source `3_treedbs.tex`, read 2026-11-24.) Here one table serves every node,
//! which keeps the equality above, and the shape is not balanced but weighted, as follows.
//!
//! The shape: Huffman's tree (Huffman, "A Method for the Construction of Minimum-Redundancy
//! Codes", Proc. IRE 40(9), 1952, doi:10.1109/JRPROC.1952.273898) for the weights `f_c`, `f_c`
//! the tuples whose coordinate `c` the blocks and the literals are expected to visit (the caller
//! sums the estimates of `R_b` over the blocks moving `c`, plus one). The visits cost at most
//! `sum_c f_c (depth(c) + 1)` nodes. Bound: let `F = sum_c f_c`, `H = sum_c (f_c / F) log2(F /
//! f_c)`. Proof that `sum_c f_c depth(c) < F (H + 1)`: the lengths `l_c = ceil(log2(F / f_c))`
//! satisfy `sum_c 2^-l_c <= sum_c f_c / F = 1`, so (Kraft's inequality, converse) a binary tree
//! has the leaves at those depths or less: take the `l_c` in increasing order and give each the
//! next interval of length `2^-l_c` in `[0, 1)`, which starts at a multiple of its length since
//! every length before it is a multiple too, so the intervals are the nodes of the complete tree
//! at depths `l_c` and none contains another; removing the nodes with one child only shortens
//! paths. That tree costs at most `sum_c f_c l_c < sum_c f_c (log2(F / f_c) + 1) = F (H + 1)`;
//! Huffman's tree has the least `sum_c f_c depth(c)` of all binary trees with these leaves
//! (Huffman 1952, the "minimum-redundancy" of the title). `H <= log2 C`, so the cost is never
//! above a balanced tree's; in `tests::spanning_rows` the coordinate every middle block moves
//! weighs about half of `F` and sits at depth 1, and the work is linear in `k`.
//!
//! Depth: below 180 when `F < 2^124`, so the recursions below are shallow. The caller's weights
//! are sums of terms each below `2^64`, one term per entry of vectors it holds in memory, so
//! fewer than `2^60` terms in all and `F < 2^124` (and the sums `wa + wb` below do not overflow
//! `u128`). Proof: in Huffman's tree, when two nodes `v, s` are merged
//! every other node waiting weighs at least `max(w(v), w(s))`, and the sibling `u` of their
//! parent `p` is one of those or is merged later from them, so `w(u) >= w(v)`. Along the path
//! from a leaf up, the weights `a_0 <= a_1 <= ...` thus satisfy `a_{i+2} = a_{i+1} + w(u) >=
//! a_{i+1} + a_i`, so `a_d >= Fib(d + 1)` for a leaf at depth `d` (`f_c >= 1`), and
//! `Fib(d + 1) <= F < 2^124 < Fib(181)` (`log2 Fib(181) = 181 log2 φ - log2 √5 + ε ≈ 124.5`)
//! gives `d + 1 < 181`.

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use zed_collections::intern::Interner;
use zed_kernel::digest::TextState;

#[cfg(test)]
thread_local! {
    /// Tests only: the words written to build the tuples reached on this thread (PRES-B-P1-
    /// copied-words), so that a test sees copies the units hide beside the walks of the blocks.
    pub(in super::super) static COPIED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Counts `n` words written to build tuples (`COPIED`, tests only). Written here, not in
/// `sumset.rs`, so that this file names nothing of that one (test `s_01f_import_graph`).
fn copied(n: u64) {
    #[cfg(test)]
    COPIED.with(|c| c.set(c.get().saturating_add(n)));
    #[cfg(not(test))]
    let _ = n;
}

/// An inner node of the shape: its leaves are the positions `lo..hi`, its left child's
/// `lo..mid`; a child is `None` when it is a leaf (one position), else its index.
#[derive(Clone, Copy)]
struct Split {
    lo: usize,
    mid: usize,
    left: Option<usize>,
    right: Option<usize>,
}

/// The coordinates a block moves, as positions of the shape in order (`ps`) and, for each,
/// its index in the block's list (`ord`).
pub(super) struct Moved {
    ps: Vec<usize>,
    ord: Vec<usize>,
}

/// The table of tuples over `C` coordinates. A tuple's id is the id of its root node; with one
/// coordinate it is the value itself, with none 0.
pub(super) struct Tuples {
    splits: Vec<Split>,
    root: Option<usize>,
    /// The position (in the order of the leaves) of each coordinate, and the coordinate at each.
    pos: Vec<usize>,
    at: Vec<usize>,
    /// Hashed by [`TextState`] (foldhash, seeded per table), not the standard map's SipHash-1-3,
    /// which costs several times as many instructions on a pair of words; a node is looked up at
    /// every inner node a block rebuilds (PERF-sumset-tuples-walks). The ids do not depend on the
    /// hasher (the interner numbers pairs in the order first met), so neither does any answer.
    /// The values at the leaves come from the program's constants, so the hasher is the seeded
    /// one, not the unseeded [`zed_kernel::digest::Digest`] (see its `DigestMap`: hash flooding).
    nodes: Interner<(usize, usize), TextState>,
}

impl Tuples {
    /// The shape of Huffman's tree for `weights`, one per coordinate, each at least 1, ties
    /// broken by the order of the coordinates, so the shape is a function of the weights.
    /// O(C log C).
    pub(super) fn new(weights: &[u128]) -> Tuples {
        let n = weights.len();
        // A heap item is `(weight, code)`, the code `c < n` for coordinate `c`, `n + s` for
        // inner node `s`.
        let mut heap: BinaryHeap<Reverse<(u128, usize)>> = (weights.iter().enumerate())
            .map(|(c, &w)| Reverse((w, c)))
            .collect();
        let mut kids: Vec<(usize, usize)> = Vec::with_capacity(n.saturating_sub(1));
        while heap.len() > 1 {
            let Reverse((wa, a)) = heap.pop().expect("two items");
            let Reverse((wb, b)) = heap.pop().expect("two items");
            heap.push(Reverse((wa + wb, n + kids.len())));
            kids.push((a, b));
        }
        let mut t = Tuples {
            splits: Vec::with_capacity(kids.len()),
            root: None,
            pos: vec![0; n],
            at: Vec::with_capacity(n),
            nodes: Interner::default(),
        };
        if let Some(Reverse((_, top))) = heap.pop() {
            t.root = t.place(top, n, &kids);
        }
        t
    }

    /// Numbers the leaves under `code` in order from `self.at.len()`, and returns the index of
    /// its split (`None` for a leaf).
    fn place(&mut self, code: usize, n: usize, kids: &[(usize, usize)]) -> Option<usize> {
        if code < n {
            self.pos[code] = self.at.len();
            self.at.push(code);
            return None;
        }
        let (a, b) = kids[code - n];
        let lo = self.at.len();
        let left = self.place(a, n, kids);
        let mid = self.at.len();
        let right = self.place(b, n, kids);
        self.splits.push(Split {
            lo,
            mid,
            left,
            right,
        });
        Some(self.splits.len() - 1)
    }

    /// The coordinates `mv` (distinct) as a [`Moved`].
    pub(super) fn moved(&self, mv: &[usize]) -> Moved {
        let mut ord: Vec<usize> = (0..mv.len()).collect();
        ord.sort_unstable_by_key(|&i| self.pos[mv[i]]);
        let ps = ord.iter().map(|&i| self.pos[mv[i]]).collect();
        Moved { ps, ord }
    }

    /// The nodes visited to read or rebuild the coordinates of `m`: the union of their paths,
    /// leaves included. O(that number).
    pub(super) fn visits(&self, m: &Moved) -> u64 {
        fn go(t: &Tuples, s: Option<usize>, ps: &[usize]) -> u64 {
            let Some(s) = s else { return 1 };
            let k = ps.partition_point(|&p| p < t.splits[s].mid);
            let mut n = 1;
            if k > 0 {
                n += go(t, t.splits[s].left, &ps[..k]);
            }
            if k < ps.len() {
                n += go(t, t.splits[s].right, &ps[k..]);
            }
            n
        }
        if m.ps.is_empty() {
            return 0;
        }
        go(self, self.root, &m.ps)
    }

    /// The id of the tuple with `vals[c]` at each coordinate `c`. O(C).
    pub(super) fn make(&mut self, vals: &[usize]) -> usize {
        fn go(t: &mut Tuples, s: Option<usize>, lo: usize, vals: &[usize]) -> usize {
            let Some(s) = s else {
                return vals[t.at[lo]];
            };
            let sp = t.splits[s];
            let l = go(t, sp.left, sp.lo, vals);
            let r = go(t, sp.right, sp.mid, vals);
            copied(2);
            t.nodes.intern((l, r))
        }
        if self.at.is_empty() {
            return 0;
        }
        go(self, self.root, 0, vals)
    }

    /// Writes the value of each coordinate of `m` in tuple `id` to `out` at its index in the
    /// block's list (`out` at least that long). One walk, O([`Tuples::visits`]), nothing
    /// allocated, so a caller reading many tuples reuses one `out`.
    pub(super) fn read_into(&self, id: usize, m: &Moved, out: &mut [usize]) {
        fn go(
            t: &Tuples,
            s: Option<usize>,
            r: usize,
            ps: &[usize],
            ord: &[usize],
            out: &mut [usize],
        ) {
            let Some(s) = s else {
                out[ord[0]] = r;
                return;
            };
            let sp = t.splits[s];
            let (l, rr) = t.nodes[r];
            let k = ps.partition_point(|&p| p < sp.mid);
            if k > 0 {
                go(t, sp.left, l, &ps[..k], &ord[..k], out);
            }
            if k < ps.len() {
                go(t, sp.right, rr, &ps[k..], &ord[k..], out);
            }
        }
        if !m.ps.is_empty() {
            go(self, self.root, id, &m.ps, &m.ord, out);
        }
    }

    /// The id of tuple `id` with each coordinate of `m` replaced by `f(i, v)`, `i` its index in
    /// the block's list and `v` its value in `id` (PERF-sumset-tuples-walks). One walk reads and
    /// rebuilds: a block that shifts a tuple passes `v + w_i`, one that takes a tuple apart
    /// records `v` and passes 0, one that builds a tuple from a rest passes the new value. The
    /// two walks and three vectors it replaced (`read`, then `set` with a vector in the order of
    /// the leaves) ran 104.5M instructions at `k = 120` on `tests::spanning_rows(k, 13)`, more
    /// than the 81.5M of the vectors of b71e720ba (b22-period1, jobs m13 and neg13); with this
    /// walk and the foldhash maps of `scaled`, 66.4M (b22-period2, job new2).
    /// O([`Tuples::visits`]); an inner node whose children come back unchanged is returned as it
    /// is, not interned again: its id is the one interned for that pair before, since the
    /// interner gives each pair one id. So a block whose `f` leaves a value as it was (a shift by
    /// 0, a rest already 0) costs no lookup at the nodes above it.
    pub(super) fn map(
        &mut self,
        id: usize,
        m: &Moved,
        mut f: impl FnMut(usize, usize) -> usize,
    ) -> usize {
        fn go<F: FnMut(usize, usize) -> usize>(
            t: &mut Tuples,
            s: Option<usize>,
            r: usize,
            ps: &[usize],
            ord: &[usize],
            f: &mut F,
        ) -> usize {
            let Some(s) = s else {
                return f(ord[0], r);
            };
            let sp = t.splits[s];
            let (l0, r0) = t.nodes[r];
            let k = ps.partition_point(|&p| p < sp.mid);
            let l = if k > 0 {
                go(t, sp.left, l0, &ps[..k], &ord[..k], f)
            } else {
                l0
            };
            let rr = if k < ps.len() {
                go(t, sp.right, r0, &ps[k..], &ord[k..], f)
            } else {
                r0
            };
            if (l, rr) == (l0, r0) {
                return r;
            }
            copied(2);
            t.nodes.intern((l, rr))
        }
        if m.ps.is_empty() {
            return id;
        }
        go(self, self.root, id, &m.ps, &m.ord, &mut f)
    }
}
