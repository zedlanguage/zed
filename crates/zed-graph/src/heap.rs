//! A heap that yields its least element first, and the search of Dijkstra built on it.
//!
//! [`MinHeap`] is `BinaryHeap<Reverse<T>>` under one name, so the workspace's many least-first
//! queues share one type and none of them writes `Reverse` at each push and pop. Its order is
//! that of `T`: a queue of `(key, node)` pairs breaks ties of key by node, as every caller's
//! `BinaryHeap<Reverse<(key, node)>>` did.
//!
//! [`Dijkstra`] is the lazy-deletion form of Dijkstra's search (E. W. Dijkstra, "A note on two
//! problems in connexion with graphs", Numerische Mathematik 1, 269-271, 1959,
//! doi:10.1007/BF01386390; the paper keeps no heap, the lazy-deletion heap is the usual later
//! form): a label per node, lowered only when a strictly smaller distance is found, each
//! lowering pushing a new entry, and an entry skipped when it comes up if its node's label has
//! fallen since. With
//! every weight 0 or more, the first entry of a node that comes up at its label is its least
//! distance, and it comes up once, since a label never falls to the value it already has:
//! O(m log m) for m lowerings, each one a heap push. A potential `p` makes the reduced weight
//! of an edge `x → y` of weight `w` equal to `p(x) + w - p(y)`; [`reduced`] checks that it is
//! 0 or more, which is what makes the search exact on graphs with negative weights
//! (D. B. Johnson, "Efficient algorithms for shortest paths in sparse networks", JACM 24(1),
//! 1-13, 1977, doi:10.1145/321992.321993). Checked 2026-11-20: both DOIs on Crossref; the
//! papers not read, from memory. `dijkstra_on_reduced_weights_gives_least_distances` checks the
//! distances against Bellman–Ford on the raw weights, `a_negative_reduced_weight_is_refused`
//! the check of [`reduced`], and `stale_entries_come_up_as_stale` the lazy deletion.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

/// A queue that yields its least element first.
#[derive(Clone, Debug)]
pub struct MinHeap<T>(BinaryHeap<Reverse<T>>);

impl<T: Ord> MinHeap<T> {
    /// An empty heap.
    pub fn new() -> MinHeap<T> {
        MinHeap(BinaryHeap::new())
    }

    /// Adds `x`, O(log n).
    pub fn push(&mut self, x: T) {
        self.0.push(Reverse(x));
    }

    /// Removes and returns the least element, O(log n).
    pub fn pop(&mut self) -> Option<T> {
        self.0.pop().map(|Reverse(x)| x)
    }

    /// The least element, O(1).
    pub fn peek(&self) -> Option<&T> {
        self.0.peek().map(|Reverse(x)| x)
    }

    /// The number of elements.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the heap holds no element.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Removes every element, keeping the memory.
    pub fn clear(&mut self) {
        self.0.clear();
    }
}

impl<T: Ord> Default for MinHeap<T> {
    fn default() -> MinHeap<T> {
        MinHeap::new()
    }
}

/// The heap of the elements of `iter`, built in O(n) (`BinaryHeap::from` of a vector), not
/// by n pushes in O(n log n).
impl<T: Ord> FromIterator<T> for MinHeap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> MinHeap<T> {
        MinHeap(iter.into_iter().map(Reverse).collect())
    }
}

/// The labels of a [`Dijkstra`] search, by node: a vector for nodes `0..n` that all have a
/// label from the start, or a map for nodes met as the search goes, where a vector of `n`
/// entries would cost O(n) for each search of a small part of a large graph.
pub trait Labels<K, D> {
    /// The label of `k`, `None` while it has none.
    fn label(&self, k: &K) -> Option<&D>;
    /// Sets the label of `k` to `d`.
    fn set_label(&mut self, k: K, d: D);
}

/// Every node `0..len` labeled from the start.
impl<D> Labels<usize, D> for Vec<D> {
    fn label(&self, k: &usize) -> Option<&D> {
        Some(&self[*k])
    }

    fn set_label(&mut self, k: usize, d: D) {
        self[k] = d;
    }
}

impl<K: Ord, D> Labels<K, D> for BTreeMap<K, D> {
    fn label(&self, k: &K) -> Option<&D> {
        self.get(k)
    }

    fn set_label(&mut self, k: K, d: D) {
        self.insert(k, d);
    }
}

/// A reduced weight below zero: the potential does not hold at an edge, so the search on the
/// reduced weights would not be Dijkstra's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NegativeReducedWeight;

/// The reduced weight `r` of an edge, `Err` when it is below `zero`.
pub fn reduced<D: Ord>(r: D, zero: &D) -> Result<D, NegativeReducedWeight> {
    if r < *zero {
        Err(NegativeReducedWeight)
    } else {
        Ok(r)
    }
}

/// The lazy-deletion search of Dijkstra over nodes `K` at distances `D`, with its labels `L`
/// (see the module's notes). The caller reads the edges of each node [`Dijkstra::pop`] gives
/// and [`Dijkstra::lower`]s their heads, so it decides where the search stops and which edges
/// it follows; [`reduced`] checks each weight it adds.
///
/// # Cost, proved
///
/// Take a search from `s` starts in which the caller, as above, lowers only the heads of the
/// edges of the nodes [`Dijkstra::pop`] gives, every weight 0 or more, and let `e` be the
/// number of edges out of the nodes it gives. Then it pushes at most `s + e` entries, takes at
/// most `s + e`, and costs O((s + e) log(s + e)) comparisons:
///
/// 1. A node comes up at its label at most once. Say `v` comes up at `d`. Every entry still
///    queued has a key of `d` or more (the heap gives its least first), and every later
///    lowering is to such a key plus a weight of 0 or more, so to `d` or more; [`Dijkstra::lower`]
///    refuses any value not below the label `d`, so `v` is never queued again. The entries of
///    `v` queued before were pushed at labels strictly above `d` (each push lowers the label
///    strictly), so they come up stale.
///    This needs the starts to be distinct: two equal entries `(d, v)` given to
///    [`Dijkstra::starting`] would both come up at the label. Every caller passes distinct
///    starts (zedc-solvers negsssp.rs `0..n`, zedc-preimage product.rs one start, the tests
///    `[0, 1]`); the others begin with [`Dijkstra::new`] and queue only by
///    [`Dijkstra::lower`], which queues no repeat. With a repeat the count below still holds,
///    since every lowering made while reading `v`'s edges again is refused, the labels being
///    at or below it already.
/// 2. So the caller reads the edges of each node once, and makes at most one lowering per edge
///    read: at most `e` lowerings, each pushing one entry, plus the `s` starts.
/// 3. Each entry is taken at most once, so at most `s + e` are taken, and the heap never holds
///    more than `s + e`. A push of a binary heap costs at most `log2(h)` comparisons and a pop
///    at most `2 log2(h)` at size `h`, so the heap costs O((s + e) log(s + e)); the rest is
///    O(1) per entry and per edge read, plus the labels' cost (O(n) to make a vector of `n`, or
///    a map lookup per lowering).
///
/// With `n` nodes, one start and `e = 4n`, that is O(n log n).
///
/// # Cost, measured
///
/// The bench `dijkstra_takes_n_log_n_time` (PERF-dijkstra-ratio-9, 2026-11-20) runs this
/// search on a random graph of `m` nodes with 4 edges each. Counting instructions retired, `P`
/// entries taken and `W = Σ log2(heap size)` over the takes, the fit
/// `instructions = 39.0·W + 193·P + 227·m` made on `m` = 12,500, 100,000 and 800,000 predicts
/// the instructions at 6,400,000 within 0.001%: no part of the search grows faster than the
/// sum of the heap's `log2(h)`. `P/m` is 1.215, 1.221, 1.219 and 1.219 at the four sizes, and
/// `W/P`, the mean `log2` of the heap's size at a take, is 11.67, 14.69, 17.68 and 20.68: up by
/// 3 = log2(8) at each step, as a heap of a fixed share of the nodes is. The ratios
/// T(8m)/T(m) are 9.163, 8.968 and 8.875. The heap's term alone grows by `8·(L + 3)/L` for a
/// mean log size `L` (9.61 from 100,000, since `L` = 14.69 is below `log2 m` = 16.6, the heap
/// holding a share of the nodes); the linear terms grow by 8, and they hold 40% of the
/// instructions at 100,000, which brings the whole to 8.97, below the goal of 9 and below
/// `8 ln(8m)/ln m` = 9.44.
///
/// An indexed heap with decrease-key would take each node once (`P = m`, not 1.22·m). It was
/// not built: it is a second heap kept beside [`MinHeap`], and for the map labels of
/// zedc-preimage its position store would be a map too, a `log` factor per sift step. Not
/// measured.
#[derive(Clone, Debug)]
pub struct Dijkstra<K, D, L> {
    heap: MinHeap<(D, K)>,
    labels: L,
}

impl<K: Ord + Clone, D: Ord + Clone, L: Labels<K, D>> Dijkstra<K, D, L> {
    /// A search with the labels `labels` and no node queued.
    pub fn new(labels: L) -> Dijkstra<K, D, L> {
        Dijkstra {
            heap: MinHeap::new(),
            labels,
        }
    }

    /// A search with the labels `labels`, each node of `starts` queued at its label, in
    /// O(s) for `s` starts.
    pub fn starting(labels: L, starts: impl IntoIterator<Item = K>) -> Dijkstra<K, D, L> {
        let heap = starts
            .into_iter()
            .filter_map(|k| Some((labels.label(&k)?.clone(), k)))
            .collect();
        Dijkstra { heap, labels }
    }

    /// Lowers the label of `k` to `d` and queues `k` at it, when `k` has no label or a larger
    /// one; whether it fell. A label equal to `d` is kept and nothing is queued, so each node
    /// comes up at most once at each of its labels.
    pub fn lower(&mut self, k: K, d: D) -> bool {
        if self.labels.label(&k).is_some_and(|c| *c <= d) {
            return false;
        }
        self.labels.set_label(k.clone(), d.clone());
        self.heap.push((d, k));
        true
    }

    /// Takes the least queued entry: `Some(Some((d, k)))` when `d` is still the label of `k`,
    /// `Some(None)` when the label has fallen since it was queued, `None` when the queue is
    /// empty. For a caller that counts each entry taken as a unit of work, as a search that
    /// takes turns with another does.
    pub fn pop_entry(&mut self) -> Option<Option<(D, K)>> {
        let (d, k) = self.heap.pop()?;
        Some((self.labels.label(&k) == Some(&d)).then_some((d, k)))
    }

    /// The next node at its label, skipping entries whose label has fallen; `None` when no
    /// node is queued.
    pub fn pop(&mut self) -> Option<(D, K)> {
        loop {
            if let Some(x) = self.pop_entry()? {
                return Some(x);
            }
        }
    }

    /// The labels so far.
    pub fn labels(&self) -> &L {
        &self.labels
    }

    /// The labels, once the search is over.
    pub fn into_labels(self) -> L {
        self.labels
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{Dijkstra, MinHeap, NegativeReducedWeight, reduced};

    /// Least first, ties of key by the second part, as `BinaryHeap<Reverse<_>>` gave.
    #[test]
    fn the_heap_yields_least_first() {
        let mut h: MinHeap<(u32, usize)> = [(3, 0), (1, 5), (1, 2), (2, 9)].into_iter().collect();
        h.push((0, 7));
        assert_eq!(h.peek(), Some(&(0, 7)));
        let all: Vec<_> = std::iter::from_fn(|| h.pop()).collect();
        assert_eq!(all, [(0, 7), (1, 2), (1, 5), (2, 9), (3, 0)]);
        assert!(h.is_empty());
    }

    /// Least distances on a small graph with a potential, against Bellman–Ford on the raw
    /// weights: each node comes up once, at its distance.
    #[test]
    fn dijkstra_on_reduced_weights_gives_least_distances() {
        // Edges with negative weights, and a potential at which each holds.
        let edges: [(usize, usize, i64); 6] = [
            (0, 1, 4),
            (0, 2, 1),
            (2, 1, -2),
            (1, 3, 1),
            (2, 3, 5),
            (3, 4, -3),
        ];
        let p: [i64; 5] = [0, -1, 1, 0, -3];
        let mut d: Dijkstra<usize, i64, BTreeMap<usize, i64>> = Dijkstra::new(BTreeMap::new());
        d.lower(0, 0);
        let mut order = Vec::new();
        while let Some((x, v)) = d.pop() {
            order.push(v);
            for &(a, b, w) in edges.iter().filter(|e| e.0 == v) {
                let r = reduced(p[a] + w - p[b], &0).unwrap();
                d.lower(b, x + r);
            }
        }
        let mut sorted = order.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, [0, 1, 2, 3, 4]);
        let mut bf = [i64::MAX; 5];
        bf[0] = 0;
        for _ in 0..5 {
            for &(a, b, w) in &edges {
                if bf[a] != i64::MAX && bf[a] + w < bf[b] {
                    bf[b] = bf[a] + w;
                }
            }
        }
        let labels = d.into_labels();
        for v in 0..5 {
            assert_eq!(labels[&v] - p[0] + p[v], bf[v], "node {v}");
        }
    }

    /// A reduced weight below zero is refused; zero is not.
    #[test]
    fn a_negative_reduced_weight_is_refused() {
        assert_eq!(reduced(-1i64, &0), Err(NegativeReducedWeight));
        assert_eq!(reduced(0i64, &0), Ok(0));
    }

    /// An entry whose label has fallen since it was queued comes up as stale, and a label
    /// equal to the one held queues nothing.
    #[test]
    fn stale_entries_come_up_as_stale() {
        let mut d: Dijkstra<usize, i64, Vec<i64>> = Dijkstra::starting(vec![5, 7], [0, 1]);
        assert!(d.lower(1, 3));
        assert!(!d.lower(1, 3));
        assert_eq!(d.pop_entry(), Some(Some((3, 1))));
        assert_eq!(d.pop_entry(), Some(Some((5, 0))));
        assert_eq!(d.pop_entry(), Some(None));
        assert_eq!(d.pop_entry(), None);
    }
}
