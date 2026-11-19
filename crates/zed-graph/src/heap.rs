//! A heap that yields its least element first, and the search of Dijkstra built on it.
//!
//! [`MinHeap`] is `BinaryHeap<Reverse<T>>` under one name, so the workspace's many least-first
//! queues share one type and none of them writes `Reverse` at each push and pop. Its order is
//! that of `T`: a queue of `(key, node)` pairs breaks ties of key by node, as every caller's
//! `BinaryHeap<Reverse<(key, node)>>` did.
//!
//! [`Dijkstra`] is the lazy-deletion form of Dijkstra's search (E. W. Dijkstra, "A note on two
//! problems in connexion with graphs", Numerische Mathematik 1, 269-271, 1959): a label per
//! node, lowered only when a strictly smaller distance is found, each lowering pushing a new
//! entry, and an entry skipped when it comes up if its node's label has fallen since. With
//! every weight 0 or more, the first entry of a node that comes up at its label is its least
//! distance, and it comes up once, since a label never falls to the value it already has:
//! O(m log m) for m lowerings, each one a heap push. A potential `p` makes the reduced weight
//! of an edge `x → y` of weight `w` equal to `p(x) + w - p(y)`; [`reduced`] checks that it is
//! 0 or more, which is what makes the search exact on graphs with negative weights
//! (D. B. Johnson, "Efficient algorithms for shortest paths in sparse networks", JACM 24(1),
//! 1-13, 1977).

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
