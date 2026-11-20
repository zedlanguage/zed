//! Kahn's topological order (A. B. Kahn, "Topological sorting of large networks", CACM 5(11),
//! 558-562, 1962, doi:10.1145/368996.369025: place a node that waits on nothing, take its
//! edges away, repeat) with the choice among ready nodes given by the caller, and the search
//! for what a set of roots reaches, with a visited set. Checked 2026-11-20: the DOI on
//! Crossref; the paper not read, the method from memory.
//! `each_ready_set_gives_its_own_topological_order` checks each order is topological and
//! `a_parallel_edge_is_waited_on_twice` the count of edges waited on.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};

/// The nodes ready to be placed in [`kahn`], and which is placed next: the choice that makes
/// one topological order out of the many. [`Vec`] places the last made ready first,
/// [`VecDeque`] the first, and `BinaryHeap<Reverse<usize>>` the least number.
pub trait Ready {
    /// Adds a node that waits on nothing more.
    fn push(&mut self, v: usize);
    /// Takes the node to place next, or `None` when no node is ready.
    fn pop(&mut self) -> Option<usize>;
}

impl Ready for Vec<usize> {
    fn push(&mut self, v: usize) {
        Vec::push(self, v);
    }
    fn pop(&mut self) -> Option<usize> {
        Vec::pop(self)
    }
}

impl Ready for VecDeque<usize> {
    fn push(&mut self, v: usize) {
        self.push_back(v);
    }
    fn pop(&mut self) -> Option<usize> {
        self.pop_front()
    }
}

impl Ready for BinaryHeap<Reverse<usize>> {
    fn push(&mut self, v: usize) {
        BinaryHeap::push(self, Reverse(v));
    }
    fn pop(&mut self) -> Option<usize> {
        BinaryHeap::pop(self).map(|Reverse(v)| v)
    }
}

/// The nodes that wait on nothing, by number: where [`kahn`] starts when every such node is a
/// start.
pub fn sources(waits: &[usize]) -> impl Iterator<Item = usize> + '_ {
    (0..waits.len()).filter(|&v| waits[v] == 0)
}

/// Kahn's algorithm: takes the nodes of `ready` one at a time in its order, calls `placed`
/// with each, and then, for each edge `kids(v)` gives out of it, lowers by one the number of
/// edges its head still `waits` on, making the head ready when that reaches 0. The caller
/// fills `waits` (one count per edge into a node, as `kids` gives them) and puts the starting
/// nodes in `ready`, often [`sources`]. Returns the number of nodes placed; on a graph with a
/// cycle the nodes on it and after it are never placed, and keep a count above 0 in `waits`.
// Complexity tradeoff: each node placed once and each edge out of it read once, O(n + e) and
// the cost of `ready`'s operations (O(1) for a stack or queue, O(log n) for a heap). The naive
// alternative, scanning for a node with no edge left in, is O(n^2). Taking the edges out of a
// node (`kids`), not into it, is what lets a count per node replace the lists of edges in.
pub fn kahn<I: IntoIterator<Item = usize>>(
    waits: &mut [usize],
    ready: &mut impl Ready,
    mut kids: impl FnMut(usize) -> I,
    mut placed: impl FnMut(usize),
) -> usize {
    let mut count = 0;
    while let Some(v) = ready.pop() {
        count += 1;
        placed(v);
        for c in kids(v) {
            waits[c] -= 1;
            if waits[c] == 0 {
                ready.push(c);
            }
        }
    }
    count
}

/// Searches from `roots` along `kids`, the visited set kept by the caller through `first`,
/// which adds a node to it and says whether it was new: each root and each node `kids` gives
/// is passed to `first`, and the new ones are searched, last found first. When the search
/// ends, the visited set holds exactly what the roots reach.
// Complexity tradeoff: each node reached is searched once, so the cost is O(r + e) calls of
// `first` for the r nodes reached and the e edges out of them, and of `kids` once per node;
// without the visited set (P207) a node reached by several paths is searched once per path,
// exponential on a DAG of shared parts. The set is the caller's, so it may be a bit vector, a
// hash set or an ordered set, as the node's keys suit, and may note the nodes met twice.
pub fn reach<K, I: IntoIterator<Item = K>>(
    roots: impl IntoIterator<Item = K>,
    mut first: impl FnMut(&K) -> bool,
    mut kids: impl FnMut(&K) -> I,
) {
    let mut todo: Vec<K> = roots.into_iter().filter(|k| first(k)).collect();
    while let Some(k) = todo.pop() {
        for c in kids(&k) {
            if first(&c) {
                todo.push(c);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Ready, kahn, reach, sources};
    use std::cmp::Reverse;
    use std::collections::{BinaryHeap, VecDeque};

    /// Kahn's order of the graph `kids` over `0..n` with `ready`, and whether every node is
    /// placed.
    fn order(kids: &[Vec<usize>], mut ready: impl Ready) -> (Vec<usize>, bool) {
        let mut waits = vec![0; kids.len()];
        for ks in kids {
            for &c in ks {
                waits[c] += 1;
            }
        }
        for v in sources(&waits).collect::<Vec<_>>() {
            ready.push(v);
        }
        let mut out = Vec::new();
        let placed = kahn(&mut waits, &mut ready, |v| kids[v].clone(), |v| out.push(v));
        assert_eq!(placed, out.len());
        (out, placed == kids.len())
    }

    #[test]
    fn each_ready_set_gives_its_own_topological_order() {
        // 0 -> 2, 1 -> 2, 2 -> 3, 1 -> 4: the sources 0 and 1 are ready first.
        let kids = vec![vec![2], vec![2, 4], vec![3], vec![], vec![]];
        assert_eq!(order(&kids, Vec::new()), (vec![1, 4, 0, 2, 3], true));
        assert_eq!(order(&kids, VecDeque::new()), (vec![0, 1, 2, 4, 3], true));
        assert_eq!(
            order(&kids, BinaryHeap::<Reverse<usize>>::new()),
            (vec![0, 1, 2, 3, 4], true)
        );
        // A cycle 1 -> 2 -> 1 leaves 1, 2 and what follows them unplaced.
        let kids = vec![vec![1], vec![2], vec![1, 3], vec![]];
        assert_eq!(order(&kids, Vec::new()), (vec![0], false));
    }

    #[test]
    fn a_parallel_edge_is_waited_on_twice() {
        let kids = vec![vec![1, 1], vec![]];
        assert_eq!(order(&kids, Vec::new()), (vec![0, 1], true));
    }

    #[test]
    fn reach_visits_each_node_once_and_finds_what_the_roots_reach() {
        // A diamond reached by two paths, a node only a cycle reaches, and one not reached.
        let kids = [vec![1, 2], vec![3], vec![3], vec![4], vec![3], vec![0]];
        let mut seen = vec![false; kids.len()];
        let mut met = vec![0; kids.len()];
        reach(
            [0, 0],
            |&v| {
                met[v] += 1;
                !std::mem::replace(&mut seen[v], true)
            },
            |&v| kids[v].clone(),
        );
        assert_eq!(seen, [true, true, true, true, true, false]);
        // Met once per root or edge into it from a node reached; searched once.
        assert_eq!(met, [2, 1, 1, 3, 1, 0]);
    }
}
