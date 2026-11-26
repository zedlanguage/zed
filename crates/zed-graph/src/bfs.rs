//! A shortest path by breadth-first search, with its scratch kept across searches.
//!
//! The reports of a cycle (import cycles in zedc unit.rs and zed-tools imports.rs, grammar
//! cycles in zed-tools llp.rs, loops of limits in zedc-preimage loops.rs) each searched
//! breadth first from a node, inside its strongly connected component, for the first edge to a
//! target, often the start itself, and walked the parents back. [`BfsPaths`] is that search
//! once. The breadth-first search for a shortest path is credited to E. F. Moore, "The
//! shortest path through a maze", 1959, not read (zed-graph worklist.rs lists where it was
//! looked for); the proof below stands without it.
//!
//! Why the path found is a shortest one, and of those the one the edge order picks first.
//! Nodes are met in passes: pass 0 is `s`, pass `k + 1` the nodes first met on the edges of
//! pass `k`, and the queue holds the passes in order. By induction on `k`, pass `k` holds
//! exactly the nodes at distance `k` from `s` by the edges `next` gives: a node at distance
//! `k + 1` has an edge from one at distance `k`, which is in pass `k`, so it is met by pass
//! `k + 1`; it is not met earlier, since that would give it a shorter path. The first edge to a
//! target leaves the earliest pass that has one, so the path has the least number of edges,
//! and within passes the edges are taken in queue order and each node's edges in the order
//! `next` gives, which fixes which shortest path is found (and so the text of the reports
//! built from it). Each node met records the node and edge it was first met by, so walking
//! those back from the target gives the path. Tests: `bfs_paths_finds_a_shortest_path` and
//! `bfs_paths_agrees_with_the_map_search_it_replaced` below.

/// The scratch of breadth-first searches over nodes `0..n`: for each node met by the search
/// running, whether it was met and the node and edge it was first met by, and the nodes met in
/// order, which is also the queue. A search clears only the nodes it met, so it costs the part
/// of the graph it reaches, not `n`; the arrays are made once, `O(n)`.
pub struct BfsPaths<E> {
    met: Vec<bool>,
    by: Vec<Option<(usize, E)>>,
    queue: Vec<usize>,
}

impl<E: Copy> BfsPaths<E> {
    /// Scratch for searches over nodes `0..n`.
    pub fn new(n: usize) -> Self {
        BfsPaths {
            met: vec![false; n],
            by: vec![None; n],
            queue: Vec::new(),
        }
    }

    /// A shortest path from `s` along the edges `next` gives, each a head and a payload (such
    /// as the edge's place in the text), to the first head `goal` accepts: its edges in order,
    /// each the node it leaves, its payload and its head; `None` when no edge reaches a goal.
    /// `goal` is asked of each edge's head before whether it was met, so with `goal(s)` true
    /// the path is a shortest cycle through `s`; a goal is not asked of `s` itself. `next`
    /// filters the edges (to a component, or by a test of the edge), and its order picks among
    /// the shortest paths (module doc). `O(k + e)` for the `k` nodes met and the `e` edges
    /// taken from them.
    pub fn path<I: IntoIterator<Item = (usize, E)>>(
        &mut self,
        s: usize,
        mut next: impl FnMut(usize) -> I,
        mut goal: impl FnMut(usize) -> bool,
    ) -> Option<Vec<(usize, E, usize)>> {
        self.met[s] = true;
        self.queue.push(s);
        let mut head = 0;
        let mut end = None;
        'search: while let Some(&u) = self.queue.get(head) {
            head += 1;
            for (v, e) in next(u) {
                if goal(v) {
                    end = Some((u, e, v));
                    break 'search;
                }
                if !self.met[v] {
                    self.met[v] = true;
                    self.by[v] = Some((u, e));
                    self.queue.push(v);
                }
            }
        }
        let path = end.map(|last| {
            let mut steps = vec![last];
            let mut x = last.0;
            while let Some((from, e)) = self.by[x] {
                steps.push((from, e, x));
                x = from;
            }
            steps.reverse();
            steps
        });
        for v in self.queue.drain(..) {
            self.met[v] = false;
            self.by[v] = None;
        }
        path
    }
}

#[cfg(test)]
mod tests {
    use super::BfsPaths;
    use std::collections::{BTreeMap, VecDeque};

    #[test]
    fn bfs_paths_finds_a_shortest_path() {
        // 0 -> 1 -> 2 -> 3, and 0 -> 4 -> 3: the shorter way to 3 is through 4.
        let kids = [vec![1, 4], vec![2], vec![3], vec![0], vec![3]];
        let mut b = BfsPaths::new(5);
        let next = |u: usize| kids[u].iter().map(|&v| (v, ()));
        let p = b.path(0, next, |v| v == 3).expect("3 is reached");
        assert_eq!(p, vec![(0, (), 4), (4, (), 3)]);
        // A shortest cycle through 0, and the scratch cleared for the next search.
        let c = b.path(0, next, |v| v == 0).expect("0 is on a cycle");
        assert_eq!(c, vec![(0, (), 4), (4, (), 3), (3, (), 0)]);
        // A self-loop closes a cycle of one edge; a goal never reached gives None.
        let mut b = BfsPaths::new(2);
        assert_eq!(
            b.path(0, |_| [(0, 'a')], |v| v == 0),
            Some(vec![(0, 'a', 0)])
        );
        assert_eq!(b.path(0, |_| [(0, 'a')], |v| v == 1), None);
    }

    /// On random graphs, `path` gives the path the `BTreeMap` search of zedc-preimage
    /// loops.rs `cycle_at` it replaced gives (kept here as the oracle), for a target equal to
    /// the start and for another, with one scratch reused across all the searches.
    #[test]
    fn bfs_paths_agrees_with_the_map_search_it_replaced() {
        let (mut rng, seed) = crate::seed::Rng::fresh("bfs_paths_agrees_with_the_map_search");
        let mut b = BfsPaths::new(12);
        for _ in 0..3000 {
            let n = 1 + rng.below(12);
            let kids: Vec<Vec<usize>> = (0..n)
                .map(|_| (0..rng.below(4)).map(|_| rng.below(n)).collect())
                .collect();
            let (s, t) = (rng.below(n), rng.below(n));
            // The oracle: the search as written in loops.rs, with the edge to the target
            // checked before the visited test, ending at the first edge into the target.
            let mut prev: BTreeMap<usize, usize> = BTreeMap::new();
            let mut q = VecDeque::from([s]);
            let mut want = None;
            'search: while let Some(u) = q.pop_front() {
                for &w in &kids[u] {
                    if w == t {
                        let mut p = vec![(u, w)];
                        let mut x = u;
                        while x != s {
                            p.push((prev[&x], x));
                            x = prev[&x];
                        }
                        p.reverse();
                        want = Some(p);
                        break 'search;
                    }
                    if w == s || prev.contains_key(&w) {
                        continue;
                    }
                    prev.insert(w, u);
                    q.push_back(w);
                }
            }
            let got = b.path(s, |u| kids[u].iter().map(|&v| (v, ())), |v| v == t);
            let got = got.map(|p| p.into_iter().map(|(u, (), v)| (u, v)).collect::<Vec<_>>());
            assert_eq!(got, want, "seed {seed}: kids {kids:?}, from {s} to {t}");
        }
    }
}
