//! Kahn's topological order (A. B. Kahn, "Topological sorting of large networks", CACM 5(11),
//! 558-562, 1962, doi:10.1145/368996.369025: place a node that waits on nothing, take its
//! edges away, repeat) with the choice among ready nodes given by the caller, and the search
//! for what a set of roots reaches, with a visited set. Read 2026-11-21 (PDF, OpenAlex's
//! cached copy, verification only; title and author checked on the copy). P. 559: "The basic
//! procedure is to establish a list of all unique events with a count of the number of
//! immediate predecessors of each event"; p. 560 (Figure 3): events whose count is zero get
//! the next serial numbers, "their successors now have one less predecessor outstanding;
//! therefore, the count for these successors can be decremented by one", and when a pass
//! ends with no new zero, either every event is numbered or "there is an illegal loop in the
//! network", told apart "by comparing the number of events" numbered with the total. The
//! order is topological because a node is numbered only once its count, the number of its
//! predecessors not yet numbered, is zero. Departure: the paper finds the ready events by
//! scanning the whole count list again on each pass, at most M + 1 passes for M "the maximum
//! number of reversals on any one path" (p. 559), so O(M · E) for E events (p. 561); here a
//! node is put in the caller's [`Ready`] set when its count reaches zero, so each node and
//! edge is handled once, O(V + E) plus the set's own cost.
//! `each_ready_set_gives_its_own_topological_order` checks each order is topological and
//! `a_parallel_edge_is_waited_on_twice` the count of edges waited on; neither measures the
//! time.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};
use std::convert::Infallible;
use std::ops::ControlFlow;

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
    first: impl FnMut(&K) -> bool,
    mut kids: impl FnMut(&K) -> I,
) {
    if let Some(never) = reach_until(roots, first, |k| {
        ControlFlow::<Infallible, I>::Continue(kids(k))
    }) {
        match never {}
    }
}

/// [`reach`] that may stop early: each node searched, in the same order, is passed to `visit`,
/// which either gives its kids (`Continue`) or ends the whole search with a value
/// (`Break`), returned as `Some`. `None` when the search ran to the end; then the visited set
/// holds exactly what the roots reach. After a `Break` it holds the nodes searched and the
/// kids of those searched that `first` was given, some of them not yet searched.
// Complexity tradeoff: as [`reach`], O(r + e) calls of `first` and one of `visit` per node
// searched, for the r nodes and e edges up to the stop, so a search that stops at once costs
// O(roots). [`reach`] is this with a `visit` that never stops; `Infallible` makes that a type
// with no `Break`, so the compiler drops the test and the two cost the same.
pub fn reach_until<K, I: IntoIterator<Item = K>, B>(
    roots: impl IntoIterator<Item = K>,
    mut first: impl FnMut(&K) -> bool,
    mut visit: impl FnMut(&K) -> ControlFlow<B, I>,
) -> Option<B> {
    let mut todo: Vec<K> = roots.into_iter().filter(|k| first(k)).collect();
    while let Some(k) = todo.pop() {
        match visit(&k) {
            ControlFlow::Continue(kids) => {
                for c in kids {
                    if first(&c) {
                        todo.push(c);
                    }
                }
            }
            ControlFlow::Break(b) => return Some(b),
        }
    }
    None
}

/// Visits in post-order what `roots` reach along the edges `enter` gives, on an explicit stack
/// in place of recursion, so a long chain of nodes cannot overflow the thread's stack. When a
/// node comes to the top, `enter(ctx, v, kids)` says whether to visit it, false when the caller
/// has visited it already (its memo), and if so pushes the nodes below it to `kids`; they are
/// visited in that order, and then `leave(ctx, v)`. So `leave` meets each node after every
/// node below it, and a node that two parents push is entered once if `leave` marks it
/// visited. The graph must be acyclic: a node met again below itself is entered again. `ctx`
/// is the state both read and change, such as the memo.
// Complexity tradeoff: each node visited is entered and left once, and each edge out of it
// is pushed once, O(n + e) and heap space for the edges waiting; a node pushed by several
// parents costs one `enter` per push. The naive form, a recursive call per edge, is the same
// order of time but takes a stack frame per level of the graph, and so overflowed on chains
// some thousands deep (FAIL-l0126-stack-overflow-after-d).
pub fn post_order<C, K>(
    ctx: &mut C,
    roots: impl IntoIterator<Item = K>,
    mut enter: impl FnMut(&mut C, &K, &mut Vec<K>) -> bool,
    mut leave: impl FnMut(&mut C, K),
) {
    let mut stack: Vec<(K, bool)> = roots.into_iter().map(|k| (k, false)).collect();
    stack.reverse();
    let mut kids = Vec::new();
    while let Some((k, below_left)) = stack.pop() {
        if below_left {
            leave(ctx, k);
        } else if enter(ctx, &k, &mut kids) {
            stack.push((k, true));
            stack.extend(kids.drain(..).rev().map(|c| (c, false)));
        } else {
            // A node not visited has no edges to follow, whatever `enter` pushed.
            kids.clear();
        }
    }
}

/// Makes each node of `roots` and each node it needs, each after those it needs, on an
/// explicit stack in place of recursion. `make(v, needs)` either makes `v` and returns true,
/// or pushes to `needs` nodes not yet made that it needs and returns false; it is called for
/// `v` again once those are made, the last pushed first. A node made already should return
/// true at once. For when the nodes a node needs are found only by trying to make it, as by
/// a walk that reads the results of those below it. The nodes needed must form an acyclic
/// graph, or the loop does not end.
// Complexity tradeoff: a `make` that pushes every node it lacks in one call is called at most
// twice a node, once to find what it lacks and once to make it, so the cost is at most twice
// that of making each node once; the alternative, finding the nodes below first in a
// separate walk, duplicates the walk that finds them in each caller.
pub fn make_after_needs<K>(
    roots: impl IntoIterator<Item = K>,
    mut make: impl FnMut(&K, &mut Vec<K>) -> bool,
) {
    let mut stack: Vec<K> = roots.into_iter().collect();
    let mut needs = Vec::new();
    while let Some(top) = stack.last() {
        if make(top, &mut needs) {
            stack.pop();
            // A node made needs nothing more, whatever `make` pushed.
            needs.clear();
        } else {
            stack.append(&mut needs);
        }
    }
}

/// The cycle that the walk from `start` along `next` runs into, on nodes `0..n` each with one
/// successor `next(v) < n`: the nodes from the first one met twice, in order along the walk,
/// that node first. The walk among `n` nodes meets one twice within `n + 1` steps, so it ends.
/// Each node walked keeps its place on the walk in a dense array, `O(n)` for the array and
/// `O(k)` for the `k` nodes walked; a map keyed by node would cost `O(k log k)` and no array,
/// the better choice only for a walk much shorter than `n`, which the callers do not have
/// (the one caller, zedc-resolve topo.rs, has done `O(n log n)` work before).
pub fn functional_cycle(
    n: usize,
    start: usize,
    mut next: impl FnMut(usize) -> usize,
) -> Vec<usize> {
    let mut at = vec![usize::MAX; n];
    let mut path = Vec::new();
    let mut v = start;
    while at[v] == usize::MAX {
        at[v] = path.len();
        path.push(v);
        v = next(v);
    }
    path.split_off(at[v])
}

#[cfg(test)]
mod tests {
    use super::{
        Ready, functional_cycle, kahn, make_after_needs, post_order, reach, reach_until, sources,
    };
    use std::cmp::Reverse;
    use std::collections::{BinaryHeap, VecDeque};
    use std::ops::ControlFlow;

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

    /// `reach_until` stops at the first node `visit` breaks on, in the order `reach` searches;
    /// with no break it finds what `reach` finds.
    #[test]
    fn reach_until_stops_at_the_first_node_that_breaks() {
        let kids = [vec![1, 2], vec![3], vec![3], vec![4], vec![3], vec![0]];
        let mut order = Vec::new();
        let mut seen = vec![false; kids.len()];
        let hit = reach_until(
            [0],
            |&v| !std::mem::replace(&mut seen[v], true),
            |&v| {
                order.push(v);
                if v == 3 {
                    ControlFlow::Break(v * 10)
                } else {
                    ControlFlow::Continue(kids[v].clone())
                }
            },
        );
        assert_eq!(hit, Some(30));
        // Last found first: 0, then 2 (pushed after 1), then 3.
        assert_eq!(order, [0, 2, 3]);
        // No root is new: nothing is searched.
        let none: Option<()> = reach_until(
            [0],
            |_| false,
            |_| ControlFlow::Continue(Vec::<usize>::new()),
        );
        assert_eq!(none, None);
    }

    /// On random graphs, `reach_until` with no break visits what the inline stack-and-set
    /// search the callers wrote before visits (kept as the oracle), in the same order, and
    /// breaking at a node gives the prefix of that order up to the node.
    #[test]
    fn reach_until_agrees_with_the_inline_search_it_replaced() {
        let (mut rng, seed) = crate::seed::Rng::fresh("reach_until_agrees_with_the_inline_search");
        for _ in 0..500 {
            let n = 1 + rng.below(10);
            let kids: Vec<Vec<usize>> = (0..n)
                .map(|_| (0..rng.below(4)).map(|_| rng.below(n)).collect())
                .collect();
            let roots: Vec<usize> = (0..1 + rng.below(3)).map(|_| rng.below(n)).collect();
            // The oracle: the loop as written inline at each site before.
            let mut want = Vec::new();
            let mut seen = vec![false; n];
            let mut stack: Vec<usize> = Vec::new();
            for &r in &roots {
                if !seen[r] {
                    seen[r] = true;
                    stack.push(r);
                }
            }
            while let Some(v) = stack.pop() {
                want.push(v);
                for &c in &kids[v] {
                    if !seen[c] {
                        seen[c] = true;
                        stack.push(c);
                    }
                }
            }
            let mut got = Vec::new();
            let mut seen2 = vec![false; n];
            let stop = rng.below(n + 1);
            let hit = reach_until(
                roots.iter().copied(),
                |&v| !std::mem::replace(&mut seen2[v], true),
                |&v| {
                    got.push(v);
                    if v == stop {
                        ControlFlow::Break(v)
                    } else {
                        ControlFlow::Continue(kids[v].iter().copied())
                    }
                },
            );
            match want.iter().position(|&v| v == stop) {
                Some(at) => {
                    assert_eq!(hit, Some(stop), "seed {seed}");
                    assert_eq!(got, want[..=at], "seed {seed}");
                }
                None => {
                    assert_eq!(hit, None, "seed {seed}");
                    assert_eq!(got, want, "seed {seed}");
                    assert_eq!(seen2, seen, "seed {seed}");
                }
            }
        }
    }

    #[test]
    fn post_order_leaves_each_node_once_after_those_below_it_in_the_order_given() {
        // A diamond 0 -> {1, 2} -> 3, and 2 -> 4; node 5 is not reached.
        let kids = [vec![1, 2], vec![3], vec![3, 4], vec![], vec![], vec![]];
        let mut left: Vec<usize> = Vec::new();
        post_order(
            &mut left,
            [0, 0],
            |left, &v, out| {
                let new = !left.contains(&v);
                if new {
                    out.extend(&kids[v]);
                }
                new
            },
            |left, v| left.push(v),
        );
        assert_eq!(left, [3, 1, 4, 2, 0]);
    }

    #[test]
    fn make_after_needs_makes_each_node_after_those_it_needs_and_once() {
        // The same diamond: a node is made once every node below it is.
        let kids = [vec![1, 2], vec![3], vec![3, 4], vec![], vec![], vec![]];
        let mut made: Vec<usize> = Vec::new();
        let mut calls = 0;
        make_after_needs([0], |&v, needs| {
            calls += 1;
            if made.contains(&v) {
                return true;
            }
            needs.extend(kids[v].iter().filter(|c| !made.contains(c)));
            if needs.is_empty() {
                made.push(v);
            }
            needs.is_empty()
        });
        assert_eq!(made, [4, 3, 2, 1, 0]);
        // Twice for 0 and 2, which lacked nodes when first tried; once for 1, whose 3 was made
        // by then, and for the leaves 3 and 4.
        assert_eq!(calls, 7);
    }

    #[test]
    fn both_walks_go_down_a_chain_a_million_long_on_a_small_stack() {
        const N: usize = 1_000_000;
        std::thread::Builder::new()
            .stack_size(64 << 10)
            .spawn(|| {
                let mut left = vec![false; N];
                let mut count = 0;
                post_order(
                    &mut left,
                    [0],
                    |left, &v, out| {
                        if v + 1 < N {
                            out.push(v + 1);
                        }
                        !left[v]
                    },
                    |left, v| {
                        left[v] = true;
                        count += 1;
                    },
                );
                assert_eq!(count, N);
                let mut made = vec![false; N];
                make_after_needs([0], |&v, needs| {
                    if v + 1 < N && !made[v + 1] {
                        needs.push(v + 1);
                        return false;
                    }
                    made[v] = true;
                    true
                });
                assert!(made.iter().all(|&m| m));
            })
            .expect("the thread starts")
            .join()
            .expect("the walks end");
    }

    #[test]
    fn functional_cycle_gives_the_cycle_from_its_first_node_met_twice() {
        // 0 -> 1 -> 2 -> 3 -> 1: the tail 0 is left out, the cycle starts at 1.
        assert_eq!(functional_cycle(4, 0, |v| [1, 2, 3, 1][v]), vec![1, 2, 3]);
        // A start on its cycle, and a node that is its own successor.
        assert_eq!(functional_cycle(4, 2, |v| [1, 2, 3, 1][v]), vec![2, 3, 1]);
        assert_eq!(functional_cycle(3, 1, |v| [1, 1, 0][v]), vec![1]);
    }

    /// On random functional graphs, `functional_cycle` gives what the `BTreeMap` walk of
    /// zedc-resolve topo.rs it replaced gives (kept here as the oracle).
    #[test]
    fn functional_cycle_agrees_with_the_map_walk_it_replaced() {
        let (mut rng, seed) = crate::seed::Rng::fresh("functional_cycle_agrees_with_the_map_walk");
        for _ in 0..2000 {
            let n = 1 + rng.below(12);
            let next: Vec<usize> = (0..n).map(|_| rng.below(n)).collect();
            let start = rng.below(n);
            let mut seen = std::collections::BTreeMap::new();
            let mut path = Vec::new();
            let mut i = start;
            while !seen.contains_key(&i) {
                seen.insert(i, path.len());
                path.push(i);
                i = next[i];
            }
            let want = path.split_off(seen[&i]);
            assert_eq!(
                functional_cycle(n, start, |v| next[v]),
                want,
                "seed {seed}: next {next:?}, start {start}"
            );
        }
    }
}
