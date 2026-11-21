//! Graph algorithms shared by every crate of the workspace. It depends on no other crate, so
//! zed-kernel, the lowest of the others, can use it too, and each search below is written once.
//!
//! [`Search`] finds the strongly connected components of a directed graph (R. Tarjan,
//! "Depth-First Search and Linear Graph Algorithms", SIAM Journal on Computing 1(2), 146-160,
//! 1972, doi:10.1137/0201010), on an explicit stack in place of recursion, so a long chain of
//! nodes cannot overflow the thread's stack. Its caller gives the edges one at a time
//! ([`Walk`]), so the nodes may be found and numbered as the search meets them, and one search
//! may be run again from new roots after its graph has grown. Each node and each edge is read
//! once: O(n + e) time and O(n) space beside the graph. [`tarjan`] is the search over a graph
//! whose nodes are `0..n` and whose edges are lists, and [`components`] and [`on_cycle`] are
//! its two common uses. The paper keeps the nodes of the path on a stack with a low link each
//! and completes a component when a node's low link is its own number. Read 2026-11-21 (PDF,
//! LibGen, verification only; title and author checked on the copy). Sec. 4, p. 156: LOWLINK
//! (v) "is the smallest vertex which is in the same component as v and is reachable by
//! traversing zero or more tree arcs followed by at most one frond or cross-link"; Lemma 12:
//! "v is the root of some strongly connected component of G if and only if LOWLINK (v) = v";
//! the component is then the nodes on the stack from `v` up, since by Corollary 11 a
//! component's nodes form a subtree of the search forest rooted at its root. Theorem 13
//! (p. 157): O(V + E) time and space; Theorem 14 (p. 158): the LOWLINK values computed are
//! correct, by induction over the search. In `tests.rs`,
//! `components_are_the_classes_of_mutual_reach_numbered_in_reverse_topological_order` checks
//! the components against mutual reach on random graphs, and `a_long_chain_needs_no_deep_stack`
//! the explicit stack.
//!
//! It also holds the structures that searches share, each written once: [`MinHeap`], a heap
//! that gives its least item first, and [`Dijkstra`], the search for least distances on it
//! ([`heap`]); [`Worklist`], a queue or stack that holds each item at most once ([`worklist`]);
//! [`IdSource`], a counter that draws numbers once each across threads ([`ids`]);
//! [`BitSet`], a set of small numbers kept one bit each ([`bitset`]); and [`UnionFind`], the classes
//! of elements joined in pairs, with the compression and linking its caller chooses, a value per
//! class and an offset per edge ([`union_find`]).

use std::marker::PhantomData;

/// The edges of a graph as [`Search::run`] reads them, and what it does with each component.
pub trait Walk {
    /// Where the search is in the edges of a node on its path; it starts at
    /// `Default::default()` when the search reaches the node, and only [`Walk::next`] changes it.
    type At: Default;
    /// The node that the next edge out of `v` goes to, `at` saying where the edges read so far
    /// end, or `None` when every edge of `v` is read. A node met for the first time may be
    /// numbered here: the search keeps one word per number up to the largest it has met, so the
    /// numbers should be dense, as `0, 1, 2, …` in the order met are. An edge the walk leaves
    /// out, as one to a node whose component an earlier search found, is simply not given.
    fn next(&mut self, v: usize, at: &mut Self::At) -> Option<usize>;
    /// A strongly connected component, found once every component it reaches is found, so the
    /// components come in a reverse topological order. Its members are in the order the search
    /// reached them, so the first is the one it reached the component by; `found` may reorder
    /// them. `from` is the node the search reached that first member from, `None` for a root.
    fn found(&mut self, members: &mut [usize], from: Option<usize>);
}

/// No number yet: a node the search has not reached.
const NEW: usize = usize::MAX;
/// A node whose component is found.
const DONE: usize = usize::MAX - 1;

/// One node on the search's path.
struct Frame<A> {
    v: usize,
    /// Its place on the search's stack.
    first: usize,
    /// The least number of a node on the stack that it reaches by the edges read so far
    /// (Tarjan's low link).
    low: usize,
    /// Where it is in its edges ([`Walk::At`]).
    at: A,
}

/// A depth-first search for strongly connected components that can be run more than once: a
/// node whose component one run found is passed over by every later run, as a node of a
/// component found earlier in the same run is, so a caller whose graph grows between runs
/// (new nodes, with edges to old ones, but no new edge out of an old node) searches only what
/// is new.
// Complexity tradeoff: the low link lives on the path, not per node, since only the node whose
// edges are being read and the node it was reached from ever change theirs; with a node's place
// on the stack kept on the path too, a node costs one word (`index`), where the usual form keeps
// three (number, low link, on-stack flag or place). Each node is entered once and each edge given
// once, O(n + e) over every run together; `index` grows to the largest number met, so a caller
// numbering nodes as met pays O(n) for it.
pub struct Search<A> {
    /// Per node: [`NEW`]; its number in the order reached while its component is open; then
    /// [`DONE`].
    index: Vec<usize>,
    /// The nodes reached whose component is not yet found.
    stack: Vec<usize>,
    /// The path of the search, each node with where it is in its edges.
    path: Vec<Frame<A>>,
    /// The number of the next node reached.
    count: usize,
}

impl<A: Default> Default for Search<A> {
    fn default() -> Self {
        Search::new()
    }
}

impl<A: Default> Search<A> {
    /// A search that has reached no node.
    pub fn new() -> Self {
        Search::with_capacity(0)
    }

    /// A search with room for the nodes `0..n`.
    pub fn with_capacity(n: usize) -> Self {
        Search {
            index: vec![NEW; n],
            stack: Vec::new(),
            path: Vec::new(),
            count: 0,
        }
    }

    fn state(&self, v: usize) -> usize {
        self.index.get(v).copied().unwrap_or(NEW)
    }

    fn enter(&mut self, v: usize) {
        if v >= self.index.len() {
            self.index.resize(v + 1, NEW);
        }
        let i = self.count;
        self.count += 1;
        self.index[v] = i;
        self.path.push(Frame {
            v,
            first: self.stack.len(),
            low: i,
            at: A::default(),
        });
        self.stack.push(v);
    }

    /// Searches from each of `roots` in turn that no run has reached, and only the nodes
    /// reached from them, calling [`Walk::found`] with each component.
    pub fn run<W: Walk<At = A>>(&mut self, walk: &mut W, roots: impl IntoIterator<Item = usize>) {
        for root in roots {
            if self.state(root) != NEW {
                continue;
            }
            self.enter(root);
            while let Some(top) = self.path.last_mut() {
                if let Some(w) = walk.next(top.v, &mut top.at) {
                    match self.state(w) {
                        NEW => self.enter(w),
                        DONE => {}
                        // On the stack: `w` reaches the node being read, so they are one
                        // component.
                        i => {
                            let top = self.path.last_mut().expect("the node being read");
                            top.low = top.low.min(i);
                        }
                    }
                    continue;
                }
                // Every edge of `v` is read: its low link passes to the node the search came
                // from.
                let Frame { v, first, low, .. } = self.path.pop().expect("the node being read");
                let from = self.path.last_mut().map(|u| {
                    u.low = u.low.min(low);
                    u.v
                });
                if low == self.index[v] {
                    for &w in &self.stack[first..] {
                        self.index[w] = DONE;
                    }
                    walk.found(&mut self.stack[first..], from);
                    self.stack.truncate(first);
                }
            }
        }
    }
}

/// Calls `found` with the members of each strongly connected component of the graph whose
/// nodes are `0..n`, in the order Tarjan's search completes them: a component is completed
/// after every component it reaches, so the order is a reverse topological order of the
/// components.
///
/// The search starts from each of `roots` in turn not yet reached, and only the nodes reached
/// from them are searched. `out(v)` gives the edges out of `v`, and `head` the node each edge
/// goes to, or `None` for an edge the search leaves out. The members are given in the order
/// the search reached them, so the first is the one it reached the component by;
/// `found` may reorder them.
// Complexity tradeoff: every crate once had its own copy of this search (DEDUP-tarjan); a copy
// per caller let each pick its own edge type and order of members, which the closures `out` and
// `head` and the slice given to `found` now give at the cost of one indirect call per edge, which
// each closure being inlined at its call site removes. A component's members are a slice of the
// search's stack, taken in O(size) with no list built per component; a caller that wants the
// order of the earlier copies that popped them one by one reads the slice backward.
pub fn tarjan<'g, E: 'g>(
    n: usize,
    roots: impl IntoIterator<Item = usize>,
    out: impl Fn(usize) -> &'g [E],
    head: impl FnMut(&E) -> Option<usize>,
    found: impl FnMut(&mut [usize]),
) {
    let mut lists = Lists {
        out,
        head,
        found,
        edge: PhantomData,
    };
    Search::with_capacity(n).run(&mut lists, roots);
}

/// The graph [`tarjan`] searches: edges given as a list per node.
struct Lists<'g, E, O, H, F> {
    out: O,
    head: H,
    found: F,
    edge: PhantomData<&'g E>,
}

impl<'g, E: 'g, O, H, F> Walk for Lists<'g, E, O, H, F>
where
    O: Fn(usize) -> &'g [E],
    H: FnMut(&E) -> Option<usize>,
    F: FnMut(&mut [usize]),
{
    /// The place in `out(v)` of the next edge to read.
    type At = usize;

    fn next(&mut self, v: usize, k: &mut usize) -> Option<usize> {
        let edges = (self.out)(v);
        while let Some(e) = edges.get(*k) {
            *k += 1;
            if let Some(w) = (self.head)(e) {
                return Some(w);
            }
        }
        None
    }

    fn found(&mut self, members: &mut [usize], _from: Option<usize>) {
        (self.found)(members);
    }
}

/// The strongly connected component of each node of the graph `out`, each edge going to the
/// node `head` gives, the components numbered from 0 in the order [`tarjan`] completes them:
/// an edge from one component to another goes to a lower number.
pub fn components<E>(out: &[Vec<E>], head: impl Fn(&E) -> usize) -> Vec<usize> {
    let n = out.len();
    let (mut comp, mut count) = (vec![usize::MAX; n], 0);
    tarjan(
        n,
        0..n,
        |v| &out[v],
        |e| Some(head(e)),
        |members| {
            for &w in members.iter() {
                comp[w] = count;
            }
            count += 1;
        },
    );
    comp
}

/// Whether each node of the graph `edges` lies on a cycle: in a strongly connected component of
/// two nodes or more, or with an edge to itself.
pub fn on_cycle(edges: &[Vec<usize>]) -> Vec<bool> {
    let n = edges.len();
    let mut cyclic = vec![false; n];
    tarjan(
        n,
        0..n,
        |v| &edges[v],
        |&w| Some(w),
        |members| {
            if members.len() > 1 || edges[members[0]].contains(&members[0]) {
                for &w in members.iter() {
                    cyclic[w] = true;
                }
            }
        },
    );
    cyclic
}

pub mod bitset;
pub mod heap;
pub mod ids;
pub mod worklist;

pub mod union_find;
pub use union_find::{
    Compression, Diff, Keep, Linking, Offset, Parents, Parity, Signed, UnionFind, root_of,
};

pub use bitset::BitSet;
pub use heap::{Dijkstra, Labels, MinHeap, NegativeReducedWeight, reduced};
pub use ids::IdSource;
pub use worklist::{Order, Worklist};

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/scaling.rs"]
#[expect(
    dead_code,
    reason = "the benchmarks use only some of the shared checks"
)]
mod scaling;

// The meter's `malloc` in this crate's test binary, which `scaling` measures each run with
// (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
#[cfg(test)]
zed_alloc_count::meter_entry_points!();

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;

#[cfg(test)]
mod bench;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod units;

mod biconnected;
pub use biconnected::{biconnected, block_of_edges};

mod lift;
pub use lift::{Intervals, Lift, dag_idom};

mod order;
pub use order::{Ready, kahn, make_after_needs, post_order, reach, sources};
