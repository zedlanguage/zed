//! Orders of a dependency graph: each item after what it depends on, or the cycles.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

/// An order of `0..deps.len()` with each item after its dependencies, ties by index; else the
/// items of one cycle, in order along it. The ready items wait in a heap, smallest first, each
/// counting the dependencies it still waits on, so the order takes `O((n + e) log n)`.
///
/// Kahn's method (A. B. Kahn, "Topological sorting of large networks", Communications of the
/// ACM 5(11), 558-562, 1962, doi:10.1145/368996.369025, Crossref 2026-11-20, not read: take a
/// node no remaining edge enters, output it, remove its edges, repeat) with a heap in place of
/// its queue. Tarjan's search (`cycles` below)
/// alone also gives an order, the components in the order it closes them, in `O(n + e)`; it is
/// not used for the order because that order follows the depth-first search, not the text,
/// and the order here fixes the order of the checks and so of the messages (DESIGN
/// sec:checking_in_zed, "Checks and evaluations on one dependency graph"). The heap costs the
/// `log n`; `n log n` work passes the scaling limit from `n = 777` (DESIGN sec:plan).
#[doc(hidden)]
pub fn topo(deps: &[Vec<usize>]) -> Result<Vec<usize>, Vec<usize>> {
    let (order, done) = place(deps, deps.len(), &vec![false; deps.len()]);
    if order.len() < deps.len() {
        // Every item left waits on another left: walk to the first in each list.
        // Why the `expect`s here and in `cycle` cannot fire. `place` sets `waits[i]` to the
        // number of entries of `deps[i]` (here nothing is `out`), and `zed_graph::kahn`
        // (zed-graph order.rs) marks a node done when it pops it, decrements `waits[c]` once
        // for each entry of `c`'s list naming that node, and pushes `c` when `waits[c]`
        // reaches 0. So a node not done has `waits > 0`: an entry of its list names a node
        // not done (the `find`). `order` has fewer than `deps.len()` items, and here every
        // node is an item, so some node is not done (`cycle`'s first `find`). `cycle` walks
        // `next` among the finitely many nodes not done, so it meets one twice and stops.
        // Test: `l01_16_elaboration::order::joins_order_as_their_items_written_out` runs
        // `topo` on 4000 random graphs, more than 400 of them with a cycle; it checks only
        // that a cycle is reported (`Err(_)`), not which.
        return Err(cycle(&done, |i| {
            *(deps[i].iter())
                .find(|&&d| !done[d])
                .expect("a dependency left")
        }));
    }
    Ok(order)
}

/// [`topo`] of the items `0..items` of a graph whose nodes from `items` on are joins, each
/// waiting on the items of its list: an item waiting on a join waits on each of them. The
/// order is that of the graph with each join's items written into each list naming the join,
/// at the cost of the graph as given. Else every cycle of the graph: each strongly connected
/// component that holds a cycle, as its items in increasing order, the components in order
/// of their least item, so the set reported does not depend on where the search starts.
#[doc(hidden)]
pub fn topo_joined(deps: &[Vec<usize>], items: usize) -> Result<Vec<usize>, Vec<Vec<usize>>> {
    let (order, done) = place(deps, items, &vec![false; deps.len()]);
    if order.len() < items {
        return Err(cycles(deps, items, &done));
    }
    Ok(order)
}

/// [`topo_joined`] that orders around the cycles: every item outside a cycle, each after
/// its dependencies outside a cycle, ties by index, as [`topo_joined`] orders the graph with
/// the items of every cycle taken out; and every cycle, as [`topo_joined`] gives them. An
/// item that waits on a cycle, directly or through other items, is placed: a cycle passes
/// through items only, a join waiting on items alone, so taking out the items of every
/// cycle leaves a graph with none. `O((n + e) log n)`: two placements and one search for
/// the cycles, each visiting every node and edge once.
pub fn topo_around_cycles(deps: &[Vec<usize>], items: usize) -> (Vec<usize>, Vec<Vec<usize>>) {
    let (order, done) = place(deps, items, &vec![false; deps.len()]);
    if order.len() == items {
        return (order, Vec::new());
    }
    let cycles = cycles(deps, items, &done);
    let mut out = vec![false; deps.len()];
    for &i in cycles.iter().flatten() {
        out[i] = true;
    }
    let (order, _) = place(deps, items, &out);
    debug_assert_eq!(
        order.len() + cycles.iter().map(Vec::len).sum::<usize>(),
        items,
        "every item outside a cycle is placed"
    );
    (order, cycles)
}

/// The strongly connected components of the nodes not `done` that hold a cycle, each as its
/// items, those below `items`, in increasing order, the components in order of their least
/// item, by [`zed_graph::tarjan`] (R. Tarjan, "Depth-First Search and Linear Graph
/// Algorithms", SIAM Journal on Computing 1(2), 146-160, 1972, doi:10.1137/0201010, Crossref
/// 2026-11-20): each node and edge is visited
/// once, then the components are sorted, `O(n + e + c log c)`.
fn cycles(deps: &[Vec<usize>], items: usize, done: &[bool]) -> Vec<Vec<usize>> {
    let n = deps.len();
    let mut out: Vec<Vec<usize>> = Vec::new();
    zed_graph::tarjan(
        n,
        (0..n).filter(|&v| !done[v]),
        |v| &deps[v],
        |&w| (!done[w]).then_some(w),
        |component| {
            let v = component[0];
            if component.len() > 1 || deps[v].contains(&v) {
                let mut its: Vec<usize> =
                    (component.iter().copied()).filter(|&x| x < items).collect();
                its.sort_unstable();
                out.push(its);
            }
        },
    );
    // A join waits only on items, so every cycle passes an item.
    out.sort_unstable_by_key(|c| c[0]);
    out
}

/// The items of `0..items` placed in order, and which nodes are placed or passed. A join is
/// passed once its last item is placed, before the next item is taken, so the items ready at
/// each step are those of the graph without joins. A node marked `out` is taken out of the
/// graph: it is never placed, and nothing waits on it.
fn place(deps: &[Vec<usize>], items: usize, out: &[bool]) -> (Vec<usize>, Vec<bool>) {
    let n = deps.len();
    let mut waits: Vec<usize> = vec![0; n];
    let mut users: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, ds) in deps.iter().enumerate() {
        if out[i] {
            continue;
        }
        for &d in ds.iter().filter(|&&d| !out[d]) {
            waits[i] += 1;
            users[d].push(i);
        }
    }
    let ready: BinaryHeap<Reverse<usize>> = (0..items)
        .filter(|&i| !out[i] && waits[i] == 0)
        .map(Reverse)
        .collect();
    let passed: Vec<usize> = (items..n).filter(|&j| waits[j] == 0).collect();
    let mut done = vec![false; n];
    let mut order = Vec::with_capacity(items);
    zed_graph::kahn(
        &mut waits,
        &mut JoinsFirst {
            items,
            passed,
            ready,
        },
        |i| users[i].iter().copied(),
        |i| {
            done[i] = true;
            if i < items {
                order.push(i);
            }
        },
    );
    (order, done)
}

/// The ready nodes of [`place`]: a join ready is passed before any item is taken (last ready
/// first, as the order among joins changes nothing), and the items are taken least first.
struct JoinsFirst {
    items: usize,
    passed: Vec<usize>,
    ready: BinaryHeap<Reverse<usize>>,
}

impl zed_graph::Ready for JoinsFirst {
    fn push(&mut self, v: usize) {
        match v < self.items {
            true => self.ready.push(Reverse(v)),
            false => self.passed.push(v),
        }
    }
    fn pop(&mut self) -> Option<usize> {
        self.passed
            .pop()
            .or_else(|| self.ready.pop().map(|Reverse(i)| i))
    }
}

/// The cycle reached from the first item left by `next`, which gives the item left that an
/// item left waits on.
fn cycle(done: &[bool], mut next: impl FnMut(usize) -> usize) -> Vec<usize> {
    let mut seen: BTreeMap<usize, usize> = BTreeMap::new();
    let mut path = Vec::new();
    let mut i = (0..done.len()).find(|&i| !done[i]).expect("an item left");
    while !seen.contains_key(&i) {
        seen.insert(i, path.len());
        path.push(i);
        i = next(i);
    }
    path.split_off(seen[&i])
}
