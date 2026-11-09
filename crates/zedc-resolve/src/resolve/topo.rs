//! Orders of a dependency graph: each item after what it depends on, or the cycles.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

/// An order of `0..deps.len()` with each item after its dependencies, ties by index; else the
/// items of one cycle, in order along it. The ready items wait in a heap, smallest first, each
/// counting the dependencies it still waits on, so the order takes `O((n + e) log n)`.
#[doc(hidden)]
pub fn topo(deps: &[Vec<usize>]) -> Result<Vec<usize>, Vec<usize>> {
    let (order, done) = place(deps, deps.len(), &vec![false; deps.len()]);
    if order.len() < deps.len() {
        // Every item left waits on another left: walk to the first in each list.
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
/// item. Tarjan's algorithm with an explicit stack of (node, next dependency to read): each
/// node and edge is visited once, then the components are sorted, `O(n + e + c log c)`.
fn cycles(deps: &[Vec<usize>], items: usize, done: &[bool]) -> Vec<Vec<usize>> {
    const UNSEEN: usize = usize::MAX;
    let n = deps.len();
    let (mut index, mut low) = (vec![UNSEEN; n], vec![0; n]);
    let mut on_stack = vec![false; n];
    let (mut stack, mut work): (Vec<usize>, Vec<(usize, usize)>) = (Vec::new(), Vec::new());
    let mut out: Vec<Vec<usize>> = Vec::new();
    let mut next = 0;
    for root in 0..n {
        if done[root] || index[root] != UNSEEN {
            continue;
        }
        work.push((root, 0));
        while let Some(&(v, k)) = work.last() {
            if k == 0 {
                index[v] = next;
                low[v] = next;
                next += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if let Some(&w) = deps[v].get(k) {
                work.last_mut().expect("the node read").1 = k + 1;
                if done[w] {
                    continue;
                }
                if index[w] == UNSEEN {
                    work.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            work.pop();
            if let Some(&(u, _)) = work.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                let at = stack.len()
                    - 1
                    - (stack.iter().rev())
                        .position(|&x| x == v)
                        .expect("a component's root is on the stack");
                let component = stack.split_off(at);
                for &x in &component {
                    on_stack[x] = false;
                }
                if component.len() > 1 || deps[v].contains(&v) {
                    let mut its: Vec<usize> =
                        (component.into_iter()).filter(|&x| x < items).collect();
                    its.sort_unstable();
                    out.push(its);
                }
            }
        }
    }
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
    let mut ready: BinaryHeap<Reverse<usize>> = (0..items)
        .filter(|&i| !out[i] && waits[i] == 0)
        .map(Reverse)
        .collect();
    let mut passed: Vec<usize> = (items..n).filter(|&j| waits[j] == 0).collect();
    let mut done = vec![false; n];
    let mut order = Vec::with_capacity(items);
    loop {
        let i = match passed.pop() {
            Some(j) => j,
            None => match ready.pop() {
                Some(Reverse(i)) => {
                    order.push(i);
                    i
                }
                None => break,
            },
        };
        done[i] = true;
        for &u in &users[i] {
            waits[u] -= 1;
            if waits[u] == 0 {
                match u < items {
                    true => ready.push(Reverse(u)),
                    false => passed.push(u),
                }
            }
        }
    }
    (order, done)
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
