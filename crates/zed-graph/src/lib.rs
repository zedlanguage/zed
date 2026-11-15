//! Graph algorithms shared by every crate of the workspace. It depends on no other crate, so
//! zed-kernel, the lowest of the others, can use it too, and each search below is written once.
//!
//! [`tarjan`] finds the strongly connected components of a directed graph whose nodes are
//! `0..n` (R. Tarjan, "Depth-First Search and Linear Graph Algorithms", SIAM Journal on
//! Computing 1(2), 146-160, 1972), on an explicit stack in place of recursion, so a long chain
//! of nodes cannot overflow the thread's stack. Each node and each edge is read once: O(n + e)
//! time and O(n) space beside the graph. [`components`] and [`on_cycle`] are its two common
//! uses.

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
    mut head: impl FnMut(&E) -> Option<usize>,
    mut found: impl FnMut(&mut [usize]),
) {
    const NEW: usize = usize::MAX;
    // When each node was reached; the least of those of the nodes on the stack it reaches by the
    // edges read so far (the low link); and its place on the stack while its component is open,
    // NEW before and after, so a node is on the stack exactly when its place is not NEW.
    let (mut index, mut low, mut at) = (vec![NEW; n], vec![0; n], vec![NEW; n]);
    // The nodes reached whose component is not yet complete, and the path of the search, each
    // node on it with the place of its next edge to read.
    let (mut stack, mut path): (Vec<usize>, Vec<(usize, usize)>) = (Vec::new(), Vec::new());
    let mut next = 0;
    for root in roots {
        if index[root] != NEW {
            continue;
        }
        path.push((root, 0));
        while let Some(&mut (v, ref mut k)) = path.last_mut() {
            if *k == 0 {
                (index[v], low[v], at[v]) = (next, next, stack.len());
                next += 1;
                stack.push(v);
            }
            if let Some(e) = out(v).get(*k) {
                *k += 1;
                let Some(w) = head(e) else { continue };
                if index[w] == NEW {
                    path.push((w, 0));
                } else if at[w] != NEW {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            // Every edge of `v` is read: its low link passes to the node the search came from.
            path.pop();
            if let Some(&(u, _)) = path.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                let first = at[v];
                for &w in &stack[first..] {
                    at[w] = NEW;
                }
                found(&mut stack[first..]);
                stack.truncate(first);
            }
        }
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

/// The seed of a random test, new on each run and printed, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
mod seed;

#[cfg(test)]
mod bench;

#[cfg(test)]
mod tests;
