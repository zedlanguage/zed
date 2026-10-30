//! The weak topological order of a dependency graph (DESIGN.md sec:domains, fixed by step
//! M0.5), computed by Bourdoncle's algorithm [Bourdoncle, "Efficient chaotic iteration
//! strategies with widenings", 1993, figure 4].
//!
//! The vertices are `0..n` in source order, and each vertex's successors are listed in source
//! order; the depth-first traversal starts from the vertices in that order and visits
//! successors in that order. A graph has many weak topological orders, and this traversal
//! picks one, so the order, and with it the widening points, is a function of the source.

use std::fmt;

/// An element of a weak topological order: a vertex, or a component with its head and body.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Element {
    /// A vertex on no cycle through the enclosing head.
    Vertex(usize),
    /// A strongly connected part, iterated as a loop: the head, where widening happens, and
    /// the order of the rest, with the edges into the head removed.
    Component {
        /// The head: the first vertex of the component the traversal reaches.
        head: usize,
        /// The weak topological order of the rest of the component.
        body: Vec<Element>,
    },
}

impl Element {
    /// The vertices of the element, in order, each copied once.
    pub fn vertices(&self) -> Vec<usize> {
        let mut out = Vec::new();
        let mut todo = vec![self];
        while let Some(e) = todo.pop() {
            match e {
                Element::Vertex(v) => out.push(*v),
                Element::Component { head, body } => {
                    out.push(*head);
                    todo.extend(body.iter().rev());
                }
            }
        }
        out
    }
}

impl fmt::Display for Element {
    /// Bourdoncle's notation: `0 (1 2 (3 4)) 5`, a component in parentheses, head first.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Element::Vertex(v) => write!(f, "{v}"),
            Element::Component { head, body } => {
                write!(f, "({head}")?;
                for e in body {
                    write!(f, " {e}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Prints an order in Bourdoncle's notation.
pub fn show(order: &[Element]) -> String {
    order
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

/// The weak topological order of the graph whose vertex `v` has the successors `succ[v]`.
///
/// It is the order Bourdoncle's recursive algorithm gives, computed from one depth-first
/// traversal in `O((V + E) log V)` (the rule of low complexity, DESIGN.md Part G), where the
/// recursive algorithm traverses each component again at every level of nesting and costs
/// `O(d·(V + E))` for nesting depth `d`. A vertex is a head when an edge returns to it from its
/// own subtree, and its component is the part of its subtree that reaches it there, found as a
/// loop of the loop-nesting forest (the method of Havlak, "Nesting of reducible and irreducible
/// loops", 1997, with each edge read once as in Ramalingam, "Identifying loops in almost linear
/// time", 1999): an edge that is not a back edge is filed at the common ancestor of its ends,
/// the first vertex whose component can hold both. Each level lists its elements in decreasing
/// order of the time the traversal finished them. The step tests check the result against the
/// declarative definition (`m0_05_widening_and_iteration::wto`).
pub fn weak_topological_order(succ: &[Vec<usize>]) -> Vec<Element> {
    let n = succ.len();
    let t = Traversal::of(succ);
    let mut preds_back: Vec<Vec<usize>> = vec![Vec::new(); n];
    // Each non-back edge, filed at the common ancestor of its ends where it can first lie
    // inside a component.
    let mut filed: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n];
    let up = t.ancestors();
    for (u, ws) in succ.iter().enumerate() {
        for &w in ws {
            if t.ancestor_or_self(w, u) {
                preds_back[w].push(u);
            } else if let Some(a) = t.common_ancestor(&up, u, w) {
                filed[a].push((u, w));
            }
        }
    }
    let mut set: Vec<usize> = (0..n).collect();
    // The edges into each set whose source is not yet known to be inside a component with it.
    let mut entries: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut head_of = vec![NONE; n];
    let mut is_head = vec![false; n];
    let mut taken = vec![NONE; n];
    for &h in t.order.iter().rev() {
        for (u, w) in std::mem::take(&mut filed[h]) {
            let r = find(&mut set, w);
            entries[r].push(u);
        }
        let mut work = Vec::new();
        for &u in &preds_back[h] {
            is_head[h] = true;
            let r = find(&mut set, u);
            if r != h && taken[r] != h {
                taken[r] = h;
                work.push(r);
            }
        }
        let mut members = Vec::new();
        while let Some(x) = work.pop() {
            members.push(x);
            for u in std::mem::take(&mut entries[x]) {
                let r = find(&mut set, u);
                if r != h && taken[r] != h {
                    taken[r] = h;
                    work.push(r);
                }
            }
        }
        // Each member's entries were read when it was taken, so only the set changes.
        for x in members {
            head_of[x] = h;
            set[x] = h;
        }
    }
    // Each level's elements, in decreasing order of finishing.
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); n + 1];
    for &v in t.finished.iter().rev() {
        let level = if head_of[v] == NONE { n } else { head_of[v] };
        children[level].push(v);
    }
    let mut built: Vec<Option<Element>> = (0..n).map(|_| None).collect();
    for &v in &t.finished {
        built[v] = Some(if is_head[v] {
            let body = std::mem::take(&mut children[v])
                .into_iter()
                .map(|c| built[c].take().expect("a member finishes before its head"))
                .collect();
            Element::Component { head: v, body }
        } else {
            Element::Vertex(v)
        });
    }
    std::mem::take(&mut children[n])
        .into_iter()
        .map(|c| built[c].take().expect("every vertex is built"))
        .collect()
}

const NONE: usize = usize::MAX;

/// The set that holds `v`, named by its outermost head found so far; halves the path.
fn find(set: &mut [usize], mut v: usize) -> usize {
    while set[v] != v {
        set[v] = set[set[v]];
        v = set[v];
    }
    v
}

/// The depth-first traversal from the vertices in order, each vertex's successors in order.
struct Traversal {
    /// Each vertex's number in the order the traversal reached it.
    pre: Vec<usize>,
    /// One more than the largest number in the vertex's subtree.
    end: Vec<usize>,
    /// The vertex's parent in the traversal's forest.
    parent: Vec<usize>,
    /// The vertices in the order the traversal reached them.
    order: Vec<usize>,
    /// The vertices in the order the traversal finished them.
    finished: Vec<usize>,
}

impl Traversal {
    fn of(succ: &[Vec<usize>]) -> Traversal {
        let n = succ.len();
        let mut t = Traversal {
            pre: vec![NONE; n],
            end: vec![0; n],
            parent: vec![NONE; n],
            order: Vec::with_capacity(n),
            finished: Vec::with_capacity(n),
        };
        let mut stack: Vec<(usize, usize)> = Vec::new();
        for root in 0..n {
            if t.pre[root] != NONE {
                continue;
            }
            t.pre[root] = t.order.len();
            t.order.push(root);
            stack.push((root, 0));
            while let Some(&mut (v, ref mut i)) = stack.last_mut() {
                if let Some(&w) = succ[v].get(*i) {
                    *i += 1;
                    if t.pre[w] == NONE {
                        t.pre[w] = t.order.len();
                        t.parent[w] = v;
                        t.order.push(w);
                        stack.push((w, 0));
                    }
                } else {
                    stack.pop();
                    t.end[v] = t.order.len();
                    t.finished.push(v);
                }
            }
        }
        t
    }

    /// Whether `a` is `v` or an ancestor of it.
    fn ancestor_or_self(&self, a: usize, v: usize) -> bool {
        self.pre[a] <= self.pre[v] && self.pre[v] < self.end[a]
    }

    /// For each `k`, each vertex's ancestor `2^k` levels up, or itself at a root.
    fn ancestors(&self) -> Vec<Vec<usize>> {
        let n = self.pre.len();
        let first = (0..n)
            .map(|v| {
                if self.parent[v] == NONE {
                    v
                } else {
                    self.parent[v]
                }
            })
            .collect();
        let mut up: Vec<Vec<usize>> = vec![first];
        while (1usize << up.len()) < n.max(1) {
            let last = up.last().expect("one level");
            let next = (0..n).map(|v| last[last[v]]).collect();
            up.push(next);
        }
        up
    }

    /// The deepest common ancestor of `u` and `w`, if they are in one tree.
    fn common_ancestor(&self, up: &[Vec<usize>], u: usize, w: usize) -> Option<usize> {
        if self.ancestor_or_self(u, w) {
            return Some(u);
        }
        let mut a = u;
        for level in up.iter().rev() {
            if !self.ancestor_or_self(level[a], w) {
                a = level[a];
            }
        }
        let p = up[0][a];
        self.ancestor_or_self(p, w).then_some(p)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_chain_has_no_component() {
        let order = weak_topological_order(&[vec![1], vec![2], vec![]]);
        assert_eq!(show(&order), "0 1 2");
    }

    #[test]
    fn an_inner_loop_is_a_component_inside_the_outer_one() {
        // A loop 2 → 3 → 4 → 5 → 6 → 2 with an inner loop 4 ⇄ 5 and an exit 6 → 7. The inner
        // head is 4, which the traversal reaches before 5.
        let succ = vec![
            vec![1],
            vec![2, 7],
            vec![3],
            vec![4, 6],
            vec![5],
            vec![4, 6],
            vec![2, 7],
            vec![],
        ];
        assert_eq!(show(&weak_topological_order(&succ)), "0 1 (2 3 (4 5) 6) 7");
    }

    #[test]
    fn a_self_loop_is_a_component() {
        let order = weak_topological_order(&[vec![0, 1], vec![]]);
        assert_eq!(show(&order), "(0) 1");
        assert_eq!(order[0].vertices(), vec![0]);
    }
}
