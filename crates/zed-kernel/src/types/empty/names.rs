//! A union's arms that another union it reaches through names also has (item
//! GROUP-cycle-dup-names).
//!
//! A member named as an arm is its own node, so `Node = Alias | (Tree, Tree)` with
//! `Alias = ((int) -> Thunk) | (Tree, Tree)` gives `Node` an arm `(Tree, Tree)` that it also
//! reaches through `Alias`. Written out, the two arms are one, so the decider's count of the
//! independent cycles differed by one between the two ways of writing the group, and the named
//! form could be refused when the written-out form was decided. [`absorb`] makes a copy of the
//! system without such arms, which [`super::judge`] decides as well.

use super::super::bes::{Bes, Kind};

/// A copy of `b` without the arms of each union node whose type (`same`, by node) is an arm of
/// another union node that it reaches through unions, when the dominators or the
/// post-dominators of the union graph show that it reaches it; `None` when no arm is dropped.
/// `union` marks the union nodes: a member whose body is a union or a name, and a union part.
/// `b` is sealed, and so is the copy.
///
/// A union keeps each type it reaches through unions: a dropped arm's type is an arm of a union
/// it reaches by an arm that is kept, so the copy is a system of the same types and each answer
/// it decides is the type's. The copy does not replace `b`: the decider's bounds and its count
/// of cycles depend on the graph's shape, not only on its number of edges, and dropping arms
/// can turn a decided member into a refused one:
/// `D0 = (D0, D0) | D1 | ((D0, int), (int) -> D1) | (int) -> (D0, D0)` with
/// `D1 = ((D0, int), (int) -> D1) | (int) -> (D0, D0) | (D0, D0)` is decided inhabited, and
/// refused with `D0`'s arms that `D1` has dropped. Taking
/// a member decided by either system therefore decides every member `b` decides. The dominator
/// and post-dominator trees are unique, so what is dropped does not depend on the order of the
/// definitions or of the arms.
///
/// Time O(m log m) in the union nodes' arms: a topological order of the union graph, the
/// dominators by lowest common ancestors over binary lifting, then a sort of (type, union)
/// pairs; the copy is linear in `b`.
///
/// Complexity tradeoff: an arm is dropped only when the union dominates, in the graph of unions
/// through their union arms, another union with an arm of its type, or is post-dominated by one.
/// Why: dropping every arm that a union reaches through another path is the transitive
/// reduction of that graph, which costs as much as its transitive closure (Aho, Garey and
/// Ullman 1972), O(n·m) or a matrix product; even the one-level case, an arm of a union that is
/// also an arm of one of its union arms, is triangle detection. Trigger: a name
/// used in two places, reached by a union through it and directly: in
/// `A = B | (A, B) | (int, (int) -> (int) -> B) | (B, A) | ((int) -> B, A | B)` with
/// `B = (B, A) | ((int) -> B, A | B)`, each `A | B` reaches `B` through `A`, which both name, so
/// neither dominates `A`, and the group is refused where `A | B` written `A` is decided; two
/// names with equal bodies; parts equal only once arms are dropped. Cost: such a
/// group keeps the extra cycle and may be refused, as before this item, and goes to the
/// search. COMPLEXITY.md K88. A complete solution needs the transitive reduction of the union
/// graph.
pub(super) fn absorb(b: &Bes, same: &[u32], union: &[bool]) -> Option<Bes> {
    // The union nodes, numbered 0..k; `k` is the virtual root of each tree.
    let unions: Vec<u32> = (0..b.len() as u32).filter(|&v| union[v as usize]).collect();
    let k = unions.len();
    if k < 2 {
        return None;
    }
    let mut local = vec![u32::MAX; b.len()];
    for (i, &v) in unions.iter().enumerate() {
        local[v as usize] = i as u32;
    }
    // The union graph: each union's arms that are unions, by local number, both ways.
    let (mut down, mut up) = (vec![Vec::new(); k], vec![Vec::new(); k]);
    for (i, &v) in unions.iter().enumerate() {
        for &c in b.children(v) {
            let c = local[c as usize];
            if c != u32::MAX {
                down[i].push(c);
                up[c as usize].push(i as u32);
            }
        }
    }
    let order = topological(&down, &up);
    // The dominator tree from the unions no union names, and the post-dominator tree from the
    // unions with no union arm; a node's immediate (post-)dominator is the lowest common
    // ancestor of its parents (children) in the union graph, all placed before it.
    let mut dom = Lift::new(k);
    for &v in &order {
        dom.attach(v, idom(&dom, &up[v as usize], k as u32));
    }
    let mut post = Lift::new(k);
    for &v in order.iter().rev() {
        post.attach(v, idom(&post, &down[v as usize], k as u32));
    }
    let (dom, post) = (dom.intervals(), post.intervals());
    // Each arm's type with the union that has it, grouped by type.
    let mut pairs: Vec<(u32, u32)> = (unions.iter().enumerate())
        .flat_map(|(i, &v)| {
            b.children(v)
                .iter()
                .map(move |&c| (same[c as usize], i as u32))
        })
        .collect();
    pairs.sort_unstable();
    pairs.dedup();
    let mut drops: Vec<(u32, u32)> = Vec::new();
    let (mut by_dom, mut by_post, mut open) = (Vec::new(), Vec::new(), Vec::new());
    for run in pairs.chunk_by(|x, y| x.0 == y.0) {
        if run.len() < 2 {
            continue;
        }
        let ty = run[0].0;
        // A union with another of the run in its dominator subtree reaches it.
        by_dom.clear();
        by_dom.extend(run.iter().map(|&(_, u)| u));
        by_dom.sort_unstable_by_key(|&u| dom.pre[u as usize]);
        for w in by_dom.windows(2) {
            let (u, next) = (w[0] as usize, w[1] as usize);
            if dom.pre[next] <= dom.last[u] {
                drops.push((w[0], ty));
            }
        }
        // A union with another of the run among its post-dominators reaches it.
        by_post.clear();
        by_post.extend(run.iter().map(|&(_, u)| u));
        by_post.sort_unstable_by_key(|&u| post.pre[u as usize]);
        open.clear();
        for &u in &by_post {
            while open
                .last()
                .is_some_and(|&a: &u32| post.last[a as usize] < post.pre[u as usize])
            {
                open.pop();
            }
            if !open.is_empty() {
                drops.push((u, ty));
            }
            open.push(u);
        }
    }
    // By union, then type; a union dropped by both tests is listed twice.
    drops.sort_unstable();
    drops.dedup();
    if drops.is_empty() {
        return None;
    }
    let mut a = b.clone();
    for run in drops.chunk_by(|x, y| x.0 == y.0) {
        let v = unions[run[0].0 as usize];
        let kept: Vec<u32> = (b.children(v).iter())
            .copied()
            .filter(|&c| {
                run.binary_search_by_key(&same[c as usize], |d| d.1)
                    .is_err()
            })
            .collect();
        debug_assert!(
            !kept.is_empty(),
            "a union keeps the arm that reaches the other"
        );
        a.set(v, Kind::Or, kept);
    }
    a.seal();
    Some(a)
}

/// The union graph's nodes, each after its parents (Kahn's algorithm); the graph is acyclic,
/// since a member's body is contractive.
fn topological(down: &[Vec<u32>], up: &[Vec<u32>]) -> Vec<u32> {
    let mut need: Vec<usize> = up.iter().map(Vec::len).collect();
    let mut order: Vec<u32> = (0..down.len() as u32)
        .filter(|&v| need[v as usize] == 0)
        .collect();
    let mut i = 0;
    while let Some(&v) = order.get(i) {
        i += 1;
        for &c in &down[v as usize] {
            need[c as usize] -= 1;
            if need[c as usize] == 0 {
                order.push(c);
            }
        }
    }
    debug_assert_eq!(
        order.len(),
        down.len(),
        "unions through names form no cycle"
    );
    order
}

/// The lowest common ancestor in `tree` of `parents`, or `root` when there is none.
fn idom(tree: &Lift, parents: &[u32], root: u32) -> u32 {
    (parents.iter().copied())
        .reduce(|a, c| tree.lca(a, c))
        .unwrap_or(root)
}

/// A tree grown leaf by leaf, with each node's ancestors at powers of two for lowest common
/// ancestors in O(log n); node `k` of `k + 1` is the root.
struct Lift {
    levels: usize,
    depth: Vec<u32>,
    /// The ancestor 2^j above node `v` at `v * levels + j`, the root above the root.
    up: Vec<u32>,
}

impl Lift {
    fn new(k: usize) -> Self {
        let levels = (usize::BITS - k.leading_zeros()) as usize + 1;
        let mut up = vec![0; (k + 1) * levels];
        up[k * levels..].fill(k as u32);
        Lift {
            levels,
            depth: vec![0; k + 1],
            up,
        }
    }

    fn attach(&mut self, v: u32, parent: u32) {
        let (v, l) = (v as usize, self.levels);
        self.depth[v] = self.depth[parent as usize] + 1;
        self.up[v * l] = parent;
        for j in 1..l {
            self.up[v * l + j] = self.up[self.up[v * l + j - 1] as usize * l + j - 1];
        }
    }

    fn lca(&self, mut a: u32, mut c: u32) -> u32 {
        let l = self.levels;
        if self.depth[a as usize] < self.depth[c as usize] {
            std::mem::swap(&mut a, &mut c);
        }
        let mut rise = self.depth[a as usize] - self.depth[c as usize];
        let mut j = 0;
        while rise > 0 {
            if rise & 1 == 1 {
                a = self.up[a as usize * l + j];
            }
            rise >>= 1;
            j += 1;
        }
        if a == c {
            return a;
        }
        for j in (0..l).rev() {
            let (x, y) = (self.up[a as usize * l + j], self.up[c as usize * l + j]);
            if x != y {
                (a, c) = (x, y);
            }
        }
        self.up[a as usize * l]
    }

    /// Each node's preorder number and the largest in its subtree, children in any order.
    fn intervals(&self) -> Intervals {
        let n = self.depth.len();
        let root = n - 1;
        let mut kids = vec![Vec::new(); n];
        for v in 0..root {
            kids[self.up[v * self.levels] as usize].push(v as u32);
        }
        let (mut pre, mut last) = (vec![0u32; n], vec![0u32; n]);
        let (mut next, mut stack) = (0u32, vec![(root as u32, false)]);
        while let Some((v, closing)) = stack.pop() {
            if closing {
                last[v as usize] = next - 1;
                continue;
            }
            pre[v as usize] = next;
            next += 1;
            stack.push((v, true));
            stack.extend(kids[v as usize].iter().map(|&c| (c, false)));
        }
        Intervals { pre, last }
    }
}

/// A tree's preorder numbers: `w` is in `v`'s subtree when `pre[v] <= pre[w] <= last[v]`.
struct Intervals {
    pre: Vec<u32>,
    last: Vec<u32>,
}
