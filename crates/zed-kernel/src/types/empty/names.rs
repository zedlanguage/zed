//! A union's arms that another union it reaches through names also has (item
//! GROUP-cycle-dup-names).
//!
//! A member named as an arm is its own node, so `Node = Alias | (Tree, Tree)` with
//! `Alias = ((int) -> Thunk) | (Tree, Tree)` gives `Node` an arm `(Tree, Tree)` that it also
//! reaches through `Alias`. Written out, the two arms are one, so the decider's count of the
//! independent cycles differed by one between the two ways of writing the group, and the named
//! form could be refused when the written-out form was decided. [`absorb`] makes a copy of the
//! system without such arms, which [`super::judge`] decides as well.
//!
//! Parts of two definitions written alike, and two definitions with one body, are nodes of
//! their own for the same reason (item GROUP-cycle-dup-across). [`merged`] makes a copy of the
//! system with the nodes that play alike made one, which [`super::judge`] decides too, with
//! and without the arms [`absorb`] drops.

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
/// also an arm of one of its union arms, is triangle detection. Trigger: a name used in two
/// places, reached by a union through it and directly, as in
/// `A = B | (A, B) | (int, (int) -> (int) -> B) | (B, A) | ((int) -> B, A | B)` with
/// `B = (B, A) | ((int) -> B, A | B)`: each `A | B` reaches `B` through `A`, which both name, so
/// neither dominates `A`. That group is decided all the same, since the edge from `A | B` to `B`
/// runs along the cycle through `A` (`bes::one_cycle_but_union_chords`) and the two
/// `((int) -> B, A | B)` play alike ([`merged`], item GROUP-cycle-dup-across). Left open: parts
/// equal only once arms are dropped, as with `A`'s `A | B` written `A | B | (B, A)`. Cost: such a
/// group keeps the extra cycle and may be refused, and goes to the search. COMPLEXITY.md K88.
/// A complete solution needs the transitive reduction of the union graph, with the nodes that
/// play alike merged again after it drops arms, until nothing changes.
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

/// `b` with the nodes that play alike made one node, and for each node of `b` its node in the
/// copy, and whether each node of the copy is a union; `None` when no two nodes play alike (item
/// GROUP-cycle-dup-across). `leaf` marks the leaves, the parts the decider does not take, which
/// `b` holds as `Bot` and [`super::judge`] sets `Top` for its second run. `b` is sealed, and so
/// is the copy.
///
/// Two nodes play alike when they lie in one class of the coarsest partition in which the
/// nodes of a class have one kind, are all leaves or all not, and have children in the same
/// classes: the coarsest bisimulation of the system read as a game. The game on the copy is the
/// game on `b` with each class one position, so every node's answer in the copy, with the
/// leaves `Bot` or `Top`, is its answer in `b`, and each answer the decider gives for the copy is
/// the node's. Parts of two definitions written alike are in one class, and so are two
/// definitions with one body, as `Node` and `A2` with
/// `type Node = A1 | (Tree, Tree) | (A2, #z)` and `type A2 = A1 | (Tree, Tree) | (A2, #z)`:
/// each `(A2, #z)` is one node in the copy, and `Node` and `A2` one too. [`super::judge`]
/// decides the copy beside `b`, whose nodes keep the definition that wrote them for the
/// refusal message. The classes do not depend on how the nodes are numbered; the copy numbers
/// them by their first node in `b`.
///
/// Complexity tradeoff: the naive way to the coarsest partition splits every class by its
/// members' sets of child classes until no class splits, a round per split, O(n·m) (Kanellakis
/// and Smolka 1990). Used: the refinement of Paige and Tarjan (1987), O(m log n): a class is
/// split by a smaller part of an earlier class, and each node's count of children in each such
/// part tells the nodes with children in both parts from those with children in one, so a node
/// is in a part handled at most log n times. Tradeoff: one count per node and part it has
/// children in, and the edges into each node, held while the partition is refined.
pub(super) fn merged(b: &Bes, leaf: &[bool], union: &[bool]) -> Option<(Bes, Vec<u32>, Vec<bool>)> {
    let n = b.len();
    // Each node's distinct children, and the edges into each node by their place in `child`.
    let mut at = Vec::with_capacity(n + 1);
    at.push(0);
    let mut child = Vec::new();
    for v in 0..n as u32 {
        let start = child.len();
        child.extend_from_slice(b.children(v));
        child[start..].sort_unstable();
        let mut kept = start;
        for i in start..child.len() {
            if kept == start || child[i] != child[kept - 1] {
                child[kept] = child[i];
                kept += 1;
            }
        }
        child.truncate(kept);
        at.push(child.len());
    }
    let mut into_at = vec![0usize; n + 1];
    for &w in &child {
        into_at[w as usize + 1] += 1;
    }
    for v in 0..n {
        into_at[v + 1] += into_at[v];
    }
    let (mut into, mut fill) = (vec![0u32; child.len()], into_at.clone());
    let mut from = vec![0u32; child.len()];
    for v in 0..n {
        for (e, &w) in child.iter().enumerate().take(at[v + 1]).skip(at[v]) {
            from[e] = v as u32;
            into[fill[w as usize]] = e as u32;
            fill[w as usize] += 1;
        }
    }
    // The first partition: by kind, leaf or not, and whether a node has children (the split by
    // the class of every node).
    let key = |v: usize| {
        let kind = match b.kind(v as u32) {
            Kind::Or => 0,
            Kind::And => 1,
            Kind::Mor => 2,
            Kind::Top => 3,
            Kind::Bot => 4,
        };
        (kind * 2 + usize::from(leaf[v])) * 2 + usize::from(at[v + 1] > at[v])
    };
    let mut p = Partition::new(n, 20, key);
    if p.start.len() == n {
        return None;
    }
    // One count of children per node and coarse class, for the class of every node first.
    let mut count: Vec<u32> = (0..n).map(|v| (at[v + 1] - at[v]) as u32).collect();
    let mut counted: Vec<u32> = from.clone();
    let (mut in_b, mut seen, mut only_b) = (Vec::new(), vec![u32::MAX; n], Vec::new());
    let mut part = Vec::new();
    while let Some(c) = p.compound.last().copied() {
        // The smaller of two fine classes of the coarse class `c` becomes a coarse class.
        let (x, y) = (p.coarse[c as usize][0], p.coarse[c as usize][1]);
        let small = if p.size(x) <= p.size(y) { x } else { y };
        p.leave(small);
        part.clear();
        part.extend_from_slice(p.members(small));
        // The nodes with children in `small`, and each one's count of them.
        in_b.clear();
        for &w in &part {
            for &e in &into[into_at[w as usize]..into_at[w as usize + 1]] {
                let v = from[e as usize] as usize;
                if seen[v] == u32::MAX {
                    seen[v] = count.len() as u32;
                    count.push(0);
                    in_b.push(v as u32);
                }
                count[seen[v] as usize] += 1;
            }
        }
        // Those whose children in the old coarse class all lie in `small`.
        only_b.clear();
        for &w in &part {
            for &e in &into[into_at[w as usize]..into_at[w as usize + 1]] {
                let v = from[e as usize] as usize;
                let whole = counted[e as usize];
                if count[whole as usize] == count[seen[v] as usize] {
                    only_b.push(v as u32);
                }
            }
        }
        p.split(&in_b);
        p.split(&only_b);
        for &w in &part {
            for &e in &into[into_at[w as usize]..into_at[w as usize + 1]] {
                let v = from[e as usize] as usize;
                count[counted[e as usize] as usize] -= 1;
                counted[e as usize] = seen[v];
            }
        }
        for &v in &in_b {
            seen[v as usize] = u32::MAX;
        }
    }
    if p.start.len() == n {
        return None;
    }
    // The copy, each class numbered by its first node.
    let mut id = vec![u32::MAX; p.start.len()];
    let mut first = Vec::new();
    let node: Vec<u32> = (0..n)
        .map(|v| {
            let q = p.class[v] as usize;
            if id[q] == u32::MAX {
                id[q] = first.len() as u32;
                first.push(v);
            }
            id[q]
        })
        .collect();
    let mut m = Bes::new();
    let mut unions = vec![false; first.len()];
    for v in 0..n {
        unions[node[v] as usize] |= union[v];
    }
    for &v in &first {
        let mut children: Vec<u32> = child[at[v]..at[v + 1]]
            .iter()
            .map(|&w| node[w as usize])
            .collect();
        children.sort_unstable();
        children.dedup();
        m.add(b.kind(v as u32), children);
    }
    m.seal();
    Some((m, node, unions))
}

/// A partition of nodes `0..n` into fine classes, each a run of `order`, and of the fine
/// classes into coarse classes, for [`merged`].
struct Partition {
    /// The nodes, each fine class a run.
    order: Vec<u32>,
    /// Each node's place in `order`.
    place: Vec<u32>,
    /// Each node's fine class.
    class: Vec<u32>,
    /// Each fine class's run of `order`, and how many of its nodes [`Partition::split`] has
    /// marked, at the run's start.
    start: Vec<u32>,
    end: Vec<u32>,
    marked: Vec<u32>,
    /// Each fine class's coarse class, and its place in that class's list.
    outer: Vec<u32>,
    slot: Vec<u32>,
    /// Each coarse class's fine classes.
    coarse: Vec<Vec<u32>>,
    /// The coarse classes with two fine classes or more.
    compound: Vec<u32>,
    touched: Vec<u32>,
}

impl Partition {
    /// The fine classes by `key`, below `keys`, in the order of the keys; one coarse class.
    fn new(n: usize, keys: usize, key: impl Fn(usize) -> usize) -> Self {
        let mut at = vec![0u32; keys + 1];
        for v in 0..n {
            at[key(v) + 1] += 1;
        }
        for k in 0..keys {
            at[k + 1] += at[k];
        }
        let mut fill = at.clone();
        let (mut order, mut place) = (vec![0u32; n], vec![0u32; n]);
        let mut class = vec![0u32; n];
        let (mut start, mut end) = (Vec::new(), Vec::new());
        let mut of_key = vec![u32::MAX; keys];
        for v in 0..n {
            let k = key(v);
            if of_key[k] == u32::MAX {
                of_key[k] = start.len() as u32;
                start.push(at[k]);
                end.push(at[k + 1]);
            }
            class[v] = of_key[k];
            order[fill[k] as usize] = v as u32;
            place[v] = fill[k];
            fill[k] += 1;
        }
        let classes = start.len();
        let compound = if classes >= 2 { vec![0] } else { Vec::new() };
        Partition {
            order,
            place,
            class,
            marked: vec![0; classes],
            outer: vec![0; classes],
            slot: (0..classes as u32).collect(),
            coarse: vec![(0..classes as u32).collect()],
            start,
            end,
            compound,
            touched: Vec::new(),
        }
    }

    fn size(&self, q: u32) -> u32 {
        self.end[q as usize] - self.start[q as usize]
    }

    fn members(&self, q: u32) -> &[u32] {
        &self.order[self.start[q as usize] as usize..self.end[q as usize] as usize]
    }

    /// Takes fine class `q` out of its coarse class, which is the last compound one, into a
    /// coarse class of its own.
    fn leave(&mut self, q: u32) {
        let c = self.outer[q as usize] as usize;
        let list = &mut self.coarse[c];
        let i = self.slot[q as usize] as usize;
        list.swap_remove(i);
        if let Some(&moved) = list.get(i) {
            self.slot[moved as usize] = i as u32;
        }
        if list.len() < 2 {
            self.compound.pop();
        }
        self.outer[q as usize] = self.coarse.len() as u32;
        self.slot[q as usize] = 0;
        self.coarse.push(vec![q]);
    }

    /// Splits each fine class into its nodes in `nodes` and the rest; a node may come twice.
    fn split(&mut self, nodes: &[u32]) {
        self.touched.clear();
        for &v in nodes {
            let q = self.class[v as usize] as usize;
            let (i, j) = (self.place[v as usize], self.start[q] + self.marked[q]);
            if i < j {
                continue;
            }
            let w = self.order[j as usize];
            self.order.swap(i as usize, j as usize);
            self.place[v as usize] = j;
            self.place[w as usize] = i;
            if self.marked[q] == 0 {
                self.touched.push(q as u32);
            }
            self.marked[q] += 1;
        }
        for k in 0..self.touched.len() {
            let q = self.touched[k] as usize;
            let m = std::mem::take(&mut self.marked[q]);
            if m == self.end[q] - self.start[q] {
                continue;
            }
            let fresh = self.start.len() as u32;
            let s = self.start[q];
            self.start.push(s);
            self.end.push(s + m);
            self.marked.push(0);
            self.start[q] = s + m;
            for &v in &self.order[s as usize..(s + m) as usize] {
                self.class[v as usize] = fresh;
            }
            let c = self.outer[q] as usize;
            self.outer.push(c as u32);
            self.slot.push(self.coarse[c].len() as u32);
            self.coarse[c].push(fresh);
            if self.coarse[c].len() == 2 {
                self.compound.push(c as u32);
            }
        }
    }
}
