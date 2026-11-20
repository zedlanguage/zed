//! Inhabitation of a recursive type group as a Boolean equation system (DESIGN.md
//! sec:type_language, cross-review X14): one node for each type of the group and each part of
//! it, of five kinds. An `Or` node is inhabited when one child is (a union), an `And` node when
//! every child is (a tuple, whose components must all have values), a `Mor` node when its one
//! child, the value type of a morphism type, is inhabited; `Top` is inhabited and `Bot` is not.
//!
//! The fixed point differs by the edge a cycle passes through. A value is finite, so a cycle of
//! tuple edges alone holds no value: such nodes take the least fixed point. A morphism is a
//! value however its value type recurs, since a function can return without calling itself, so
//! a cycle through a `Mor` edge takes the greatest fixed point. Groups mixing both are a game
//! whose answers [`decide`] finds in time linear in nodes and edges:
//!
//! 1. edges no least fixed point can use are dropped (an `And` child that is an `And` parent of
//!    the same node, a self loop);
//! 2. the strongly connected components are taken bottom up; a component with no tuple cycle
//!    takes the greatest fixed point, one with no `Mor` edge inside it the least;
//! 3. other components get a lower and an upper bound, each a few fixed-point passes; nodes
//!    where they agree are decided;
//! 4. the undecided nodes are split into components again; one with a single `Mor` edge inside
//!    is solved exactly by two least-fixed-point passes, one where every tuple cycle has one
//!    player's choices only by one deletion cascade;
//! 5. a component left with a tuple cycle of cyclomatic number 2 or more and an `And` node with
//!    two undecided children is refused, with its counts as the cause, and so is every node
//!    whose answer depends on a refused one; a tuple cycle that is one simple cycle once the
//!    `Or` edges running along it are dropped is not refused (item GROUP-cycle-dup-across).
//!
//! No step depends on a size: a refusal is a property of the component's shape. Results do not
//! depend on the order nodes are numbered in.

/// A node's kind.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// A union: inhabited when one child is.
    Or,
    /// A tuple or an atom payload: inhabited when every child is.
    And,
    /// A morphism type; its one child is the value type.
    Mor,
    /// A type with a value outside the group.
    Top,
    /// A type with no value.
    Bot,
}

/// A Boolean equation system: each node's kind, children and parents.
#[derive(Clone, Debug, Default)]
pub struct Bes {
    kind: Vec<Kind>,
    children: Vec<Vec<u32>>,
    parents: Vec<Vec<u32>>,
}

impl Bes {
    /// A system with no node.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a node and returns its number. A `Mor` node has exactly one child, and a `Top` or
    /// `Bot` node none, so that no constant node is on a cycle or is a parent: the arms for
    /// them in the passes over a component with a cycle are `unreachable!`.
    pub fn add(&mut self, kind: Kind, children: Vec<u32>) -> u32 {
        assert!(
            kind != Kind::Mor || children.len() == 1,
            "a morphism node has its value type as its one child"
        );
        assert!(
            !matches!(kind, Kind::Top | Kind::Bot) || children.is_empty(),
            "a constant node has no child"
        );
        let v = u32::try_from(self.kind.len()).expect("a group has fewer than 2^32 nodes");
        self.kind.push(kind);
        self.children.push(children);
        self.parents.push(Vec::new());
        v
    }

    /// Sets a node's children, for a node added before them.
    pub fn set(&mut self, v: u32, kind: Kind, children: Vec<u32>) {
        assert!(
            kind != Kind::Mor || children.len() == 1,
            "a morphism node has its value type as its one child"
        );
        assert!(
            !matches!(kind, Kind::Top | Kind::Bot) || children.is_empty(),
            "a constant node has no child"
        );
        self.kind[v as usize] = kind;
        self.children[v as usize] = children;
    }

    /// Fills in the parents; called once all nodes are added.
    pub fn seal(&mut self) {
        for p in &mut self.parents {
            p.clear();
        }
        for (v, cs) in self.children.iter().enumerate() {
            for &w in cs {
                self.parents[w as usize].push(v as u32);
            }
        }
    }

    /// The number of nodes.
    pub fn len(&self) -> usize {
        self.kind.len()
    }

    /// Whether there is no node.
    pub fn is_empty(&self) -> bool {
        self.kind.is_empty()
    }

    /// The kind of node `v`.
    pub fn kind(&self, v: u32) -> Kind {
        self.kind[v as usize]
    }

    /// The children of node `v`.
    pub fn children(&self, v: u32) -> &[u32] {
        &self.children[v as usize]
    }

    /// The parents of node `v`, once the system is sealed.
    pub fn parents(&self, v: u32) -> &[u32] {
        &self.parents[v as usize]
    }

    /// Whether `tc`, a component of the tuple graph, has a cycle.
    fn cyclic(&self, tc: &[u32]) -> bool {
        tc.len() > 1 || {
            let v = tc[0];
            self.kind(v) != Kind::Mor && self.children(v).contains(&v)
        }
    }
}

/// A node's answer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Answer {
    /// No value.
    Empty,
    /// Some value.
    Inhabited,
    /// Not decided: the node is in, or depends on, a refused component.
    Refused,
}

/// Why a component was refused: a tuple cycle among undecided nodes with more than one way
/// around it and an `And` node that needs two undecided children. The counts are those of the
/// first such cycle found; `component` and `tuples` are sets, which do not depend on the order
/// the nodes are numbered in, for a message to name (item GROUP-refusal).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Refusal {
    /// The undecided nodes of the refused component, in increasing order.
    pub component: Vec<u32>,
    /// The `And` nodes with two or more undecided children on every tuple cycle of the
    /// component that is refused for its shape, in increasing order.
    pub tuples: Vec<u32>,
    /// A node of the refused tuple cycle.
    pub node: u32,
    /// The nodes of the tuple cycle.
    pub nodes: usize,
    /// The distinct edges between them.
    pub internal_edges: usize,
    /// Edges minus nodes plus one: the number of independent cycles.
    pub cyclomatic: usize,
    /// `And` nodes with two or more undecided children.
    pub branching_and: usize,
    /// `Or` nodes with two or more undecided children, at least 1.
    pub branching_or: usize,
    /// The morphism types inside the undecided component.
    pub gates: usize,
}

/// The answer for each node and the refusals that left nodes undecided.
#[derive(Clone, Debug)]
pub struct Decision {
    /// One for each node.
    pub answers: Vec<Answer>,
    /// One for each refused component.
    pub refusals: Vec<Refusal>,
}

/// Buffers sized once to the number of nodes, so no pass over a component allocates in the
/// number of nodes.
struct Scratch {
    in_sub: Vec<bool>,
    local: Vec<u32>,
    t_comp: Vec<u32>,
    o_comp: Vec<u32>,
    need: Vec<u32>,
    lo: Vec<bool>,
    hi: Vec<bool>,
    cur: Vec<bool>,
    tmp: Vec<bool>,
    queue: Vec<u32>,
}

impl Scratch {
    fn new(n: usize) -> Self {
        Self {
            in_sub: vec![false; n],
            local: vec![u32::MAX; n],
            t_comp: vec![u32::MAX; n],
            o_comp: vec![u32::MAX; n],
            need: vec![0; n],
            lo: vec![false; n],
            hi: vec![false; n],
            cur: vec![false; n],
            tmp: vec![false; n],
            queue: Vec::with_capacity(n),
        }
    }

    fn base(&self, lo: bool) -> &[bool] {
        if lo { &self.lo } else { &self.hi }
    }

    fn mark(&mut self, sub: &[u32], on: bool) {
        for &v in sub {
            self.in_sub[v as usize] = on;
        }
    }
}

/// Which edges a component search follows.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Edges {
    All,
    /// Every edge but those out of `Mor` nodes.
    Tuple,
    /// Edges from an `Or` node to an `Or` node.
    OrOr,
}

/// Per-node marks for counting distinct successors: `mark[w] == cur` means `w` was seen under
/// the current node. Advancing `cur` clears every mark at once; at `u32::MAX` the marks are
/// cleared and counting starts again.
struct Stamp {
    mark: Vec<u32>,
    cur: u32,
}

impl Stamp {
    fn new(n: usize) -> Self {
        Self {
            mark: vec![0; n],
            cur: 0,
        }
    }

    fn advance(&mut self) {
        if self.cur == u32::MAX {
            self.mark.fill(0);
            self.cur = 0;
        }
        self.cur += 1;
    }

    /// Marks `w`; true if `w` was not yet marked under the current node.
    fn first(&mut self, w: usize) -> bool {
        let fresh = self.mark[w] != self.cur;
        self.mark[w] = self.cur;
        fresh
    }
}

/// The strongly connected components of `sub` along `edges`, children first
/// ([`zed_graph::tarjan`]), the members of each in the order the search completed them.
// Memory: the shared search keeps its arrays per node in usize, where this module's own copy
// before DEDUP-tarjan kept u32 and bool: 24 bytes per node of `sub` in place of 9, beside the
// graph; the time is the same O(nodes + edges of `sub`).
fn components(g: &Bes, sub: &[u32], edges: Edges, local: &mut [u32]) -> Vec<Vec<u32>> {
    for (i, &v) in sub.iter().enumerate() {
        local[v as usize] = i as u32;
    }
    let follows = |u: u32| match edges {
        Edges::All => true,
        Edges::Tuple => g.kind(u) != Kind::Mor,
        Edges::OrOr => g.kind(u) == Kind::Or,
    };
    let mut out: Vec<Vec<u32>> = Vec::new();
    let place: &[u32] = local;
    zed_graph::tarjan(
        sub.len(),
        0..sub.len(),
        |u| {
            let u = sub[u];
            if follows(u) { g.children(u) } else { &[] }
        },
        |&w| {
            if edges == Edges::OrOr && g.kind(w) != Kind::Or {
                return None;
            }
            let w = place[w as usize];
            (w != u32::MAX).then_some(w as usize)
        },
        |c| out.push(c.iter().rev().map(|&w| sub[w]).collect()),
    );
    for &v in sub {
        local[v as usize] = u32::MAX;
    }
    out
}

/// Whether `sub` without the edges out of `Mor` nodes has a cycle.
fn has_tuple_cycle(g: &Bes, sub: &[u32], local: &mut [u32]) -> bool {
    components(g, sub, Edges::Tuple, local)
        .iter()
        .any(|c| g.cyclic(c))
}

/// How a least-fixed-point pass reads a `Mor` node whose child is inside the component.
#[derive(Clone, Copy, PartialEq, Eq)]
enum MorRead {
    /// As not inhabited: the pure tuple least fixed point.
    False,
    /// As an `And` of its child, solved with the rest.
    Joint,
    /// As its child's value in `tmp`.
    FromTmp,
}

/// The least fixed point on `sub` into `cur`. Nodes outside `sub` read `lo` when `base_lo`,
/// else `hi`. When `seed_tmp`, nodes with `tmp` set start inhabited; `forced`, if a node, starts
/// inhabited.
fn lfp(
    g: &Bes,
    sub: &[u32],
    base_lo: bool,
    mor: MorRead,
    seed_tmp: bool,
    forced: Option<u32>,
    sc: &mut Scratch,
) {
    sc.queue.clear();
    for &v in sub {
        sc.in_sub[v as usize] = true;
        sc.cur[v as usize] = false;
    }
    for &v_u32 in sub {
        let v = v_u32 as usize;
        let base = sc.base(base_lo);
        let need = if forced == Some(v_u32) || (seed_tmp && sc.tmp[v]) {
            0
        } else {
            match g.kind(v_u32) {
                // `sub` lies in a component with a tuple cycle (`settle` with one, `bounds`,
                // step 4 of `decide`), and a constant, with no child, is on no cycle.
                Kind::Top | Kind::Bot => {
                    unreachable!("a constant node in a component with a cycle")
                }
                Kind::Mor => {
                    let w = g.children(v_u32)[0] as usize;
                    let holds = if !sc.in_sub[w] {
                        Some(base[w])
                    } else {
                        match mor {
                            MorRead::False => Some(false),
                            MorRead::FromTmp => Some(sc.tmp[w]),
                            MorRead::Joint => None,
                        }
                    };
                    match holds {
                        Some(true) => 0,
                        Some(false) => u32::MAX,
                        None => 1,
                    }
                }
                Kind::Or => {
                    let ext = g
                        .children(v_u32)
                        .iter()
                        .any(|&w| !sc.in_sub[w as usize] && base[w as usize]);
                    if ext { 0 } else { 1 }
                }
                Kind::And => {
                    let mut ext_false = false;
                    let mut internal = 0u32;
                    for &w in g.children(v_u32) {
                        if sc.in_sub[w as usize] {
                            internal += 1;
                        } else if !base[w as usize] {
                            ext_false = true;
                        }
                    }
                    if ext_false { u32::MAX } else { internal }
                }
            }
        };
        sc.need[v] = need;
        if need == 0 {
            sc.cur[v] = true;
            sc.queue.push(v_u32);
        }
    }
    while let Some(w) = sc.queue.pop() {
        for &p_u32 in &g.parents[w as usize] {
            let p = p_u32 as usize;
            // A `Mor` parent is counted down only under `MorRead::Joint`: under `False` and
            // `FromTmp` its child `w`, in `sub`, gave it a need of 0 (so it is inhabited) or of
            // `u32::MAX`, and this test skips it.
            if !sc.in_sub[p] || sc.cur[p] || sc.need[p] == u32::MAX {
                continue;
            }
            sc.need[p] -= 1;
            if sc.need[p] == 0 {
                sc.cur[p] = true;
                sc.queue.push(p_u32);
            }
        }
    }
    sc.mark(sub, false);
}

/// The greatest fixed point on `sub` into `cur`. Nodes outside `sub` read `lo` when `base_lo`,
/// else `hi`. When `start_tmp`, only nodes with `tmp` set start inhabited. When `narrow`, an
/// `And` node's edges inside its tuple component (`t_comp`) and an `Or` node's edges to `Or`
/// nodes of its `Or` component (`o_comp`) read as not inhabited.
fn gfp(g: &Bes, sub: &[u32], base_lo: bool, start_tmp: bool, narrow: bool, sc: &mut Scratch) {
    sc.queue.clear();
    for &v in sub {
        let v = v as usize;
        sc.in_sub[v] = true;
        sc.cur[v] = (!start_tmp || sc.tmp[v]) && g.kind[v] != Kind::Bot;
    }
    let is_cut = |sc: &Scratch, v: usize, w: usize| -> bool {
        if !narrow || !sc.in_sub[w] || sc.t_comp[v] == u32::MAX || sc.t_comp[v] != sc.t_comp[w] {
            return false;
        }
        match g.kind[v] {
            Kind::And => true,
            Kind::Or => g.kind[w] == Kind::Or && sc.o_comp[v] == sc.o_comp[w],
            Kind::Mor => false,
            // `w` is a child of `v` (both callers), and a constant has no child: `Bes::add` and
            // `Bes::set` assert it, and `simplify` makes a node `Bot` only with no children.
            Kind::Top | Kind::Bot => unreachable!("a constant node has no child `w`"),
        }
    };
    for &v_u32 in sub {
        let v = v_u32 as usize;
        if !sc.cur[v] {
            sc.need[v] = 0;
            sc.queue.push(v_u32);
            continue;
        }
        let base = sc.base(base_lo);
        let mut ok = 0u32;
        for &w in g.children(v_u32) {
            let w = w as usize;
            let ok_w = if sc.in_sub[w] {
                !is_cut(sc, v, w)
            } else {
                base[w]
            };
            if ok_w {
                ok += 1;
            }
        }
        sc.need[v] = ok;
        let dead = match g.kind[v] {
            Kind::Or => ok == 0,
            Kind::And | Kind::Mor => (ok as usize) < g.children[v].len(),
            Kind::Top | Kind::Bot => false,
        };
        if dead {
            sc.cur[v] = false;
            sc.need[v] = 0;
            sc.queue.push(v_u32);
        }
    }
    while let Some(w) = sc.queue.pop() {
        let w = w as usize;
        for &p_u32 in &g.parents[w] {
            let p = p_u32 as usize;
            if !sc.in_sub[p] || !sc.cur[p] || is_cut(sc, p, w) {
                continue;
            }
            let dead = match g.kind[p] {
                Kind::Or => {
                    sc.need[p] -= 1;
                    sc.need[p] == 0
                }
                Kind::And | Kind::Mor => true,
                // `Bes::seal` makes `p` a parent of `w` only for a child `w` of `p`, and a
                // constant has no child (`Bes::add`, `Bes::set`, `simplify`).
                Kind::Top | Kind::Bot => unreachable!("a constant node is no node's parent"),
            };
            if dead {
                sc.cur[p] = false;
                sc.need[p] = 0;
                sc.queue.push(p_u32);
            }
        }
    }
    sc.mark(sub, false);
}

fn copy_cur(sub: &[u32], from: &[bool], to: &mut [bool]) {
    for &v in sub {
        to[v as usize] = from[v as usize];
    }
}

/// Decides `sub` without a refusal: by the greatest fixed point when it has no tuple cycle,
/// else by the least.
fn settle(g: &Bes, sub: &[u32], tuple_cycle: bool, sc: &mut Scratch) {
    for base_lo in [true, false] {
        if tuple_cycle {
            lfp(g, sub, base_lo, MorRead::False, false, None, sc);
        } else {
            gfp(g, sub, base_lo, false, false, sc);
        }
        let Scratch { cur, lo, hi, .. } = sc;
        copy_cur(sub, cur, if base_lo { lo } else { hi });
    }
}

/// The lower bound `lo` (the narrowed greatest fixed point, then the least fixed point seeded by
/// it) and the upper bound `hi` (greatest, least reading `Mor` children from it, greatest again)
/// on `sub`.
fn bounds(g: &Bes, sub: &[u32], sc: &mut Scratch) {
    for (i, t) in components(g, sub, Edges::Tuple, &mut sc.local)
        .iter()
        .enumerate()
    {
        for &v in t {
            sc.t_comp[v as usize] = i as u32;
        }
    }
    for (i, o) in components(g, sub, Edges::OrOr, &mut sc.local)
        .iter()
        .enumerate()
    {
        for &v in o {
            sc.o_comp[v as usize] = i as u32;
        }
    }
    gfp(g, sub, true, false, true, sc);
    copy_cur(sub, &sc.cur, &mut sc.tmp);
    lfp(g, sub, true, MorRead::Joint, true, None, sc);
    for &v in sub {
        let v = v as usize;
        sc.lo[v] = sc.cur[v];
        sc.t_comp[v] = u32::MAX;
        sc.o_comp[v] = u32::MAX;
    }
    gfp(g, sub, false, false, false, sc);
    copy_cur(sub, &sc.cur, &mut sc.tmp);
    lfp(g, sub, false, MorRead::FromTmp, false, None, sc);
    copy_cur(sub, &sc.cur, &mut sc.tmp);
    gfp(g, sub, false, true, false, sc);
    copy_cur(sub, &sc.cur, &mut sc.hi);
}

/// Marks every undecided parent of a refused node refused.
fn refuse_upward(g: &Bes, refused: &mut [bool], sc: &mut Scratch) {
    sc.queue.clear();
    sc.queue
        .extend((0..refused.len()).filter(|&v| refused[v]).map(|v| v as u32));
    while let Some(w) = sc.queue.pop() {
        for &p in &g.parents[w as usize] {
            let p = p as usize;
            if !refused[p] && sc.lo[p] != sc.hi[p] {
                refused[p] = true;
                sc.queue.push(p as u32);
            }
        }
    }
}

/// Decides `u_set`, in which every tuple cycle has one player's choices only, by one deletion
/// cascade: a node dies when its kind says so, and a tuple cycle dies with every node on it once
/// nothing outside it can feed it.
fn delete_cascade(g: &Bes, u_set: &[u32], t_sccs: &[Vec<u32>], sc: &mut Scratch) {
    sc.queue.clear();
    for &v in u_set {
        let v = v as usize;
        sc.in_sub[v] = true;
        sc.cur[v] = true;
        sc.t_comp[v] = u32::MAX;
    }
    let nt = t_sccs.len();
    let mut cyclic = vec![false; nt];
    let mut broken = vec![true; nt];
    let mut seeds = vec![0u32; nt];
    for (cid, tc) in t_sccs.iter().enumerate() {
        for &v in tc {
            sc.t_comp[v as usize] = cid as u32;
        }
        cyclic[cid] = g.cyclic(tc);
        broken[cid] = !cyclic[cid];
    }
    for (cid, tc) in t_sccs.iter().enumerate() {
        if !cyclic[cid] {
            continue;
        }
        let mut s = 0u32;
        for &v in tc {
            match g.kind(v) {
                Kind::Or => {
                    for &w in g.children(v) {
                        let w = w as usize;
                        let live_outside = if sc.in_sub[w] {
                            sc.t_comp[w] != cid as u32
                        } else {
                            sc.hi[w]
                        };
                        if live_outside {
                            s += 1;
                        }
                    }
                }
                Kind::And | Kind::Mor => {}
                // `tc` is a component with `cyclic` true: two nodes or more, each with a child
                // in it, or one node that is its own child. A constant has no child (`Bes::add`,
                // `Bes::set`, `simplify`).
                Kind::Top | Kind::Bot => unreachable!("a constant node on a tuple cycle"),
            }
        }
        seeds[cid] = s;
    }
    for &v_u32 in u_set {
        let v = v_u32 as usize;
        let need = match g.kind(v_u32) {
            // `u_set` lies in a component with a cycle (step 4 of `decide`), and a constant,
            // with no child, is on no cycle.
            Kind::Top | Kind::Bot => unreachable!("a constant node in a component with a cycle"),
            Kind::Mor | Kind::And => {
                let dead_ext = g
                    .children(v_u32)
                    .iter()
                    .any(|&w| !sc.in_sub[w as usize] && !sc.hi[w as usize]);
                if dead_ext { 0 } else { 1 }
            }
            Kind::Or => g
                .children(v_u32)
                .iter()
                .filter(|&&w| sc.in_sub[w as usize] || sc.hi[w as usize])
                .count() as u32,
        };
        sc.need[v] = need;
        // `need` is 0 only when `v` is an `And` or `Mor` node with a child `w`, or an `Or` node
        // all of whose children `w`, lie outside `u_set` with `hi[w]` false. Each such `w` has
        // `lo[w] == hi[w]`: inside `r_scc` by the filter that made `u_set`; outside it, else
        // `reaches_refused` in `decide` held and `r_scc` was refused, not cascaded. So
        // `lo[w] == hi[w] == false`, and no write to `lo` or `hi` falls between the last
        // `bounds` over `v` (on `r_scc`, or on the whole component when `r_scc` is all of it)
        // and this call: the components are taken bottom up and each is finished before the
        // next, and `refusal` writes neither. In that `bounds`:
        // - `hi[v]` is the last greatest fixed point (`narrow` false, reading `hi` outside its
        //   `sub`). At its fixed point a live `And`/`Mor` has every child live and a live `Or`
        //   one child live, a child inside `sub` read as its own value (its `hi`), outside as
        //   `hi`. So `hi[v]` is false.
        // - `lo[v]` is the least fixed point seeded by the narrowed greatest one (`tmp`), both
        //   reading `lo` outside `sub`. In the narrowed pass a cut edge reads as not inhabited,
        //   so the children `w` read false there too and `tmp[v]` is false; in the least pass
        //   an `And`/`Mor` with a child never set, or an `Or` with no child set, is never set.
        //   So `lo[v]` is false.
        // Then `lo[v] == hi[v]` and `v` is not in `u_set`: `need` is at least 1, and a node of
        // `u_set` dies only when a tuple cycle loses its last seed, below.
        if need == 0 {
            unreachable!("a node of `u_set` has a child that may be inhabited")
        }
    }
    let kill = |sc: &mut Scratch, tc: &[u32]| {
        for &u in tc {
            if sc.cur[u as usize] {
                sc.cur[u as usize] = false;
                sc.need[u as usize] = 0;
                sc.queue.push(u);
            }
        }
    };
    for (cid, tc) in t_sccs.iter().enumerate() {
        if cyclic[cid] && !broken[cid] && seeds[cid] == 0 {
            broken[cid] = true;
            kill(sc, tc);
        }
    }
    while let Some(w) = sc.queue.pop() {
        // A node of a tuple component died; if the component is a simple cycle, that breaks it
        // into a chain. Every queued node has a component: `t_sccs` is `components` of `u_set`
        // (Tarjan from every node of `u_set`, so each lies in one), the loop above set
        // `t_comp` from it, and only nodes of `u_set` are queued (`kill` of a component, and a
        // parent `p` with `in_sub[p]`, which holds of `u_set` alone here). By the same proof
        // each such parent `p` has a component, so `cp` below is never `u32::MAX`.
        let cw = sc.t_comp[w as usize];
        if cw == u32::MAX {
            unreachable!("a node of `u_set` outside every tuple component")
        }
        broken[cw as usize] = true;
        for &p_u32 in &g.parents[w as usize] {
            let p = p_u32 as usize;
            if !sc.in_sub[p] {
                continue;
            }
            let cp = sc.t_comp[p];
            if g.kind[p] == Kind::Or && cp != cw && !broken[cp as usize] {
                seeds[cp as usize] -= 1;
                if seeds[cp as usize] == 0 {
                    broken[cp as usize] = true;
                    kill(sc, &t_sccs[cp as usize]);
                }
            }
            if sc.cur[p] && sc.need[p] > 0 && sc.need[p] != u32::MAX {
                sc.need[p] -= 1;
                if sc.need[p] == 0 {
                    sc.cur[p] = false;
                    sc.queue.push(p_u32);
                }
            }
        }
    }
    for &v in u_set {
        let v = v as usize;
        sc.lo[v] = sc.cur[v];
        sc.hi[v] = sc.cur[v];
        sc.in_sub[v] = false;
        sc.t_comp[v] = u32::MAX;
    }
}

/// The first cyclic tuple component of `u_set` with cyclomatic number 2 or more and an `And`
/// node with two distinct undecided children, if any. Distinct children are counted with
/// `stamp`, in time linear in the edges.
// Complexity tradeoff (COMPLEXITY.md K26): the naive count searches a list of the children
// seen, O(n²) on a node of `n` children (control `exring:6:1`: 36.80 times at 8n, limit 24).
// Used: one stamp per node, advanced per parent, so a child is counted when its mark is not
// the current stamp, O(nodes + edges) in all. Tradeoff: one `u32` per node held for the whole
// decision. The refusal itself is the tradeoff at `group_verdicts` (`Refusal::Group`): a
// component of that shape would need a general game solver, quadratic or worse in it.
fn refusal(
    g: &Bes,
    u_set: &[u32],
    t_sccs: &[Vec<u32>],
    gates: usize,
    sc: &mut Scratch,
    stamp: &mut Stamp,
) -> Option<Refusal> {
    sc.mark(u_set, true);
    let mut found: Option<Refusal> = None;
    // Every tuple cycle is read, not only the first refused one, so the tuples named do not
    // depend on the order the cycles are found in; still one pass over the edges.
    let mut tuples = Vec::new();
    for (cid, tc) in t_sccs.iter().enumerate() {
        if !g.cyclic(tc) {
            continue;
        }
        for &v in tc {
            sc.t_comp[v as usize] = cid as u32;
        }
        let (mut internal_edges, mut branching_and, mut branching_or) = (0, 0, 0);
        let branching = tuples.len();
        for &v in tc {
            stamp.advance();
            let (mut internal, mut undecided) = (0usize, 0usize);
            for &w in g.children(v) {
                let w = w as usize;
                if sc.in_sub[w] && stamp.first(w) {
                    undecided += 1;
                    if sc.t_comp[w] == cid as u32 {
                        internal += 1;
                    }
                }
            }
            internal_edges += internal;
            if undecided >= 2 {
                match g.kind(v) {
                    Kind::And => {
                        branching_and += 1;
                        tuples.push(v);
                    }
                    Kind::Or => branching_or += 1,
                    // A `Mor` node has one child and a constant none (`Bes::add`, `simplify`).
                    Kind::Mor | Kind::Top | Kind::Bot => {
                        unreachable!("two children of a morphism or constant node")
                    }
                }
            }
        }
        let cyclomatic = internal_edges.saturating_sub(tc.len()) + 1;
        let shaped = cyclomatic >= 2
            && branching_and >= 1
            && !one_cycle_but_union_chords(g, tc, cid as u32, sc, stamp);
        for &v in tc {
            sc.t_comp[v as usize] = u32::MAX;
        }
        if !shaped {
            tuples.truncate(branching);
        } else if found.is_none() {
            found = Some(Refusal {
                component: Vec::new(),
                tuples: Vec::new(),
                node: *tc.iter().min().expect("a component has a node"),
                nodes: tc.len(),
                internal_edges,
                cyclomatic,
                branching_and,
                branching_or: branching_or.max(1),
                gates,
            });
        }
    }
    sc.mark(u_set, false);
    found.map(|r| {
        let mut component = u_set.to_vec();
        component.sort_unstable();
        tuples.sort_unstable();
        Refusal {
            component,
            tuples,
            ..r
        }
    })
}

/// Whether the tuple cycle `tc` (component `cid` in `sc.t_comp`, the undecided nodes in
/// `sc.in_sub`) is one simple cycle `C` through all its nodes once each edge from an `Or` node
/// `v` to a node `w` is dropped that `v`'s successor on `C` reaches along `C` through `Or` nodes
/// alone (item GROUP-cycle-dup-across). Such an edge is a union arm that another arm of the same
/// union holds through unions, `A | B` with `B = A | …`: from `v`, the player choosing at `Or`
/// nodes can take the successor and follow `C` to `w` with no morphism edge and no choice of
/// the other player on the way, so every game answer is the same without the edge, and the
/// component is the simple cycle the deletion cascade decides.
///
/// If such a `C` exists, `v`'s successor reaches each of `v`'s other children through `Or`
/// edges, so it comes before them in every topological order of the `Or` edges; the successor
/// is therefore the earliest child in one such order, and the test checks that this choice
/// closes one cycle and that each other child lies within the run of `Or` nodes that follows
/// it. A component whose `Or` edges have a cycle is not taken.
// Complexity tradeoff: the naive form is the transitive reduction of the `Or` edges before
// counting cycles, O(nodes * edges) (a reachability search from each node). Used: the test only
// asks whether the reduced component is one simple cycle, which needs one topological order of
// the `Or` edges (Kahn's algorithm, `zed_graph::kahn`; A. B. Kahn, "Topological sorting of
// large networks", Comm. ACM 5(11):558-562, 1962, doi:10.1145/368996.369025, Crossref checked
// 2026-11-20, text not obtained, the method from memory) and one walk around the cycle,
// O(nodes + edges) of `tc`.
// Tradeoff: a component that the reduction would leave with fewer cycles, but more than one, is
// still refused; its refusal does not change, since the refusal asks for two or more.
fn one_cycle_but_union_chords(
    g: &Bes,
    tc: &[u32],
    cid: u32,
    sc: &mut Scratch,
    stamp: &mut Stamp,
) -> bool {
    let n = tc.len();
    for (i, &v) in tc.iter().enumerate() {
        sc.local[v as usize] = i as u32;
    }
    // Each node's distinct children inside `tc`, by their place in `tc`.
    let (mut at, mut inner) = (Vec::with_capacity(n + 1), Vec::new());
    at.push(0);
    let mut indegree = vec![0usize; n];
    let mut fits = true;
    for &v in tc {
        stamp.advance();
        let start = inner.len();
        for &w in g.children(v) {
            if sc.in_sub[w as usize] && sc.t_comp[w as usize] == cid && stamp.first(w as usize) {
                inner.push(sc.local[w as usize]);
            }
        }
        if g.kind(v) == Kind::Or {
            for &j in &inner[start..] {
                indegree[j as usize] += 1;
            }
        } else if inner.len() - start != 1 {
            fits = false;
        }
        at.push(inner.len());
    }
    for &v in tc {
        sc.local[v as usize] = u32::MAX;
    }
    if !fits {
        return false;
    }
    let is_or = |i: usize| g.kind(tc[i]) == Kind::Or;
    // A topological order of the `Or` edges, by Kahn's algorithm, last ready first.
    let mut rank = vec![u32::MAX; n];
    let mut ready: Vec<usize> = zed_graph::sources(&indegree).collect();
    let mut ranked = 0u32;
    let placed = zed_graph::kahn(
        &mut indegree,
        &mut ready,
        // Only an `Or` node's edges are counted in `indegree`.
        |i| {
            let end = if is_or(i) { at[i + 1] } else { at[i] };
            inner[at[i]..end].iter().map(|&j| j as usize)
        },
        |i| {
            rank[i] = ranked;
            ranked += 1;
        },
    );
    if placed != n {
        return false;
    }
    let next: Vec<usize> = (0..n)
        .map(|i| {
            let kids = &inner[at[i]..at[i + 1]];
            *kids
                .iter()
                .min_by_key(|&&j| rank[j as usize])
                .expect("a node of a cycle has a child in it") as usize
        })
        .collect();
    // The successors close one cycle through every node: walk it from node 0.
    let mut place = vec![u32::MAX; n];
    let mut i = 0;
    for step in 0..n {
        if place[i] != u32::MAX {
            return false;
        }
        place[i] = step as u32;
        i = next[i];
    }
    if i != 0 {
        return false;
    }
    // From each place, how many steps along the cycle to the first node that is not `Or`; the
    // `Or` edges have no cycle, so there is one.
    let order: Vec<usize> = {
        let mut order = vec![0; n];
        for (i, &p) in place.iter().enumerate() {
            order[p as usize] = i;
        }
        order
    };
    let stop = (0..n)
        .find(|&p| !is_or(order[p]))
        .expect("an all-`Or` cycle is an `Or` cycle");
    let mut ahead = vec![0usize; n];
    for k in 1..n {
        let p = (stop + n - k) % n;
        ahead[p] = if is_or(order[p]) {
            ahead[(p + 1) % n] + 1
        } else {
            0
        };
    }
    (0..n).filter(|&i| is_or(i)).all(|i| {
        let s = place[next[i]] as usize;
        inner[at[i]..at[i + 1]].iter().all(|&j| {
            let d = (place[j as usize] as usize + n - s) % n;
            d <= ahead[s]
        })
    })
}

/// Drops edges no least fixed point can use: an `And` node with itself or an `And` parent of it
/// as a child is not inhabited, and an `Or` node's edges to itself and to its `And` parents are
/// dropped. Time linear in nodes and edges.
fn simplify(g: &Bes, in_sub: &mut [bool]) -> Bes {
    let n = g.len();
    let mut h: Bes = Bes {
        kind: g.kind.clone(),
        children: vec![Vec::new(); n],
        parents: vec![Vec::new(); n],
    };
    for v in 0..n {
        match g.kind[v] {
            Kind::And | Kind::Or => {
                for &u in &g.parents[v] {
                    in_sub[u as usize] = true;
                }
                let back = |w: u32| {
                    w as usize == v || (g.kind[w as usize] == Kind::And && in_sub[w as usize])
                };
                if g.kind[v] == Kind::And {
                    if g.children[v].iter().any(|&w| back(w)) {
                        h.kind[v] = Kind::Bot;
                    } else {
                        h.children[v].clone_from(&g.children[v]);
                    }
                } else {
                    h.children[v].extend(g.children[v].iter().copied().filter(|&w| !back(w)));
                    if h.children[v].is_empty() {
                        h.kind[v] = Kind::Bot;
                    }
                }
                for &u in &g.parents[v] {
                    in_sub[u as usize] = false;
                }
            }
            Kind::Mor | Kind::Top | Kind::Bot => h.children[v].clone_from(&g.children[v]),
        }
    }
    h.seal();
    h
}

/// Every node's answer, in time linear in nodes and edges (module docs). `g` must be sealed.
///
/// Every node answered [`Answer::Refused`] reaches a node of some refusal's `component` along
/// edges of `raw` whose ends are all answered `Refused` (PROOF-refused-469-undecided-child; read
/// by `empty::refused::refused_site`; checked on the random systems of the tests by
/// `refused_nodes_reach_a_refusal`). Proof, by induction over the order in which
/// the loop below fixes a node's answer. The answer is `Refused` when `refused[v]` or
/// `lo[v] != hi[v]`. `refused` is only ever set, and `lo` and `hi` of a node are written only
/// while its own component, or a part of it, is processed (`settle`, `bounds` and the passes
/// write them for their `sub` alone), so an answer fixed is final. The components come
/// children first, and so do the parts (`r_scc`) of one component, so every child of a node
/// lies in its part or in a part or component already done. The cases that make a node
/// `Refused`:
/// 1. `settle` of a whole component leaves `lo[v] != hi[v]`. Both of its passes end at a
///    fixed point of the same equations (an `Or` node holds when a child does, an `And` or
///    `Mor` node when all do, a `Mor` node whose child is in the component never under
///    `MorRead::False`, a constant always or never); they differ only in reading `lo` or `hi`
///    outside the component. Take `lfp` and the pass `R` in which `v` holds: `v` was set when
///    the last of the children that made it hold was set before it in `R` (an `Or` node by one
///    child, an `And` or `Mor` node by all), or at the start by a child outside. In the other
///    pass `v` fails, so one of those children `w` fails there too: an `Or` node fails only
///    with every child failing, an `And` node only with some child failing. So `w` differs
///    between the passes and holds in `R`, and if it is inside, it was set earlier in `R`.
///    Repeating, the set order of `R` falls at each step, so the chain ends at a child outside
///    the component with `lo != hi`, in a component done before. For `gfp` the same holds with
///    the order in which nodes die in the pass where `v` fails (an `Or` node dies when its last
///    child has died, an `And` or `Mor` node when one has). Every node on the chain is
///    `Refused`.
/// 2. `reaches_refused`: every node of `r_scc` is refused. `r_scc` is strongly connected, and
///    one of its nodes has a child outside it that is refused or has `lo != hi`, in a part or
///    component done before, so `Refused` for good.
/// 3. `refusal` returns `Some`: every node of `r_scc` is refused, and `r_scc` is strongly
///    connected, so each reaches a node of `u_set`, which is the refusal's `component`. This is
///    the base case.
/// 4. `refuse_upward` refuses `p`, a parent of a node refused before it.
///
/// No other step leaves `lo != hi`. A part not refused for `reaches_refused` has no child
/// outside it with `lo != hi`, and within it the nodes outside `u_set` have `lo == hi` by
/// `u_set`'s definition, so `settle` of `u_set` reads the same values outside `u_set` in its
/// two passes and gives the same answer twice; the pass for one morphism and the deletion
/// cascade set `lo` and `hi` alike. So every case but the third gives a `Refused` child, or a
/// path within a strongly connected set to one, whose answer was fixed earlier. The paths
/// follow edges of `simplify`'s copy, which keeps a subset of the edges of `raw`.
pub fn decide(raw: &Bes) -> Decision {
    let n = raw.len();
    let mut sc = Scratch::new(n);
    let mut stamp = Stamp::new(n);
    let g = &simplify(raw, &mut sc.in_sub);
    let all: Vec<u32> = (0..n as u32).collect();
    let mut refused = vec![false; n];
    let mut refusals = Vec::new();

    for scc in &components(g, &all, Edges::All, &mut sc.local) {
        sc.mark(scc, true);
        let has_mor = scc
            .iter()
            .any(|&v| g.kind(v) == Kind::Mor && sc.in_sub[g.children(v)[0] as usize]);
        sc.mark(scc, false);
        let has_tup = has_tuple_cycle(g, scc, &mut sc.local);
        if !has_mor || !has_tup {
            settle(g, scc, has_tup, &mut sc);
            continue;
        }
        bounds(g, scc, &mut sc);
        let undecided: Vec<u32> = scc
            .iter()
            .copied()
            .filter(|&v| sc.lo[v as usize] != sc.hi[v as usize])
            .collect();
        if undecided.is_empty() {
            continue;
        }
        for r_scc in &components(g, &undecided, Edges::All, &mut sc.local) {
            sc.mark(r_scc, true);
            let reaches_refused = r_scc.iter().any(|&v| {
                g.children(v).iter().any(|&w| {
                    let w = w as usize;
                    refused[w] || (!sc.in_sub[w] && sc.lo[w] != sc.hi[w])
                })
            });
            sc.mark(r_scc, false);
            if reaches_refused {
                for &v in r_scc {
                    refused[v as usize] = true;
                }
                continue;
            }
            if r_scc.len() < scc.len() {
                bounds(g, r_scc, &mut sc);
            }
            let u_set: Vec<u32> = r_scc
                .iter()
                .copied()
                .filter(|&v| sc.lo[v as usize] != sc.hi[v as usize])
                .collect();
            if u_set.is_empty() {
                continue;
            }
            sc.mark(&u_set, true);
            let mors: Vec<u32> = u_set
                .iter()
                .copied()
                .filter(|&v| g.kind(v) == Kind::Mor && sc.in_sub[g.children(v)[0] as usize])
                .collect();
            sc.mark(&u_set, false);
            let t_sccs = components(g, &u_set, Edges::Tuple, &mut sc.local);
            let tuple_cycle = t_sccs.iter().any(|tc| g.cyclic(tc));
            if !tuple_cycle || mors.is_empty() {
                settle(g, &u_set, tuple_cycle, &mut sc);
                continue;
            }
            if let [m0] = mors[..] {
                // One morphism inside: assume its value type inhabited; if the least fixed
                // point then inhabits it, that is the answer, else the least fixed point with
                // it not inhabited is.
                let w0 = g.children(m0)[0] as usize;
                lfp(g, &u_set, true, MorRead::False, false, Some(m0), &mut sc);
                if !sc.cur[w0] {
                    #[cfg(test)]
                    SECOND_PASSES.with(|c| c.set(c.get() + 1));
                    lfp(g, &u_set, true, MorRead::False, false, None, &mut sc);
                }
                for &v in &u_set {
                    let v = v as usize;
                    sc.lo[v] = sc.cur[v];
                    sc.hi[v] = sc.cur[v];
                }
                continue;
            }
            match refusal(g, &u_set, &t_sccs, mors.len(), &mut sc, &mut stamp) {
                Some(r) => {
                    for &v in r_scc {
                        refused[v as usize] = true;
                    }
                    refusals.push(r);
                }
                None => delete_cascade(g, &u_set, &t_sccs, &mut sc),
            }
        }
    }
    refuse_upward(g, &mut refused, &mut sc);
    let answers = (0..n)
        .map(|v| {
            if refused[v] || sc.lo[v] != sc.hi[v] {
                Answer::Refused
            } else if sc.lo[v] {
                Answer::Inhabited
            } else {
                Answer::Empty
            }
        })
        .collect();
    Decision { answers, refusals }
}

#[cfg(test)]
thread_local! {
    /// How often this thread's `decide` took the second least fixed point of the one-`Mor`
    /// step, so the random test can check that its draws still reach it.
    static SECOND_PASSES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
mod tests {
    use super::{
        Answer, Bes, Edges, Kind, Scratch, Stamp, components, decide, delete_cascade, gfp,
    };

    /// After 2^32 - 1 advances the marks are cleared: a node marked under the first stamp is
    /// seen fresh again under the stamp of the same number (item TEST-types-unreached-paths;
    /// the count is set here, since advancing it 2^32 times is no correctness test).
    #[test]
    fn a_stamp_at_its_last_value_clears_the_marks_when_advanced() {
        let mut s = Stamp::new(2);
        s.advance();
        assert!(s.first(1));
        s.cur = u32::MAX;
        assert!(s.first(0));
        assert!(!s.first(0));
        s.advance();
        assert_eq!(s.cur, 1);
        assert!(s.first(0));
        assert!(s.first(1));
    }

    /// The answers by the game the module comment describes, found the slow way: a node is
    /// inhabited when the player choosing a child of each `Or` node can keep every play from
    /// a `Bot` node, an `Or` node with no child, and an infinite play that passes `Mor` nodes
    /// only finitely often (a Büchi game with the `Mor` nodes accepting), against the player
    /// choosing a child of each `And` node. Nested fixed points `νZ. μY. (Mor ∧ pre Z) ∨ pre Y`,
    /// `O(n^2 (n + m))`.
    fn by_the_game(g: &Bes) -> Vec<bool> {
        let n = g.len();
        let pre = |s: &[bool], v: usize| match g.kind[v] {
            Kind::Top => true,
            Kind::Bot => false,
            Kind::Or => g.children[v].iter().any(|&w| s[w as usize]),
            Kind::And | Kind::Mor => g.children[v].iter().all(|&w| s[w as usize]),
        };
        let mut z = vec![true; n];
        loop {
            let mut y = vec![false; n];
            loop {
                let next: Vec<bool> = (0..n)
                    .map(|v| (g.kind[v] == Kind::Mor && pre(&z, v)) || pre(&y, v))
                    .collect();
                if next == y {
                    break;
                }
                y = next;
            }
            if y == z {
                return z;
            }
            z = y;
        }
    }

    /// Item TEST-kernel-unreached-paths-4: `decide`, on systems drawn at random, gives each
    /// node it does not refuse the answer of the game ([`by_the_game`]). Draws of 4 to 9
    /// nodes, mostly `Or` and `And` with one to three children and a few `Mor`, reach the
    /// deletion cascade of step 4 (`delete_cascade`) as well as the other steps.
    /// Item TEST-kernel-unreached-paths-4 (`decide`, step 4 with one `Mor` node `m0`): a
    /// system where assuming `m0` inhabited does not inhabit its child, so the second least
    /// fixed point (with `m0` not inhabited) gives the answer. Found by a random search over
    /// about 3.6 million draws of 4 to 43 nodes with few `Mor` nodes; the 40,000 draws of
    /// `decide_agrees_with_the_game_on_systems_drawn_at_random` never reach that pass.
    #[test]
    fn one_morphism_whose_assumption_fails_takes_the_second_least_fixed_point() {
        use Kind::{And as A, Bot as B, Mor as M, Or as O};
        let nodes: [(Kind, &[u32]); 20] = [
            (A, &[15, 5]),
            (A, &[12, 15, 11]),
            (A, &[17, 0, 3]),
            (A, &[5, 7, 16]),
            (O, &[16]),
            (O, &[19, 4, 17]),
            (O, &[3]),
            (O, &[12]),
            (A, &[17]),
            (O, &[14]),
            (O, &[9]),
            (M, &[2]),
            (O, &[18, 7, 13]),
            (B, &[]),
            (A, &[10, 15]),
            (M, &[7]),
            (A, &[19, 9, 1]),
            (A, &[0]),
            (M, &[17]),
            (M, &[11]),
        ];
        let mut g = Bes::new();
        for _ in &nodes {
            g.add(Kind::Bot, vec![]);
        }
        for (v, (kind, kids)) in nodes.iter().enumerate() {
            g.set(v as u32, *kind, kids.to_vec());
        }
        g.seal();
        let want = by_the_game(&g);
        let got = decide(&g);
        for v in 0..nodes.len() {
            assert_ne!(got.answers[v], Answer::Refused, "node {v}");
            assert_eq!(got.answers[v] == Answer::Inhabited, want[v], "node {v}");
        }
    }

    /// The parent walk of the narrowed `gfp` skips a cut edge: `w` dies, but `p` never counted
    /// its cut edge to `w`, so `p` stays inhabited through `x`. `decide` alone does not show
    /// it (the random test passes without the skip): a `lo` that is too small is still sound,
    /// and the later passes recover what it lost.
    #[test]
    fn the_narrowed_greatest_fixed_point_does_not_count_a_cut_edge_twice() {
        let mut g = Bes::new();
        let (p, w) = (g.add(Kind::Bot, vec![]), g.add(Kind::Bot, vec![]));
        let x = g.add(Kind::Top, vec![]);
        g.set(p, Kind::Or, vec![w, x]);
        g.set(w, Kind::Or, vec![p]);
        g.seal();
        let sub = [p, w];
        let mut sc = Scratch::new(g.len());
        for (edges, comp) in [(Edges::Tuple, 0), (Edges::OrOr, 1)] {
            for (i, c) in components(&g, &sub, edges, &mut sc.local)
                .iter()
                .enumerate()
            {
                for &v in c {
                    let at = if comp == 0 {
                        &mut sc.t_comp
                    } else {
                        &mut sc.o_comp
                    };
                    at[v as usize] = i as u32;
                }
            }
        }
        assert_eq!(sc.t_comp[p as usize], sc.t_comp[w as usize]);
        assert_eq!(sc.o_comp[p as usize], sc.o_comp[w as usize]);
        sc.lo[x as usize] = true;
        gfp(&g, &sub, true, false, true, &mut sc);
        assert!(sc.cur[p as usize], "p reads x, which holds");
        assert!(!sc.cur[w as usize], "w's one edge is cut");
    }

    /// The narrowed `gfp` cuts no edge out of a `Mor` node. Edges out of `Mor` nodes are not
    /// followed in the tuple graph, so a `Mor` node is alone in its tuple component, and the
    /// edge to its child is inside that component only when the child is the node itself
    /// (`T = int -> T`). Item TEST-kernel-unreached-paths-4 (kernel12): no system drawn reaches
    /// this arm. The game agrees that the node is inhabited.
    #[test]
    fn the_narrowed_greatest_fixed_point_keeps_the_edge_of_a_morphism_to_itself() {
        let mut g = Bes::new();
        let m = g.add(Kind::Bot, vec![]);
        g.set(m, Kind::Mor, vec![m]);
        g.seal();
        let sub = [m];
        let mut sc = Scratch::new(g.len());
        for (i, c) in components(&g, &sub, Edges::Tuple, &mut sc.local)
            .iter()
            .enumerate()
        {
            for &v in c {
                sc.t_comp[v as usize] = i as u32;
            }
        }
        gfp(&g, &sub, true, false, true, &mut sc);
        assert!(sc.cur[m as usize], "the edge of `m` to itself is not cut");
        assert!(by_the_game(&g)[m as usize]);
        assert_eq!(decide(&g).answers[m as usize], Answer::Inhabited);
    }

    /// The cascade of `delete_cascade`, called directly: no system drawn for `decide` makes it
    /// kill a node (every tuple cycle of the `u_set`s drawn has a seed). The `Or` cycle `c, d`
    /// has no way out and dies at the start; the `Or` cycle `a, b` has one seed, `a`'s edge to
    /// `c`, and dies when `c` does; `e`'s one child in `u_set` is `a`, so it dies after it. The
    /// game agrees that no node is inhabited.
    #[test]
    fn a_tuple_cycle_dies_when_its_last_seed_does() {
        let mut g = Bes::new();
        let [a, b, c, d, e] = [(); 5].map(|_| g.add(Kind::Bot, vec![]));
        let x = g.add(Kind::Bot, vec![]);
        g.set(a, Kind::Or, vec![b, c]);
        g.set(b, Kind::Or, vec![a]);
        g.set(c, Kind::Or, vec![d]);
        g.set(d, Kind::Or, vec![c]);
        g.set(e, Kind::Or, vec![a, x]);
        g.seal();
        let mut sc = Scratch::new(g.len());
        delete_cascade(
            &g,
            &[a, b, c, d, e],
            &[vec![c, d], vec![a, b], vec![e]],
            &mut sc,
        );
        let want = by_the_game(&g);
        for v in [a, b, c, d, e] {
            let v = v as usize;
            assert_eq!(sc.lo[v], want[v], "lo of node {v}");
            assert_eq!(sc.hi[v], want[v], "hi of node {v}");
        }
    }

    /// The cascade's other branches, called directly as above. Around the cycles `c, d` and
    /// `a, b` of that test, which die in the same way: `p, q` is an `Or` cycle with two seeds,
    /// `a` and the constant `y` outside, so it loses one when `a` dies and lives; `h` is an
    /// `Or` of `a` and `y`, whose need falls from 2 to 1 and which lives; `s, r` is a cycle
    /// with the `And` node `s` of `r` and `a` and the `Or` node `r` of `s` and `a`, and `s` (a
    /// parent of `a` before `r`) dies by its need before `r` takes the cycle's last seed, so the
    /// kill of the cycle meets `s` already dead; `t`, an `Or` of `s` and `y`, must see `s` die
    /// once. The game says `p`, `q`, `h` and `t` are inhabited and the rest not.
    #[test]
    fn a_cascade_passes_over_the_dead_and_keeps_what_still_has_a_seed_or_a_child() {
        let mut g = Bes::new();
        let [a, b, c, d, s, r, t, h, p, q] = [(); 10].map(|_| g.add(Kind::Bot, vec![]));
        let y = g.add(Kind::Top, vec![]);
        g.set(a, Kind::Or, vec![b, c]);
        g.set(b, Kind::Or, vec![a]);
        g.set(c, Kind::Or, vec![d]);
        g.set(d, Kind::Or, vec![c]);
        g.set(s, Kind::And, vec![r, a]);
        g.set(r, Kind::Or, vec![s, a]);
        g.set(t, Kind::Or, vec![s, y]);
        g.set(h, Kind::Or, vec![a, y]);
        g.set(p, Kind::Or, vec![q, a, y]);
        g.set(q, Kind::Or, vec![p]);
        g.seal();
        let mut sc = Scratch::new(g.len());
        sc.lo[y as usize] = true;
        sc.hi[y as usize] = true;
        delete_cascade(
            &g,
            &[a, b, c, d, s, r, t, h, p, q],
            &[
                vec![c, d],
                vec![a, b],
                vec![s, r],
                vec![t],
                vec![h],
                vec![p, q],
            ],
            &mut sc,
        );
        let want = by_the_game(&g);
        for v in [a, b, c, d, s, r, t, h, p, q] {
            let v = v as usize;
            assert_eq!(sc.lo[v], want[v], "lo of node {v}");
            assert_eq!(sc.hi[v], want[v], "hi of node {v}");
        }
        assert_eq!(
            [p, q, h, t].map(|v| want[v as usize]),
            [true; 4],
            "the nodes kept alive are inhabited"
        );
    }

    /// Draws of the wide shape in `decide_agrees_with_the_game_on_systems_drawn_at_random`.
    /// The draws are fixed by the seed; the only two that reach the one-`Mor` step's second
    /// least fixed point are wide draws 89,504 and 413,455, and the 40,000 small draws reach
    /// every other path. So the count stops a little after the second (it was 600,000, which
    /// took up to 19.6 s alone at load 40 against the test's 24 s limit, `decide` 6 s of
    /// every 9), and the draws are checked in two tests of about 6 s each (load 52 to 68),
    /// each asserting that its half still reaches the pass.
    const WIDE_DRAWS: u64 = 420_000;

    /// The draws of `decide_agrees_with_the_game_on_systems_drawn_at_random` are numbered
    /// from 0, the 40,000 small ones first; this one starts the second half of the test, which
    /// holds the second draw that reaches the second pass (wide draw 413,455, so 453,455).
    const SECOND_HALF: u64 = 250_000;

    #[test]
    fn decide_agrees_with_the_game_on_systems_drawn_at_random() {
        draws_agree_with_the_game(0..SECOND_HALF);
    }

    /// The second half of the draws, a test of its own so each half stays well inside the
    /// time limit of one test.
    #[test]
    fn decide_agrees_with_the_game_on_systems_drawn_at_random_second_half() {
        draws_agree_with_the_game(SECOND_HALF..u64::MAX);
    }

    /// Item PROOF-refused-469-undecided-child: every node `decide` refuses reaches a node of a
    /// refusal's `component` along edges of `g` between refused nodes (the claim proved at
    /// `decide`). Walks back from the components along parents, through refused nodes only,
    /// in time linear in the nodes and edges.
    fn refused_nodes_reach_a_refusal(g: &Bes, got: &super::Decision) {
        let refused = |v: u32| got.answers[v as usize] == Answer::Refused;
        let mut reaches = vec![false; g.len()];
        let mut stack: Vec<u32> = Vec::new();
        for r in &got.refusals {
            assert!(!r.tuples.is_empty(), "a refusal lists a tuple: {r:?}");
            for &v in &r.component {
                assert!(refused(v), "node {v} of a refusal's component is refused");
                if !reaches[v as usize] {
                    reaches[v as usize] = true;
                    stack.push(v);
                }
            }
        }
        while let Some(w) = stack.pop() {
            for &p in g.parents(w) {
                if refused(p) && !reaches[p as usize] {
                    reaches[p as usize] = true;
                    stack.push(p);
                }
            }
        }
        for v in 0..g.len() as u32 {
            assert!(
                !refused(v) || reaches[v as usize],
                "refused node {v} reaches no refusal along refused nodes in {g:?}"
            );
        }
    }

    /// Draws every system in turn, so the seed reaches each draw the same way, and checks
    /// `decide` against the game on the draws numbered in `checked`; asserts that those
    /// draws take the second least fixed point of the one-`Mor` step at least once.
    fn draws_agree_with_the_game(checked: std::ops::Range<u64>) {
        // xorshift64 from a fixed seed, kept: the draws numbered in `checked`, and the draw
        // that takes the second least fixed point, are those of this stream.
        let mut rng = crate::seed::Xorshift64::new(0x9e37_79b9_7f4a_7c15);
        let mut next = |k: u64| rng.below(k);
        let (mut decided, mut refused) = (0, 0);
        let second_before = super::SECOND_PASSES.with(std::cell::Cell::get);
        // Small systems with many `Mor` nodes, then wide ones with few: only the second
        // reach the second least fixed point of the one-`Mor` step (see
        // `one_morphism_whose_assumption_fails_takes_the_second_least_fixed_point`).
        let mut index = 0;
        for (draws, span, wide) in [(40_000, 10, false), (WIDE_DRAWS, 40, true)] {
            for _ in 0..draws {
                index += 1;
                let n = 3 + next(span) as u32;
                let mors = 1 + next(5);
                let mut g = Bes::new();
                for _ in 0..n {
                    g.add(Kind::Bot, vec![]);
                }
                for v in 0..n {
                    let kind = match (wide, next(if wide { 40 } else { 32 })) {
                        (false, 0) => Kind::Top,
                        (_, 0) | (false, 1) => Kind::Bot,
                        (false, 2..=9) => Kind::Mor,
                        (true, r) if r <= mors => Kind::Mor,
                        (false, 10..=20) | (true, 1..=21) => Kind::Or,
                        _ => Kind::And,
                    };
                    let children = match kind {
                        Kind::Top | Kind::Bot => vec![],
                        Kind::Mor => vec![next(u64::from(n)) as u32],
                        _ => (0..1 + next(3))
                            .map(|_| next(u64::from(n)) as u32)
                            .collect(),
                    };
                    g.set(v, kind, children);
                }
                if !checked.contains(&(index - 1)) {
                    continue;
                }
                g.seal();
                let want = by_the_game(&g);
                let got = decide(&g);
                refused_nodes_reach_a_refusal(&g, &got);
                for v in 0..n as usize {
                    match got.answers[v] {
                        Answer::Refused => refused += 1,
                        a => {
                            decided += 1;
                            assert_eq!(a == Answer::Inhabited, want[v], "node {v} of {g:?}");
                        }
                    }
                }
            }
        }
        let second = super::SECOND_PASSES.with(std::cell::Cell::get) - second_before;
        assert!(
            second >= 1,
            "the second least fixed point of the one-Mor step taken {second} times, want 1"
        );
        assert!(
            decided > 10 * refused,
            "{decided} decided, {refused} refused"
        );
    }
}
