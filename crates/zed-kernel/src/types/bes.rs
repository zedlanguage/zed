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
//!    whose answer depends on a refused one.
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

    /// Adds a node and returns its number. A `Mor` node has exactly one child.
    pub fn add(&mut self, kind: Kind, children: Vec<u32>) -> u32 {
        assert!(
            kind != Kind::Mor || children.len() == 1,
            "a morphism node has its value type as its one child"
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
/// around it and an `And` node that needs two undecided children.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Refusal {
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

/// The strongly connected components of `sub` along `edges`, children first, by Tarjan's
/// algorithm with an explicit stack.
fn components(g: &Bes, sub: &[u32], edges: Edges, local: &mut [u32]) -> Vec<Vec<u32>> {
    let k = sub.len();
    for (i, &v) in sub.iter().enumerate() {
        local[v as usize] = i as u32;
    }
    let mut index = vec![0u32; k];
    let mut low = vec![0u32; k];
    let mut on = vec![false; k];
    let mut t = 1u32;
    let mut stack: Vec<usize> = Vec::with_capacity(k);
    let mut calls: Vec<(usize, usize)> = Vec::with_capacity(k);
    let mut out: Vec<Vec<u32>> = Vec::new();
    let follows = |u: u32| match edges {
        Edges::All => true,
        Edges::Tuple => g.kind(u) != Kind::Mor,
        Edges::OrOr => g.kind(u) == Kind::Or,
    };
    for r in 0..k {
        if index[r] != 0 {
            continue;
        }
        index[r] = t;
        low[r] = t;
        t += 1;
        stack.push(r);
        on[r] = true;
        calls.push((r, 0));
        while let Some(&mut (u_loc, ref mut i)) = calls.last_mut() {
            let u = sub[u_loc];
            let succ: &[u32] = if follows(u) { g.children(u) } else { &[] };
            if *i < succ.len() {
                let w = succ[*i];
                *i += 1;
                if edges == Edges::OrOr && g.kind(w) != Kind::Or {
                    continue;
                }
                let w_loc = local[w as usize];
                if w_loc == u32::MAX {
                    continue;
                }
                let w_loc = w_loc as usize;
                if index[w_loc] == 0 {
                    index[w_loc] = t;
                    low[w_loc] = t;
                    t += 1;
                    stack.push(w_loc);
                    on[w_loc] = true;
                    calls.push((w_loc, 0));
                } else if on[w_loc] {
                    low[u_loc] = low[u_loc].min(index[w_loc]);
                }
            } else {
                calls.pop();
                if let Some(&(p_loc, _)) = calls.last() {
                    low[p_loc] = low[p_loc].min(low[u_loc]);
                }
                if low[u_loc] == index[u_loc] {
                    let mut comp = Vec::new();
                    while let Some(w_loc) = stack.pop() {
                        on[w_loc] = false;
                        comp.push(sub[w_loc]);
                        if w_loc == u_loc {
                            break;
                        }
                    }
                    out.push(comp);
                }
            }
        }
    }
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
                Kind::Top => 0,
                Kind::Bot => u32::MAX,
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
            if !sc.in_sub[p] || sc.cur[p] || sc.need[p] == u32::MAX {
                continue;
            }
            if g.kind(p_u32) == Kind::Mor && mor != MorRead::Joint {
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
            Kind::Mor | Kind::Top | Kind::Bot => false,
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
                Kind::Top | Kind::Bot => false,
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
                Kind::Top => s += 1,
                Kind::And | Kind::Mor | Kind::Bot => {}
            }
        }
        seeds[cid] = s;
    }
    for &v_u32 in u_set {
        let v = v_u32 as usize;
        let need = match g.kind(v_u32) {
            Kind::Top => u32::MAX,
            Kind::Bot => 0,
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
        if need == 0 {
            sc.cur[v] = false;
            sc.queue.push(v_u32);
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
        let cw = sc.t_comp[w as usize];
        if cw != u32::MAX {
            // A node of a simple cycle died, which breaks the cycle into a chain.
            broken[cw as usize] = true;
        }
        for &p_u32 in &g.parents[w as usize] {
            let p = p_u32 as usize;
            if !sc.in_sub[p] {
                continue;
            }
            let cp = sc.t_comp[p];
            if g.kind[p] == Kind::Or && cp != u32::MAX && cp != cw && !broken[cp as usize] {
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
fn refusal(
    g: &Bes,
    u_set: &[u32],
    t_sccs: &[Vec<u32>],
    gates: usize,
    sc: &mut Scratch,
    stamp: &mut Stamp,
) -> Option<Refusal> {
    sc.mark(u_set, true);
    let mut found = None;
    for (cid, tc) in t_sccs.iter().enumerate() {
        if !g.cyclic(tc) {
            continue;
        }
        for &v in tc {
            sc.t_comp[v as usize] = cid as u32;
        }
        let (mut internal_edges, mut branching_and, mut branching_or) = (0, 0, 0);
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
                    Kind::And => branching_and += 1,
                    Kind::Or => branching_or += 1,
                    Kind::Mor | Kind::Top | Kind::Bot => {}
                }
            }
        }
        for &v in tc {
            sc.t_comp[v as usize] = u32::MAX;
        }
        let cyclomatic = internal_edges.saturating_sub(tc.len()) + 1;
        if cyclomatic >= 2 && branching_and >= 1 {
            found = Some(Refusal {
                node: *tc.iter().min().expect("a component has a node"),
                nodes: tc.len(),
                internal_edges,
                cyclomatic,
                branching_and,
                branching_or: branching_or.max(1),
                gates,
            });
            break;
        }
    }
    sc.mark(u_set, false);
    found
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
