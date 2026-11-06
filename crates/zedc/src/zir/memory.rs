//! Memory (step L1.34): static last-use drops, borrow inference and dup/drop fusion over
//! ZIR, giving precise reference counts for scalars, strings, tuples and closures, and a
//! machine that runs a graph under the plan and checks every count.
//!
//! **The plan.** [`plan`] decides, for each region the machine runs (the root, a lambda's
//! body, an arm of an `if` or a `match`), how each value edge is held and where its counts
//! change. An edge is *owned*, holding one reference, or *borrowed*, read under a reference
//! someone else holds. A node's output is owned. A lambda's parameter is owned when some use
//! consumes it, and borrowed otherwise (borrow inference); its captures are borrowed, since
//! the closure holds them. Each use of an edge takes it *owned*, consuming a reference, or
//! *borrowed*:
//!
//! - a tuple and an atom's payload take their parts owned, a lambda its captures, a push its
//!   value, and a result is owned; an `apply` passes each argument as the callee's
//!   parameter takes it when the callee is a lambda the plan can see (in the same region, or
//!   through captures to an enclosing one), and owned otherwise;
//! - an `if` or a `match` passes a capture owned when it is the edge's last use, the edge is
//!   owned and some arm consumes it, and a `match` takes its scrutinee owned on the same
//!   terms, an arm consuming a binder; otherwise they are borrowed;
//! - every other use, a primitive's operand, a called function, and each input of a family
//!   node, is borrowed.
//!
//! An owned edge gets a dup before each owned use but its last, and a drop after its last
//! use when that use borrows; an owned edge with no use is dropped where it appears. A
//! borrowed edge gets a dup before each owned use and is never dropped. So each reference is
//! dropped at its last use (static last-use drops), and a value used once is never counted.
//!
//! **Fusion.** A `match` that owns its scrutinee hands the arm the binders it uses, owned.
//! With fusion (`fuse`), the arm's entry releases the scrutinee keeping those binders: if the
//! scrutinee's count is 1 its cell is freed without a count write and the binders' references
//! move out of it, the other parts dropped; otherwise each kept binder gets a dup and the
//! scrutinee one decrement. Without fusion, each kept binder gets a dup and the scrutinee a
//! drop. Destructuring a fresh pair of strings and keeping one costs one count write fused,
//! and four unfused.
//!
//! **The heap.** A string, a big integer, a rational, a keypath and a family are each one
//! cell; a non-empty tuple and an atom with a payload are a cell whose children are their
//! parts' cells; a closure is a cell whose children are its captures. An integer, a float, a
//! boolean, the empty tuple and a bare atom are unboxed, and a constant is static: neither is
//! ever counted. A family's own entries are kernel data, held whole (step L3.17 manages
//! them), and the loop and family regions run in the kernel, which borrows their inputs.
//!
//! **The machine.** [`run`] runs the graph, each node under its plan. The value of each
//! scalar, family or port node comes from the kernel, which runs the node alone, raised with
//! its inputs as literals; a tuple, a closure, a call, a branch and a match run in the
//! machine, which therefore keeps the sharing the program makes. After each node, the
//! machine checks that each live cell's count is the number of references to it: from owned
//! edges still to be used, in every frame, and from live cells. So a missed drop, an extra
//! drop, a use after free and a value kept past its last use are each an error, and at the
//! end only the result is live.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::term::{Pattern, Prim, Shared, Term};
use zed_kernel::value::Value;
use zed_kernel::{Evaluator, KernelError};

use super::legalize::{Expansion, Expansions};
use super::lower::raise_with;
use super::{Node, Op, Region, RegionKind, Src, binds};

/// How an edge is held, or how a use takes it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// Holding, or consuming, one reference.
    Owned,
    /// Read under a reference held elsewhere.
    Borrowed,
}

/// The plan of one node.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct NodePlan {
    /// How each input is taken; a state input is borrowed.
    pub modes: Vec<Mode>,
    /// The inputs that get a dup before the node.
    pub dups: Vec<usize>,
    /// The edges dropped after the node.
    pub drops: Vec<Src>,
    /// The edges whose last use is the node.
    pub last: Vec<Src>,
    /// The body of the lambda an `apply` calls, when the plan sees it.
    pub callee: Option<String>,
}

/// The plan of one region.
#[derive(Clone, PartialEq, Debug)]
pub struct RegionPlan {
    /// How each argument is held.
    pub args: Vec<Mode>,
    /// The arguments dropped on entry, having no use.
    pub entry_drops: Vec<usize>,
    /// The nodes' plans.
    pub nodes: Vec<NodePlan>,
    /// The results that get a dup.
    pub result_dups: Vec<usize>,
}

/// A memory plan: one [`RegionPlan`] per region the machine runs, by path (`r`, then
/// `r.3/0` for node 3's first region), and whether `match` fuses its release.
#[derive(Clone, PartialEq, Debug)]
pub struct Plan {
    /// The regions' plans.
    pub regions: BTreeMap<String, RegionPlan>,
    /// Whether a `match` that owns its scrutinee releases it fused with its binders' dups.
    pub fuse: bool,
}

/// The counts of one run.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Stats {
    /// Count increments.
    pub increments: u64,
    /// Count decrements.
    pub decrements: u64,
    /// Cells allocated.
    pub allocations: u64,
    /// Cells freed.
    pub frees: u64,
    /// The most cells live at once.
    pub peak: u64,
    /// The cells whose count ever exceeded 1.
    pub shared: u64,
}

impl Stats {
    /// The count writes: increments and decrements.
    pub fn writes(&self) -> u64 {
        self.increments + self.decrements
    }
}

/// The expansions the counting machine asks of legalization (DESIGN.md sec:ir,
/// "Legalization"): it runs a derived node only through its certificate, and runs every
/// primitive through the kernel.
pub const EXPANSIONS: Expansions = Expansions::of(&[Expansion::Derived]);

/// The memory plan of graph `g`.
///
/// Regions nest as deep as the program, so the planner keeps its work on the heap: the regions
/// still to plan on a list, and the questions a mode asks of the regions under it (whether an
/// arm or a lambda body consumes an argument) on a stack (step T2-mid). Its contexts are the
/// chain of regions from the root to the one being planned, then those a question has entered.
pub fn plan(g: &Region, fuse: bool) -> Plan {
    let mut p = Planner {
        ctxs: vec![Ctx {
            r: g,
            path: "r".into(),
            up: None,
        }],
        params: HashMap::new(),
    };
    let mut regions = BTreeMap::new();
    // Each region still to plan: the context of the region holding it (the last of the chain
    // when it is planned, since the list is taken last in first out), the node and region it
    // is, and how its arguments are held.
    let mut todo: Vec<(usize, usize, usize, Vec<Mode>)> = Vec::new();
    p.region(
        0,
        vec![Mode::Borrowed; g.args.len()],
        &mut regions,
        &mut todo,
    );
    while let Some((c, k, i, args)) = todo.pop() {
        p.ctxs.truncate(c + 1);
        let ctx = p.sub_ctx(c, k, i);
        p.ctxs.push(ctx);
        p.region(c + 1, args, &mut regions, &mut todo);
    }
    Plan { regions, fuse }
}

/// A region with the way to its enclosing one.
struct Ctx<'a> {
    r: &'a Region,
    path: String,
    up: Option<Up<'a>>,
}

/// Where a region's captures come from: argument `first_arg` on is the node's input
/// `first_input` on, in the enclosing region, context `ctx` of the planner.
struct Up<'a> {
    ctx: usize,
    node: &'a Node,
    first_arg: usize,
    first_input: usize,
}

/// Where an edge is used.
#[derive(Clone, Copy, PartialEq, Debug)]
enum At {
    Node(usize, usize),
    Result(usize),
}

/// The edges of a region, its arguments and then its nodes' outputs, each with its uses.
struct Uses {
    base: Vec<usize>,
    uses: Vec<Vec<At>>,
    state: Vec<bool>,
}

impl Uses {
    fn of(r: &Region) -> Uses {
        let mut base = Vec::new();
        let mut state: Vec<bool> = r.args.iter().map(|e| e.is_state()).collect();
        for n in &r.nodes {
            base.push(state.len());
            state.extend(n.outputs.iter().map(|e| e.is_state()));
        }
        let mut u = Uses {
            uses: vec![Vec::new(); state.len()],
            base,
            state,
        };
        for (k, n) in r.nodes.iter().enumerate() {
            for (j, s) in n.inputs.iter().enumerate() {
                if let Some(e) = u.slot(s) {
                    u.uses[e].push(At::Node(k, j));
                }
            }
        }
        for (i, s) in r.results.iter().enumerate() {
            if let Some(e) = u.slot(s) {
                u.uses[e].push(At::Result(i));
            }
        }
        u
    }

    fn slot(&self, s: &Src) -> Option<usize> {
        match s {
            Src::Arg(i) => Some(*i),
            Src::Out(n, p) => Some(self.base[*n] + p),
            Src::Const(_) => None,
        }
    }

    /// The node holding edge `e`'s last use, when that use is not a result.
    fn last(&self, e: usize) -> Option<usize> {
        match self.uses[e].last() {
            Some(At::Node(k, _)) => Some(*k),
            _ => None,
        }
    }
}

struct Planner<'a> {
    /// The contexts: the chain from the root to the region being planned, then the regions
    /// the questions being answered have entered, each taken off when its question ends.
    ctxs: Vec<Ctx<'a>>,
    /// How each lambda body, by path, takes its parameters.
    params: HashMap<String, Vec<Mode>>,
}

/// A question the planner answers: how the use at input `j` of node `k` of region `ctx`
/// takes an edge (`Owned` is true), whether region `ctx` consumes its argument `a` when it
/// owns it, or how the lambda body `body` takes its parameters (the answer goes in
/// `Planner::params`).
enum Ask {
    Mode {
        ctx: usize,
        k: usize,
        j: usize,
        owned: bool,
        last: bool,
    },
    Consumes {
        ctx: usize,
        a: usize,
    },
    Params {
        body: usize,
    },
}

/// A question waiting for the answer to one it asked.
enum Wait<'a> {
    /// Whether region `ctx` consumes argument `a`: use `next` on is still to ask about.
    Consumes {
        ctx: usize,
        a: usize,
        uses: Uses,
        next: usize,
        last: Option<usize>,
    },
    /// The mode of argument `j` of an `apply` whose callee is the lambda body at context
    /// `body`, the last.
    Callee { body: usize, j: usize },
    /// The mode of capture `j` of the `if` or `match` at node `k` of region `ctx`, with `n`
    /// arms: arm `i` on is still to ask; the arm asked last was entered at context `mark`.
    Arms {
        ctx: usize,
        k: usize,
        j: usize,
        i: usize,
        n: usize,
        mark: usize,
    },
    /// The mode of the scrutinee of the `match` at node `k` of region `ctx`: binder `b` on of
    /// arm `i` is still to ask; the arm, when entered, is at context `mark`, with its uses.
    Scrutinee {
        ctx: usize,
        k: usize,
        ps: &'a [Pattern],
        i: usize,
        b: usize,
        arm: Option<Uses>,
        mark: usize,
    },
    /// How lambda body `body` takes its parameters: parameter `modes.len()` on, of `k`, is
    /// still to ask.
    Params {
        body: usize,
        k: usize,
        modes: Vec<Mode>,
    },
}

/// What a question does next: answer, or ask another first.
enum Step {
    Done(bool),
    Ask(Ask),
}

fn mode_of(b: bool) -> Mode {
    if b { Mode::Owned } else { Mode::Borrowed }
}

impl<'a> Planner<'a> {
    /// How the use at input `j` of node `k` takes an edge that is `owned` or not, the node
    /// being its `last` use or not.
    fn mode(&mut self, ctx: usize, k: usize, j: usize, owned: bool, last: bool) -> Mode {
        mode_of(self.answer(Ask::Mode {
            ctx,
            k,
            j,
            owned,
            last,
        }))
    }

    /// How the lambda at node `n` of region `ctx` takes its parameters.
    fn params(&mut self, ctx: usize, n: usize) -> Vec<Mode> {
        let mark = self.ctxs.len();
        let body = self.sub_ctx(ctx, n, 0);
        self.ctxs.push(body);
        self.answer(Ask::Params { body: mark });
        let m = self.params[&self.ctxs[mark].path].clone();
        self.ctxs.truncate(mark);
        m
    }

    /// Answers `ask` on a stack of the questions waiting: questions about the regions under a
    /// node go as deep as the regions nest.
    fn answer(&mut self, ask: Ask) -> bool {
        let mut waits: Vec<Wait<'a>> = Vec::new();
        let mut step = self.open(ask, &mut waits);
        loop {
            step = match step {
                Step::Ask(ask) => self.open(ask, &mut waits),
                Step::Done(b) => match waits.pop() {
                    None => return b,
                    Some(w) => self.resume(w, Some(b), &mut waits),
                },
            };
        }
    }

    /// Starts question `ask`.
    fn open(&mut self, ask: Ask, waits: &mut Vec<Wait<'a>>) -> Step {
        match ask {
            Ask::Mode {
                ctx,
                k,
                j,
                owned,
                last,
            } => {
                let node: &'a Node = &self.ctxs[ctx].r.nodes[k];
                match &node.op {
                    Op::Prim(Prim::Tuple) | Op::Lambda => Step::Done(true),
                    Op::Prim(Prim::Atom) => Step::Done(j >= 2),
                    Op::Push(_) => Step::Done(j == 1),
                    Op::Apply | Op::If if j == 0 => Step::Done(false),
                    Op::Apply => match self.resolve(ctx, &node.inputs[0]) {
                        Some((c, n)) => {
                            let mark = self.ctxs.len();
                            let body = self.sub_ctx(c, n, 0);
                            self.ctxs.push(body);
                            waits.push(Wait::Callee { body: mark, j });
                            Step::Ask(Ask::Params { body: mark })
                        }
                        None => Step::Done(true),
                    },
                    Op::If | Op::Match(_) if !(owned && last) => Step::Done(false),
                    Op::Match(ps) if j == 0 => {
                        let w = Wait::Scrutinee {
                            ctx,
                            k,
                            ps,
                            i: 0,
                            b: 0,
                            arm: None,
                            mark: self.ctxs.len(),
                        };
                        self.resume(w, None, waits)
                    }
                    Op::If | Op::Match(_) => {
                        let n = match &node.op {
                            Op::Match(ps) => ps.len(),
                            _ => 2,
                        };
                        let mark = self.ctxs.len();
                        let w = Wait::Arms {
                            ctx,
                            k,
                            j,
                            i: 0,
                            n,
                            mark,
                        };
                        self.resume(w, None, waits)
                    }
                    _ => Step::Done(false),
                }
            }
            Ask::Consumes { ctx, a } => {
                let uses = Uses::of(self.ctxs[ctx].r);
                let last = uses.last(a);
                let w = Wait::Consumes {
                    ctx,
                    a,
                    uses,
                    next: 0,
                    last,
                };
                self.resume(w, None, waits)
            }
            Ask::Params { body } => {
                if self.params.contains_key(&self.ctxs[body].path) {
                    return Step::Done(false);
                }
                let k = self.ctxs[body].up.as_ref().map_or(0, |u| u.first_arg);
                let w = Wait::Params {
                    body,
                    k,
                    modes: Vec::with_capacity(k),
                };
                self.resume(w, None, waits)
            }
        }
    }

    /// Goes on with question `w`, given the answer `got` to the question it asked last, if
    /// any: asks the next one, putting `w` back on `waits`, or answers.
    fn resume(&mut self, w: Wait<'a>, got: Option<bool>, waits: &mut Vec<Wait<'a>>) -> Step {
        match w {
            Wait::Consumes {
                ctx,
                a,
                uses,
                mut next,
                last,
            } => {
                if got == Some(true) {
                    return Step::Done(true);
                }
                let Some(&at) = uses.uses[a].get(next) else {
                    return Step::Done(false);
                };
                next += 1;
                match at {
                    At::Result(_) => Step::Done(true),
                    At::Node(k, j) => {
                        waits.push(Wait::Consumes {
                            ctx,
                            a,
                            uses,
                            next,
                            last,
                        });
                        Step::Ask(Ask::Mode {
                            ctx,
                            k,
                            j,
                            owned: true,
                            last: last == Some(k),
                        })
                    }
                }
            }
            Wait::Callee { body, j } => {
                let m = self.params[&self.ctxs[body].path]
                    .get(j - 1)
                    .copied()
                    .unwrap_or(Mode::Owned);
                self.ctxs.truncate(body);
                Step::Done(m == Mode::Owned)
            }
            Wait::Arms {
                ctx,
                k,
                j,
                mut i,
                n,
                mark,
            } => {
                self.ctxs.truncate(mark);
                if got == Some(true) {
                    return Step::Done(true);
                }
                if i == n {
                    return Step::Done(false);
                }
                let arm = self.sub_ctx(ctx, k, i);
                let a = arm.up.as_ref().map_or(0, |u| u.first_arg) + j - 1;
                self.ctxs.push(arm);
                i += 1;
                waits.push(Wait::Arms {
                    ctx,
                    k,
                    j,
                    i,
                    n,
                    mark,
                });
                Step::Ask(Ask::Consumes { ctx: mark, a })
            }
            Wait::Scrutinee {
                ctx,
                k,
                ps,
                mut i,
                mut b,
                mut arm,
                mark,
            } => {
                if got == Some(true) {
                    self.ctxs.truncate(mark);
                    return Step::Done(true);
                }
                loop {
                    let Some(u) = &arm else {
                        if i == ps.len() {
                            return Step::Done(false);
                        }
                        let c = self.sub_ctx(ctx, k, i);
                        arm = Some(Uses::of(c.r));
                        self.ctxs.push(c);
                        b = 0;
                        continue;
                    };
                    if b < binds(&ps[i]) {
                        b += 1;
                        if u.uses[b - 1].is_empty() {
                            continue;
                        }
                        waits.push(Wait::Scrutinee {
                            ctx,
                            k,
                            ps,
                            i,
                            b,
                            arm,
                            mark,
                        });
                        return Step::Ask(Ask::Consumes {
                            ctx: mark,
                            a: b - 1,
                        });
                    }
                    self.ctxs.truncate(mark);
                    arm = None;
                    i += 1;
                }
            }
            Wait::Params { body, k, mut modes } => {
                if let Some(g) = got {
                    modes.push(mode_of(g));
                }
                // A state argument holds no value, so it is borrowed, as in an arm.
                while modes.len() < k && self.ctxs[body].r.args[modes.len()].is_state() {
                    modes.push(Mode::Borrowed);
                }
                if modes.len() < k {
                    let a = modes.len();
                    waits.push(Wait::Params { body, k, modes });
                    return Step::Ask(Ask::Consumes { ctx: body, a });
                }
                self.params.insert(self.ctxs[body].path.clone(), modes);
                Step::Done(false)
            }
        }
    }

    /// Plans region `ctx`, its arguments held as `args`, and puts the regions it holds on
    /// `todo`.
    fn region(
        &mut self,
        ctx: usize,
        args: Vec<Mode>,
        out: &mut BTreeMap<String, RegionPlan>,
        todo: &mut Vec<(usize, usize, usize, Vec<Mode>)>,
    ) {
        let r: &'a Region = self.ctxs[ctx].r;
        let u = Uses::of(r);
        let owned = |e: usize| !u.state[e] && args.get(e).is_none_or(|m| *m == Mode::Owned);
        let mut nodes: Vec<NodePlan> = Vec::with_capacity(r.nodes.len());
        for (k, n) in r.nodes.iter().enumerate() {
            let modes = (0..n.inputs.len())
                .map(|j| match u.slot(&n.inputs[j]) {
                    Some(e) if u.state[e] => Mode::Borrowed,
                    Some(e) => self.mode(ctx, k, j, owned(e), u.last(e) == Some(k)),
                    None => self.mode(ctx, k, j, false, false),
                })
                .collect();
            let callee = match (&n.op, n.inputs.first()) {
                (Op::Apply, Some(f)) => self
                    .resolve(ctx, f)
                    .map(|(c, m)| format!("{}.{m}/0", self.ctxs[c].path)),
                _ => None,
            };
            nodes.push(NodePlan {
                modes,
                callee,
                ..NodePlan::default()
            });
        }
        let mut plan = RegionPlan {
            args: args.clone(),
            entry_drops: Vec::new(),
            nodes: Vec::new(),
            result_dups: Vec::new(),
        };
        // The node whose outputs hold edge `e`, found by binary search: `base` never decreases.
        let src = |e: usize| match u.base.partition_point(|b| *b <= e).checked_sub(1) {
            Some(k) if e >= r.args.len() => Src::Out(k, e - u.base[k]),
            _ => Src::Arg(e),
        };
        for e in 0..u.state.len() {
            let us = &u.uses[e];
            let last = u.last(e);
            if let Some(k) = last {
                nodes[k].last.push(src(e));
            }
            if u.state[e] {
                continue;
            }
            let Some(&end) = us.last() else {
                if owned(e) {
                    match src(e) {
                        Src::Arg(a) => plan.entry_drops.push(a),
                        s @ Src::Out(k, _) => nodes[k].drops.push(s),
                        Src::Const(_) => unreachable!("an edge is not a constant"),
                    }
                }
                continue;
            };
            // The use that takes over the edge's own reference, if any.
            let mut moved = None;
            if owned(e) {
                match end {
                    At::Result(i) => moved = Some(At::Result(i)),
                    At::Node(k, _) => {
                        let mut at_k = us.iter().filter(|a| matches!(a, At::Node(m, _) if *m == k));
                        let borrows = at_k.clone().any(
                            |a| matches!(a, At::Node(_, j) if nodes[k].modes[*j] == Mode::Borrowed),
                        );
                        if borrows {
                            nodes[k].drops.push(src(e));
                        } else {
                            moved = at_k.next_back().copied();
                        }
                    }
                }
            }
            for at in us {
                match *at {
                    _ if Some(*at) == moved => {}
                    At::Node(k, j) if nodes[k].modes[j] == Mode::Owned => nodes[k].dups.push(j),
                    At::Node(..) => {}
                    At::Result(i) => plan.result_dups.push(i),
                }
            }
        }
        // The regions under this one go on `todo` last first, so they are planned in order.
        let mut subs = Vec::new();
        for (k, n) in r.nodes.iter().enumerate() {
            let m = &nodes[k].modes;
            match &n.op {
                Op::Lambda => {
                    let mut a = self.params(ctx, k);
                    a.resize(n.regions[0].args.len(), Mode::Borrowed);
                    subs.push((ctx, k, 0, a));
                }
                Op::If | Op::Match(_) => {
                    for i in 0..n.regions.len() {
                        let arm = &n.regions[i];
                        let au = Uses::of(arm);
                        let b = match &n.op {
                            Op::Match(ps) => binds(&ps[i]),
                            _ => 0,
                        };
                        let mut a: Vec<Mode> = (0..b)
                            .map(|x| mode_of(m[0] == Mode::Owned && !au.uses[x].is_empty()))
                            .collect();
                        a.extend(m[1..].iter().copied());
                        for (x, e) in arm.args.iter().enumerate() {
                            if e.is_state() {
                                a[x] = Mode::Borrowed;
                            }
                        }
                        subs.push((ctx, k, i, a));
                    }
                }
                _ => {}
            }
        }
        todo.extend(subs.into_iter().rev());
        plan.nodes = nodes;
        out.insert(self.ctxs[ctx].path.clone(), plan);
    }

    /// The context of region `i` of node `k` of region `ctx`: a lambda's body, or an arm of
    /// an `if` or a `match`.
    fn sub_ctx(&self, ctx: usize, k: usize, i: usize) -> Ctx<'a> {
        let c = &self.ctxs[ctx];
        let node: &'a Node = &c.r.nodes[k];
        let (first_arg, first_input) = match &node.op {
            Op::Lambda => (
                node.regions[0].args.len().saturating_sub(node.inputs.len()),
                0,
            ),
            Op::Match(ps) => (binds(&ps[i]), 1),
            _ => (0, 1),
        };
        Ctx {
            r: &node.regions[i],
            path: format!("{}.{k}/{i}", c.path),
            up: Some(Up {
                ctx,
                node,
                first_arg,
                first_input,
            }),
        }
    }

    /// The lambda node `s` of region `ctx` is, as its region and index, when the plan can see
    /// it. A capture is followed out through the regions holding it, in a loop.
    fn resolve(&self, mut ctx: usize, mut s: &'a Src) -> Option<(usize, usize)> {
        loop {
            let c = &self.ctxs[ctx];
            match s {
                Src::Out(n, 0) if matches!(c.r.nodes[*n].op, Op::Lambda) => return Some((ctx, *n)),
                Src::Arg(i) => {
                    let up = c.up.as_ref()?;
                    s = up
                        .node
                        .inputs
                        .get(up.first_input + i.checked_sub(up.first_arg)?)?;
                    ctx = up.ctx;
                }
                _ => return None,
            }
        }
    }
}

/// A heap cell: its count, 0 once freed, and its children's cells.
struct Cell {
    count: u32,
    kids: Vec<Option<usize>>,
    shared: bool,
}

/// A closure: its cell, its lambda node and that node's occurrence id, the path of its body
/// and its captures.
struct Clo<'g> {
    cell: usize,
    node: &'g Node,
    id: usize,
    path: String,
    caps: Vec<Mv<'g>>,
}

/// Closures capture closures as deep as the program, so a closure's last reference drops
/// the closures it alone holds through a list, not by recursion (step T2-mid).
impl Drop for Clo<'_> {
    fn drop(&mut self) {
        let mut caps = std::mem::take(&mut self.caps);
        while let Some(m) = caps.pop() {
            if let Mv::Clo(rc) = m
                && let Ok(mut c) = Rc::try_unwrap(rc)
            {
                caps.append(&mut c.caps);
            }
        }
    }
}

/// A value in the machine.
#[derive(Clone)]
enum Mv<'g> {
    /// Data, with its cell unless it is unboxed or static.
    Data(Value, Option<usize>),
    /// A closure.
    Clo(Rc<Clo<'g>>),
    /// A primitive as a function.
    Prim(Prim),
    /// A lookup port.
    Source(Arc<str>),
    /// A port's state.
    State,
}

impl Mv<'_> {
    fn cell(&self) -> Option<usize> {
        match self {
            Mv::Data(_, c) => *c,
            Mv::Clo(c) => Some(c.cell),
            _ => None,
        }
    }
}

/// An edge's value in a frame, and whether the frame owns a reference to it.
type Slot<'g> = Option<(Mv<'g>, bool)>;

struct Machine<'g, 'e> {
    plan: &'g Plan,
    ev: &'e mut Evaluator,
    heap: Vec<Cell>,
    frames: Vec<Vec<Slot<'g>>>,
    /// For each cell, its references from owned slots and from the kids of live cells, and
    /// the slots that hold it, owned or not: kept as they change, so that a check need only
    /// look at the cells touched since the last one.
    refs: Vec<u32>,
    holds: Vec<u32>,
    touched: Vec<usize>,
    stats: Stats,
    live: u64,
    /// Each planned region by its path, with the occurrence id of its first node: the regions
    /// are numbered by one walk of the plan in path order, and node `k` of a region is its
    /// first id plus `k`, so an id depends only on where the node stands in the graph, never
    /// on where it is in memory (step ADDR-memory).
    places: HashMap<&'g str, (usize, &'g RegionPlan)>,
    /// The one-node region of each node occurrence the kernel has run, by its occurrence id.
    alone: Vec<Option<Region>>,
}

/// Runs graph `g` under `plan`, the kernel running each scalar and family node in `ev`, and
/// checks every count; returns the value and the counts.
pub fn run(g: &Region, plan: &Plan, ev: &mut Evaluator) -> Result<(Value, Stats), String> {
    let mut places = HashMap::with_capacity(plan.regions.len());
    let mut ids = 0;
    for (path, rp) in &plan.regions {
        places.insert(path.as_str(), (ids, rp));
        ids += rp.nodes.len();
    }
    let mut m = Machine {
        plan,
        ev,
        heap: Vec::new(),
        frames: Vec::new(),
        refs: Vec::new(),
        holds: Vec::new(),
        touched: Vec::new(),
        stats: Stats::default(),
        live: 0,
        places,
        alone: (0..ids).map(|_| None).collect(),
    };
    let args = g.args.iter().map(|_| (Mv::State, false)).collect();
    let mut out = m.region(g, args)?;
    let v = out.swap_remove(0);
    m.push_frame(vec![Some((v.clone(), true))]);
    m.check("the end of the run")?;
    m.pop_frame();
    m.dec(v.cell())?;
    if m.live != 0 {
        return Err(format!(
            "memory: {} live after the result is dropped",
            plural(m.live, "cell")
        ));
    }
    match v {
        Mv::Data(v, _) => Ok((v, m.stats)),
        _ => Err(KernelError::Type("the program's result is a function".into()).to_string()),
    }
}

/// A part waiting in [`Machine::release`]: one to drop, or one with the paths kept inside it.
enum Part<'p> {
    Drop(Option<usize>),
    Keep(Option<usize>, Vec<&'p [usize]>),
}

/// A region the machine is running: its plan, under its path, its edges' uses, the node it is
/// at, that node's path, and whether that node, an `apply`, holds a frame of the arguments it
/// passes owned to a callee that borrows them.
struct Running<'g> {
    r: &'g Region,
    path: &'g str,
    first: usize,
    rp: &'g RegionPlan,
    u: Uses,
    k: usize,
    at: String,
    held: bool,
}

/// What a node gives: its outputs, or a region to run whose results are its outputs.
enum Out<'g> {
    Done(Vec<Mv<'g>>),
    Call {
        r: &'g Region,
        path: &'g str,
        first: usize,
        rp: &'g RegionPlan,
        args: Vec<(Mv<'g>, bool)>,
        held: bool,
    },
}

impl<'g> Machine<'g, '_> {
    /// Runs region `r` on `args`, and the regions its nodes call, on a stack of running
    /// regions: calls and arms nest as deep as the program and its run (step T2-mid).
    fn region(&mut self, r: &'g Region, args: Vec<(Mv<'g>, bool)>) -> Result<Vec<Mv<'g>>, String> {
        let (path, first, rp) = self.plan_of("r")?;
        let mut stack = vec![self.enter(r, path, first, rp, args)?];
        loop {
            let top = stack.last_mut().expect("a running region");
            if top.k == top.r.nodes.len() {
                let outs = self.leave(top)?;
                stack.pop();
                match stack.last_mut() {
                    None => return Ok(outs),
                    Some(caller) => self.returned(caller, outs)?,
                }
                continue;
            }
            let ins = self.inputs(top)?;
            let node = &top.r.nodes[top.k];
            match self.node(node, top.first + top.k, &top.rp.nodes[top.k], &top.at, ins)? {
                Out::Done(outs) => self.finish(top, outs)?,
                Out::Call {
                    r,
                    path,
                    first,
                    rp,
                    args,
                    held,
                } => {
                    top.held = held;
                    let callee = self.enter(r, path, first, rp, args)?;
                    stack.push(callee);
                }
            }
        }
    }

    /// The plan of the region at `path`, with the path as the plan holds it and the occurrence
    /// id of the region's first node.
    fn plan_of(&self, path: &str) -> Result<(&'g str, usize, &'g RegionPlan), String> {
        self.places
            .get_key_value(path)
            .map(|(p, &(first, rp))| (*p, first, rp))
            .ok_or_else(|| {
                format!(
                    "memory: region `{path}` has no plan; only the root, lambda bodies and arms do"
                )
            })
    }

    /// Enters region `r`, at `path` with first node occurrence `first`, under plan `rp`, on
    /// `args`: checks how they arrive, and makes its frame.
    fn enter(
        &mut self,
        r: &'g Region,
        path: &'g str,
        first: usize,
        rp: &'g RegionPlan,
        args: Vec<(Mv<'g>, bool)>,
    ) -> Result<Running<'g>, String> {
        for (i, (_, owned)) in args.iter().enumerate() {
            if !r.args[i].is_state() && *owned != (rp.args[i] == Mode::Owned) {
                return Err(format!(
                    "memory: argument {i} of `{path}` arrives {}, and the plan holds it {}",
                    held(*owned),
                    held(rp.args[i] == Mode::Owned)
                ));
            }
        }
        let u = Uses::of(r);
        let mut frame: Vec<Slot<'g>> = vec![None; u.state.len()];
        for (i, a) in args.into_iter().enumerate() {
            frame[i] = Some(a);
        }
        self.push_frame(frame);
        for &a in &rp.entry_drops {
            let (v, _) = self.take(&u, &Src::Arg(a), path, "an entry drop")?;
            self.dec(v.cell())?;
        }
        self.check(&format!("the entry of `{path}`"))?;
        Ok(Running {
            r,
            path,
            first,
            rp,
            u,
            k: 0,
            at: String::new(),
            held: false,
        })
    }

    /// Reads the inputs of the node region `run` is at, as its plan takes them.
    fn inputs(&mut self, run: &mut Running<'g>) -> Result<Vec<Mv<'g>>, String> {
        run.at = format!("{}.{}", run.path, run.k);
        let (node, np, u, at) = (&run.r.nodes[run.k], &run.rp.nodes[run.k], &run.u, &run.at);
        let mut ins = Vec::new();
        for s in &node.inputs {
            ins.push(self.read(u, s, at)?);
        }
        let mut dup = vec![false; node.inputs.len()];
        for &j in &np.dups {
            dup[j] = true;
            self.inc(ins[j].cell());
        }
        for (j, s) in node.inputs.iter().enumerate() {
            if np.modes[j] == Mode::Owned && !dup[j] && u.slot(s).is_some() {
                self.take(u, s, at, &format!("input {j}, taken owned"))?;
            }
        }
        Ok(ins)
    }

    /// The region that the node `caller` is at called has given `outs`.
    fn returned(&mut self, caller: &mut Running<'g>, outs: Vec<Mv<'g>>) -> Result<(), String> {
        if caller.held {
            caller.held = false;
            let held = self.pop_frame();
            for (v, _) in held.into_iter().flatten() {
                self.dec(v.cell())?;
            }
        }
        self.finish(caller, outs)
    }

    /// Stores the outputs `outs` of the node region `run` is at, drops what its plan drops
    /// after it, checks the counts, and moves to the next node.
    fn finish(&mut self, run: &mut Running<'g>, outs: Vec<Mv<'g>>) -> Result<(), String> {
        let (k, node, np, u, at) = (
            run.k,
            &run.r.nodes[run.k],
            &run.rp.nodes[run.k],
            &run.u,
            &run.at,
        );
        for (p, v) in outs.into_iter().enumerate() {
            let owned = !node.outputs[p].is_state();
            self.set(u.base[k] + p, Some((v, owned)));
        }
        for s in &np.drops {
            let (v, _) = self.take(u, s, at, "a drop")?;
            self.dec(v.cell())?;
        }
        for s in &np.last {
            let e = u.slot(s).expect("an edge");
            if let Some((_, true)) = &self.frames.last().expect("frame")[e] {
                return Err(format!(
                    "memory: {at}: edge {} is still owned after its last use, a leak",
                    show_src(s)
                ));
            }
            self.set(e, None);
        }
        self.check(&format!("node {at}"))?;
        run.k += 1;
        Ok(())
    }

    /// Leaves region `run`, all its nodes run: gives its results and drops its frame.
    fn leave(&mut self, run: &Running<'g>) -> Result<Vec<Mv<'g>>, String> {
        let (r, rp, u, path) = (run.r, run.rp, &run.u, run.path);
        let dup: HashSet<usize> = rp.result_dups.iter().copied().collect();
        let mut out = Vec::new();
        for (i, s) in r.results.iter().enumerate() {
            let v = self.read(u, s, &format!("{path} result {i}"))?;
            if dup.contains(&i) {
                self.inc(v.cell());
            } else if u.slot(s).is_some() && !u.state[u.slot(s).expect("an edge")] {
                self.take(u, s, path, &format!("result {i}"))?;
            }
            out.push(v);
        }
        let frame = self.pop_frame();
        if let Some(e) = frame.iter().position(|s| matches!(s, Some((_, true)))) {
            return Err(format!(
                "memory: `{path}` ends still owning edge {e}, a leak"
            ));
        }
        Ok(out)
    }

    /// Runs one node, occurrence `id`, on its inputs, as the plan takes them; returns its
    /// outputs, owned.
    fn node(
        &mut self,
        node: &'g Node,
        id: usize,
        np: &NodePlan,
        at: &str,
        ins: Vec<Mv<'g>>,
    ) -> Result<Out<'g>, String> {
        let data = |m: &Mv<'g>| matches!(m, Mv::Data(..));
        Ok(Out::Done(match &node.op {
            Op::Prim(p) if ins.is_empty() && p.arity().is_some() => vec![Mv::Prim(*p)],
            Op::Prim(Prim::Tuple) if ins.iter().all(data) && !ins.is_empty() => {
                let vals = ins.iter().map(value).collect();
                let cell = self.alloc(ins.iter().map(Mv::cell).collect());
                vec![Mv::Data(Value::tuple(vals), Some(cell))]
            }
            Op::Prim(Prim::Atom) if ins.iter().all(data) => {
                let v = self.kernel(node, id, &ins)?;
                let names: &[Value] = match &ins[1] {
                    Mv::Data(Value::Tuple(ns), _) => ns,
                    _ => &[],
                };
                match &v {
                    Value::Atom(a) if !a.args.is_empty() && a.args.len() + 2 == ins.len() => {
                        let at: BTreeMap<&Value, usize> =
                            names.iter().enumerate().map(|(i, n)| (n, i)).collect();
                        let kids = (0..a.args.len())
                            .map(|i| {
                                let from = match names.is_empty() {
                                    true => i,
                                    false => at[&Value::Str(a.fields[i].clone().into())],
                                };
                                ins[2 + from].cell()
                            })
                            .collect();
                        let cell = self.alloc(kids);
                        vec![Mv::Data(v, Some(cell))]
                    }
                    _ => {
                        self.consume(np, &ins)?;
                        vec![self.fresh(v)]
                    }
                }
            }
            Op::Prim(Prim::TupleGet) => {
                let v = self.kernel(node, id, &ins)?;
                match (&ins[0], &ins[1]) {
                    (Mv::Data(Value::Tuple(_), Some(c)), Mv::Data(Value::Int(i), _)) => {
                        let kid = self.heap[*c].kids[*i as usize];
                        self.inc(kid);
                        vec![Mv::Data(v, kid)]
                    }
                    _ => vec![self.fresh(v)],
                }
            }
            Op::Lambda => {
                let cell = self.alloc(ins.iter().map(Mv::cell).collect());
                vec![Mv::Clo(Rc::new(Clo {
                    cell,
                    node,
                    id,
                    path: format!("{at}/0"),
                    caps: ins,
                }))]
            }
            Op::Apply => match &ins[0] {
                Mv::Clo(c)
                    if c.node.regions[0].args.len() == c.node.inputs.len() + ins.len() - 1 =>
                {
                    let c = c.clone();
                    if let Some(want) = &np.callee
                        && *want != c.path
                    {
                        return Err(format!(
                            "memory: {at}: the plan calls `{want}`, and the callee is `{}`",
                            c.path
                        ));
                    }
                    let (path, first, rp) = self.plan_of(&c.path)?;
                    let mut args = Vec::new();
                    let mut held = Vec::new();
                    for (i, v) in ins[1..].iter().enumerate() {
                        match (np.modes[1 + i], rp.args[i]) {
                            (Mode::Owned, Mode::Owned) => args.push((v.clone(), true)),
                            (Mode::Owned, Mode::Borrowed) => {
                                held.push(Some((v.clone(), true)));
                                args.push((v.clone(), false));
                            }
                            (Mode::Borrowed, Mode::Borrowed) => args.push((v.clone(), false)),
                            (Mode::Borrowed, Mode::Owned) => {
                                return Err(format!(
                                    "memory: {at}: argument {i} is passed borrowed to `{}`, \
                                     which consumes it",
                                    c.path
                                ));
                            }
                        }
                    }
                    args.extend(c.caps.iter().map(|v| (v.clone(), false)));
                    self.push_frame(held);
                    let callee: &'g Node = c.node;
                    return Ok(Out::Call {
                        r: &callee.regions[0],
                        path,
                        first,
                        rp,
                        args,
                        held: true,
                    });
                }
                _ => {
                    let v = self.kernel(node, id, &ins)?;
                    self.consume(np, &ins)?;
                    let mut out = vec![self.fresh(v)];
                    out.resize(node.outputs.len(), Mv::State);
                    out
                }
            },
            Op::If => {
                let arm = match &ins[0] {
                    Mv::Data(Value::Bool(b), _) => Ok(usize::from(!b)),
                    c => {
                        let mut lets = Lets::default();
                        let t = Term::If(
                            Shared::new(self.term(c, &mut lets)?),
                            Shared::new(Term::Lit(Value::Int(0))),
                            Shared::new(Term::Lit(Value::Int(1))),
                        );
                        match self.ev.run(&wrap(lets, t)).map_err(|e| e.to_string())? {
                            Value::Int(i) => Ok(i as usize),
                            v => Err(v),
                        }
                    }
                };
                match arm {
                    Ok(i) => {
                        let args = (1..ins.len())
                            .map(|j| (ins[j].clone(), np.modes[j] == Mode::Owned))
                            .collect();
                        let (path, first, rp) = self.plan_of(&format!("{at}/{i}"))?;
                        return Ok(Out::Call {
                            r: &node.regions[i],
                            path,
                            first,
                            rp,
                            args,
                            held: false,
                        });
                    }
                    Err(v) => self.failed(node, np, &ins, v)?,
                }
            }
            Op::Match(ps) => return self.matched(node, ps, np, at, ins),
            Op::Read(p) => {
                let v = match self.ev.world.inputs.get(&**p) {
                    Some(v) => {
                        let v = v.clone();
                        self.fresh(v)
                    }
                    None if self.ev.world.sources.contains_key(&**p) => Mv::Source(p.clone()),
                    None => {
                        let v = self.ev.run(&Term::Read(p.clone()));
                        return Err(v.map_or_else(|e| e.to_string(), |_| "a read".into()));
                    }
                };
                vec![v, Mv::State]
            }
            Op::Push(_) => {
                let v = self.kernel(node, id, &ins)?;
                self.consume(np, &ins)?;
                vec![self.fresh(v), Mv::State]
            }
            _ => {
                let v = self.kernel(node, id, &ins)?;
                self.consume(np, &ins)?;
                vec![self.fresh(v)]
            }
        }))
    }

    /// A `match`: the kernel picks the arm and binds its values, and the machine finds the
    /// binders' cells inside the scrutinee's and releases the scrutinee.
    fn matched(
        &mut self,
        node: &'g Node,
        ps: &[Pattern],
        np: &NodePlan,
        at: &str,
        ins: Vec<Mv<'g>>,
    ) -> Result<Out<'g>, String> {
        let mut lets = Lets::default();
        let s = self.term(&ins[0], &mut lets)?;
        let mut arms = Vec::new();
        for (i, p) in ps.iter().enumerate() {
            let mut p = p.clone();
            let mut xs = vec![Term::Lit(Value::Int(i as i64))];
            let mut n = 0;
            rename(&mut p, &mut || {
                n += 1;
                let x: Arc<str> = format!("\0bind{n}").into();
                xs.push(Term::Var(x.clone()));
                x
            });
            arms.push((p, Term::Prim(Prim::Tuple, xs)));
        }
        let t = wrap(lets, Term::Match(Shared::new(s), arms));
        let (i, vals) = match self.ev.run(&t).map_err(|e| e.to_string())? {
            Value::Tuple(xs) if matches!(xs.first(), Some(Value::Int(i)) if (*i as usize) < ps.len()) =>
            {
                let mut xs = xs.into_vec();
                let Value::Int(i) = xs.remove(0) else {
                    unreachable!("checked above")
                };
                (i as usize, xs)
            }
            v => return self.failed(node, np, &ins, v).map(Out::Done),
        };
        let path = format!("{at}/{i}");
        let (key, first, arm) = self.plan_of(&path)?;
        let mut paths = Vec::new();
        if let Mv::Data(v, _) = &ins[0] {
            binder_paths(&ps[i], v, &mut Vec::new(), &mut paths);
        }
        let scrut = ins[0].cell();
        let cells: Vec<Option<usize>> = (0..vals.len())
            .map(|b| paths.get(b).and_then(|p| self.cell_at(scrut, p)))
            .collect();
        let mut args = Vec::new();
        if np.modes[0] == Mode::Owned {
            let kept: Vec<usize> = (0..vals.len())
                .filter(|b| arm.args[*b] == Mode::Owned)
                .collect();
            let kept_paths: Vec<&[usize]> = kept
                .iter()
                .filter_map(|b| paths.get(*b).map(Vec::as_slice))
                .collect();
            if self.plan.fuse {
                self.release(scrut, &kept_paths)?;
            } else {
                for b in &kept {
                    self.inc(cells[*b]);
                }
                self.dec(scrut)?;
            }
            for (b, v) in vals.into_iter().enumerate() {
                let owned = arm.args[b] == Mode::Owned;
                args.push((Mv::Data(v, if owned { cells[b] } else { None }), owned));
            }
        } else {
            for (b, v) in vals.into_iter().enumerate() {
                if arm.args[b] == Mode::Owned {
                    return Err(format!(
                        "memory: {at}: the scrutinee is borrowed, and arm {i} owns binder {b}"
                    ));
                }
                args.push((Mv::Data(v, cells[b]), false));
            }
        }
        args.extend((1..ins.len()).map(|j| (ins[j].clone(), np.modes[j] == Mode::Owned)));
        Ok(Out::Call {
            r: &node.regions[i],
            path: key,
            first,
            rp: arm,
            args,
            held: false,
        })
    }

    /// An `if` or `match` whose decision is a failure value `v`: the value is the result,
    /// and the owned inputs are dropped.
    fn failed(
        &mut self,
        node: &Node,
        np: &NodePlan,
        ins: &[Mv<'g>],
        v: Value,
    ) -> Result<Vec<Mv<'g>>, String> {
        self.consume(np, ins)?;
        let mut out = vec![self.fresh(v)];
        out.extend(node.outputs[1..].iter().map(|_| Mv::State));
        Ok(out)
    }

    /// Fused release of the scrutinee `cell`, keeping the cells at `kept`.
    ///
    /// The scrutinee nests as deep as the program, so the parts still to drop or release wait
    /// on a stack, in order (step T2-mid).
    fn release(&mut self, cell: Option<usize>, kept: &[&[usize]]) -> Result<(), String> {
        let mut stack = vec![Part::Keep(cell, kept.to_vec())];
        while let Some(part) = stack.pop() {
            let (cell, kept) = match part {
                Part::Drop(cell) => {
                    self.dec(cell)?;
                    continue;
                }
                Part::Keep(cell, kept) => (cell, kept),
            };
            let Some(c) = cell else { continue };
            if kept.iter().any(|p| p.is_empty()) {
                continue;
            }
            if self.heap[c].count == 1 {
                self.heap[c].count = 0;
                self.stats.frees += 1;
                self.live -= 1;
                self.touched.push(c);
                let kids = std::mem::take(&mut self.heap[c].kids);
                for k in kids.iter().flatten() {
                    self.refs[*k] -= 1;
                    self.touched.push(*k);
                }
                for (i, k) in kids.into_iter().enumerate().rev() {
                    let sub: Vec<&[usize]> =
                        kept.iter().filter(|p| p[0] == i).map(|p| &p[1..]).collect();
                    stack.push(if sub.is_empty() {
                        Part::Drop(k)
                    } else {
                        Part::Keep(k, sub)
                    });
                }
            } else {
                for p in &kept {
                    let k = self.cell_at(cell, p);
                    self.inc(k);
                }
                self.dec(cell)?;
            }
        }
        Ok(())
    }

    fn cell_at(&self, mut c: Option<usize>, path: &[usize]) -> Option<usize> {
        for &i in path {
            c = *self.heap[c?].kids.get(i)?;
        }
        c
    }

    /// Drops each input the node took owned.
    fn consume(&mut self, np: &NodePlan, ins: &[Mv<'g>]) -> Result<(), String> {
        for (j, v) in ins.iter().enumerate() {
            if np.modes[j] == Mode::Owned {
                self.dec(v.cell())?;
            }
        }
        Ok(())
    }

    /// The value the kernel gives node `node`, occurrence `id`, run alone on `ins`.
    fn kernel(&mut self, node: &'g Node, id: usize, ins: &[Mv<'g>]) -> Result<Value, String> {
        let mut lets = Lets::default();
        let mut terms = Vec::new();
        for v in ins {
            terms.push(self.term(v, &mut lets)?);
        }
        let t = raise_with(self.alone(node, id), &terms)?;
        self.ev.run(&wrap(lets, t)).map_err(|e| e.to_string())
    }

    /// A one-node region running `node`, occurrence `id`, on its arguments, made the first time
    /// the occurrence runs.
    fn alone(&mut self, node: &'g Node, id: usize) -> &Region {
        self.alone[id].get_or_insert_with(|| {
            let mut n = node.clone();
            n.inputs = (0..n.inputs.len()).map(Src::Arg).collect();
            Region {
                kind: RegionKind::Function,
                args: Vec::new(),
                nodes: vec![n],
                results: vec![Src::Out(0, 0)],
            }
        })
    }

    /// The kernel term for `v`; a lookup port is read once, by a `let` in `lets`.
    ///
    /// Closures capture closures as deep as the program, so the closures entered wait on a
    /// stack with the terms of their captures so far. Each closure's term is built once, in
    /// `lets.closures`.
    fn term(&mut self, v: &Mv<'g>, lets: &mut Lets) -> Result<Term, String> {
        let mut stack: Vec<(Rc<Clo<'g>>, Vec<Term>)> = Vec::new();
        let mut got = match v {
            Mv::Clo(c) => lets.closures.get(&c.cell).cloned().or_else(|| {
                stack.push((c.clone(), Vec::new()));
                None
            }),
            v => Some(flat_term(v, lets)),
        };
        loop {
            let Some((c, terms)) = stack.last_mut() else {
                return Ok(got.expect("a term"));
            };
            terms.extend(got.take());
            match c.caps.get(terms.len()) {
                Some(Mv::Clo(d)) => {
                    got = lets.closures.get(&d.cell).cloned();
                    if got.is_none() {
                        let d = d.clone();
                        stack.push((d, Vec::new()));
                    }
                }
                Some(v) => got = Some(flat_term(v, lets)),
                None => {
                    let (c, terms) = stack.pop().expect("a closure");
                    let t = raise_with(self.alone(c.node, c.id), &terms)?;
                    lets.closures.insert(c.cell, t.clone());
                    got = Some(t);
                }
            }
        }
    }

    fn read(&self, u: &Uses, s: &Src, at: &str) -> Result<Mv<'g>, String> {
        let Some(e) = u.slot(s) else {
            let Src::Const(v) = s else {
                unreachable!("a constant")
            };
            return Ok(Mv::Data(v.clone(), None));
        };
        match &self.frames.last().expect("frame")[e] {
            Some((v, _)) => {
                if let Some(c) = v.cell()
                    && self.heap[c].count == 0
                {
                    return Err(format!(
                        "memory: {at}: edge {} is read after its cell {c} was freed",
                        show_src(s)
                    ));
                }
                Ok(v.clone())
            }
            None => Err(format!(
                "memory: {at}: edge {} is read after its last use",
                show_src(s)
            )),
        }
    }

    /// Takes the frame's reference to edge `s`, which the frame must own.
    fn take(&mut self, u: &Uses, s: &Src, at: &str, why: &str) -> Result<(Mv<'g>, bool), String> {
        let e = u.slot(s).expect("an edge");
        match self.set(e, None) {
            Some((v, true)) => Ok((v, true)),
            Some((_, false)) => Err(format!(
                "memory: {at}: {why} consumes edge {}, which is borrowed and has no dup",
                show_src(s)
            )),
            None => Err(format!(
                "memory: {at}: {why} consumes edge {}, already consumed or past its last use",
                show_src(s)
            )),
        }
    }

    fn alloc(&mut self, kids: Vec<Option<usize>>) -> usize {
        for k in kids.iter().flatten() {
            self.refs[*k] += 1;
            self.touched.push(*k);
        }
        self.refs.push(0);
        self.holds.push(0);
        self.touched.push(self.heap.len());
        self.heap.push(Cell {
            count: 1,
            kids,
            shared: false,
        });
        self.stats.allocations += 1;
        self.live += 1;
        self.stats.peak = self.stats.peak.max(self.live);
        self.heap.len() - 1
    }

    /// A fresh value: its cells allocated, the parts of a tuple or an atom each its own.
    fn fresh(&mut self, v: Value) -> Mv<'g> {
        let c = self.tree(&v);
        Mv::Data(v, c)
    }

    /// The cells of `v`, each part's before its whole's, on a stack of the tuples and atoms
    /// entered with the cells of their parts so far: values nest as deep as the program.
    fn tree(&mut self, v: &Value) -> Option<usize> {
        let mut stack: Vec<(&[Value], Vec<Option<usize>>)> = Vec::new();
        let mut next = v;
        loop {
            let mut got = match next {
                Value::Bool(_) | Value::Int(_) | Value::Float(_) => None,
                Value::Tuple(xs) if xs.is_empty() => None,
                Value::Atom(a) if a.args.is_empty() => None,
                Value::Tuple(xs) => {
                    stack.push((xs, Vec::with_capacity(xs.len())));
                    next = &xs[0];
                    continue;
                }
                Value::Atom(a) => {
                    stack.push((&a.args, Vec::with_capacity(a.args.len())));
                    next = &a.args[0];
                    continue;
                }
                Value::Str(_)
                | Value::Big(_)
                | Value::Rat(_)
                | Value::Path(_)
                | Value::Family(_) => Some(self.alloc(Vec::new())),
            };
            loop {
                let Some((xs, kids)) = stack.last_mut() else {
                    return got;
                };
                let xs: &[Value] = xs;
                kids.push(got);
                if let Some(x) = xs.get(kids.len()) {
                    next = x;
                    break;
                }
                let (_, kids) = stack.pop().expect("a tuple or atom");
                got = Some(self.alloc(kids));
            }
        }
    }

    fn inc(&mut self, c: Option<usize>) {
        if let Some(c) = c {
            self.stats.increments += 1;
            self.touched.push(c);
            self.heap[c].count += 1;
            if self.heap[c].count == 2 && !self.heap[c].shared {
                self.heap[c].shared = true;
                self.stats.shared += 1;
            }
        }
    }

    /// Drops a reference to `c`; a freed cell drops its parts', in order, before the next
    /// cell's, on a stack of the cells still to drop: values nest as deep as the program.
    fn dec(&mut self, c: Option<usize>) -> Result<(), String> {
        let mut stack: Vec<usize> = c.into_iter().collect();
        while let Some(c) = stack.pop() {
            self.stats.decrements += 1;
            if self.heap[c].count == 0 {
                return Err(format!("memory: cell {c} is dropped after it was freed"));
            }
            self.touched.push(c);
            self.heap[c].count -= 1;
            if self.heap[c].count == 0 {
                self.stats.frees += 1;
                self.live -= 1;
                let kids = std::mem::take(&mut self.heap[c].kids);
                for k in kids.iter().flatten() {
                    self.refs[*k] -= 1;
                }
                stack.extend(kids.into_iter().rev().flatten());
            }
        }
        Ok(())
    }

    /// Counts slot `s` into the references of its cell, or out of them.
    fn note(&mut self, s: &Slot<'g>, into: bool) {
        let Some((v, owned)) = s else { return };
        let Some(c) = v.cell() else { return };
        if into {
            self.holds[c] += 1;
            self.refs[c] += u32::from(*owned);
        } else {
            self.holds[c] -= 1;
            self.refs[c] -= u32::from(*owned);
        }
        self.touched.push(c);
    }

    fn push_frame(&mut self, frame: Vec<Slot<'g>>) {
        for s in &frame {
            self.note(s, true);
        }
        self.frames.push(frame);
    }

    fn pop_frame(&mut self) -> Vec<Slot<'g>> {
        let frame = self.frames.pop().expect("a frame");
        for s in &frame {
            self.note(s, false);
        }
        frame
    }

    /// Puts `s` in slot `e` of the current frame; returns what it held.
    fn set(&mut self, e: usize, s: Slot<'g>) -> Slot<'g> {
        self.note(&s, true);
        let old = std::mem::replace(&mut self.frames.last_mut().expect("a frame")[e], s);
        self.note(&old, false);
        old
    }

    /// Checks the cells touched since the last check, which passed: no other cell's count or
    /// references changed. When one is wrong, the full audit names every fault.
    fn check(&mut self, when: &str) -> Result<(), String> {
        let touched = std::mem::take(&mut self.touched);
        let wrong = touched.iter().any(|&c| {
            self.heap[c].count != self.refs[c] || (self.heap[c].count == 0 && self.holds[c] > 0)
        });
        if wrong { self.audit(when) } else { Ok(()) }
    }

    /// Checks that each live cell's count is the number of references to it, from owned
    /// slots in every frame and from live cells, and that no slot holds a freed cell.
    fn audit(&self, when: &str) -> Result<(), String> {
        let mut refs = vec![0u32; self.heap.len()];
        for (f, frame) in self.frames.iter().enumerate() {
            for (e, slot) in frame.iter().enumerate() {
                let Some((v, owned)) = slot else { continue };
                let Some(c) = v.cell() else { continue };
                if self.heap[c].count == 0 {
                    return Err(format!(
                        "memory: at {when}, edge {e} of frame {f} holds cell {c}, which is freed"
                    ));
                }
                refs[c] += u32::from(*owned);
            }
        }
        for cell in &self.heap {
            if cell.count > 0 {
                for k in cell.kids.iter().flatten() {
                    refs[*k] += 1;
                }
            }
        }
        let wrong: Vec<String> = (0..self.heap.len())
            .filter(|c| self.heap[*c].count != refs[*c])
            .map(|c| {
                format!(
                    "cell {c} has count {} and {}",
                    self.heap[c].count,
                    plural(u64::from(refs[c]), "reference")
                )
            })
            .collect();
        if wrong.is_empty() {
            return Ok(());
        }
        let mut s = format!("memory: at {when}, ");
        let _ = write!(s, "{}", wrong.join("; "));
        s.push_str(" (a count above its references is a missed drop, one below is an extra drop)");
        Err(s)
    }
}

/// The value of data `m`.
fn value(m: &Mv<'_>) -> Value {
    match m {
        Mv::Data(v, _) => v.clone(),
        _ => unreachable!("checked to be data"),
    }
}

fn port_var(p: &str) -> Arc<str> {
    format!("\0port {p}").into()
}

/// `t` with each lookup port in `ports` read first.
fn wrap(ports: Lets, t: Term) -> Term {
    ports.order.into_iter().rev().fold(t, |b, p| {
        Term::Let(port_var(&p), Shared::new(Term::Read(p)), Shared::new(b))
    })
}

/// The lookup ports a kernel term reads, each once, in the order first met, and the term of
/// each closure it holds.
#[derive(Default)]
struct Lets {
    seen: HashSet<Arc<str>>,
    order: Vec<Arc<str>>,
    /// The term of each closure met, by its cell (`Clo::cell`), which no other closure of the
    /// run has: a closure captured on many paths is built once, so the term is a graph the
    /// size of the closures, not a tree of every path (COMPLEXITY.md R9). A closure's term is
    /// a `let` of its lambda, whose parts are shared, so a copy costs a few words.
    closures: HashMap<usize, Term>,
}

/// The kernel term for `v`, which is not a closure; a lookup port is read once, by a `let`
/// in `lets`.
fn flat_term(v: &Mv<'_>, lets: &mut Lets) -> Term {
    match v {
        Mv::Data(v, _) => Term::Lit(v.clone()),
        Mv::Prim(p) => Term::PrimFn(*p),
        Mv::State => Term::Lit(Value::tuple(Vec::new())),
        Mv::Source(p) => {
            if lets.seen.insert(p.clone()) {
                lets.order.push(p.clone());
            }
            Term::Var(port_var(p))
        }
        Mv::Clo(_) => unreachable!("a closure's term is built on the stack of `term`"),
    }
}

/// The path of child indices to each binder of `p` inside `v`, which `p` matches, in
/// preorder, appended to `at`.
///
/// Patterns nest as deep as the program, so the parts still to visit wait on a stack, each
/// with the length of the path above it and its index (step T2-mid).
fn binder_paths(p: &Pattern, v: &Value, at: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    let base = at.len();
    let mut stack: Vec<(usize, Option<usize>, &Pattern, &Value)> = vec![(base, None, p, v)];
    while let Some((len, i, p, v)) = stack.pop() {
        at.truncate(len);
        at.extend(i);
        let len = at.len();
        match (p, v) {
            (Pattern::Bind(_), _) => out.push(at.clone()),
            (Pattern::Tuple(ps), Value::Tuple(xs)) => {
                let parts = ps.iter().zip(xs.iter()).enumerate();
                stack.extend(parts.rev().map(|(i, (q, x))| (len, Some(i), q, x)));
            }
            (Pattern::Atom(_, ps), Value::Atom(a)) => {
                let parts = ps.iter().zip(a.args.iter()).enumerate();
                stack.extend(parts.rev().map(|(i, (q, x))| (len, Some(i), q, x)));
            }
            (Pattern::Fields(_, fs), Value::Atom(a)) => {
                let parts = fs.iter().filter_map(|(f, q)| {
                    let i = a.fields.binary_search(f).ok()?;
                    Some((len, Some(i), q, &a.args[i]))
                });
                let parts: Vec<_> = parts.collect();
                stack.extend(parts.into_iter().rev());
            }
            _ => {}
        }
    }
    at.truncate(base);
}

/// Renames each binder of `p`, in preorder, to what `f` gives, on a stack of the parts still
/// to visit: patterns nest as deep as the program.
fn rename(p: &mut Pattern, f: &mut dyn FnMut() -> Arc<str>) {
    let mut stack = vec![p];
    while let Some(p) = stack.pop() {
        match p {
            Pattern::Bind(x) => *x = f(),
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => stack.extend(ps.iter_mut().rev()),
            Pattern::Fields(_, fs) => stack.extend(fs.iter_mut().rev().map(|(_, q)| q)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
}

fn show_src(s: &Src) -> String {
    match s {
        Src::Arg(i) => format!("argument {i}"),
        Src::Out(n, p) => format!("{n}.{p}"),
        Src::Const(v) => format!("constant {v:?}"),
    }
}

fn held(owned: bool) -> &'static str {
    if owned { "owned" } else { "borrowed" }
}

fn plural(n: u64, what: &str) -> String {
    if n == 1 {
        format!("1 {what}")
    } else {
        format!("{n} {what}s")
    }
}
