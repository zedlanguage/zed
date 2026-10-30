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

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::term::{Pattern, Prim, Term};
use zed_kernel::value::Value;
use zed_kernel::{Evaluator, KernelError};

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

/// The memory plan of graph `g`.
pub fn plan(g: &Region, fuse: bool) -> Plan {
    let p = Planner::default();
    let root = Ctx {
        r: g,
        path: "r".into(),
        up: None,
    };
    let mut regions = BTreeMap::new();
    p.region(&root, vec![Mode::Borrowed; g.args.len()], &mut regions);
    Plan { regions, fuse }
}

/// A region with the way to its enclosing one.
struct Ctx<'a> {
    r: &'a Region,
    path: String,
    up: Option<Up<'a>>,
}

/// Where a region's captures come from: argument `first_arg` on is the node's input
/// `first_input` on, in the enclosing region.
struct Up<'a> {
    ctx: &'a Ctx<'a>,
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

#[derive(Default)]
struct Planner {
    params: RefCell<HashMap<String, Vec<Mode>>>,
}

impl Planner {
    /// How the use at input `j` of node `k` takes an edge that is `owned` or not, the node
    /// being its `last` use or not.
    fn mode(&self, ctx: &Ctx<'_>, k: usize, j: usize, owned: bool, last: bool) -> Mode {
        let node = &ctx.r.nodes[k];
        let take = |b: bool| if b { Mode::Owned } else { Mode::Borrowed };
        match &node.op {
            Op::Prim(Prim::Tuple) | Op::Lambda => Mode::Owned,
            Op::Prim(Prim::Atom) => take(j >= 2),
            Op::Push(_) => take(j == 1),
            Op::Apply | Op::If if j == 0 => Mode::Borrowed,
            Op::Apply => match resolve(ctx, &node.inputs[0]) {
                Some((c, n)) => self.params(c, n).get(j - 1).copied().unwrap_or(Mode::Owned),
                None => Mode::Owned,
            },
            Op::If | Op::Match(_) if !(owned && last) => Mode::Borrowed,
            Op::Match(ps) if j == 0 => take(ps.iter().enumerate().any(|(i, p)| {
                let arm = arm_ctx(ctx, node, k, i);
                let u = Uses::of(arm.r);
                (0..binds(p)).any(|b| !u.uses[b].is_empty() && self.consumes(&arm, b))
            })),
            Op::If => take((0..2).any(|i| self.consumes(&arm_ctx(ctx, node, k, i), j - 1))),
            Op::Match(ps) => take(
                ps.iter()
                    .enumerate()
                    .any(|(i, p)| self.consumes(&arm_ctx(ctx, node, k, i), binds(p) + j - 1)),
            ),
            _ => Mode::Borrowed,
        }
    }

    /// Whether region `ctx` consumes its argument `a` when it owns it.
    fn consumes(&self, ctx: &Ctx<'_>, a: usize) -> bool {
        let u = Uses::of(ctx.r);
        let last = u.last(a);
        u.uses[a].iter().any(|at| match at {
            At::Result(_) => true,
            At::Node(k, j) => self.mode(ctx, *k, *j, true, last == Some(*k)) == Mode::Owned,
        })
    }

    /// How the lambda at node `n` of region `ctx` takes its parameters.
    fn params(&self, ctx: &Ctx<'_>, n: usize) -> Vec<Mode> {
        let body = lambda_ctx(ctx, n);
        if let Some(m) = self.params.borrow().get(&body.path) {
            return m.clone();
        }
        let k = body.up.as_ref().map_or(0, |u| u.first_arg);
        // A state argument holds no value, so it is borrowed, as in an arm.
        let m: Vec<Mode> = (0..k)
            .map(
                |i| match !body.r.args[i].is_state() && self.consumes(&body, i) {
                    true => Mode::Owned,
                    false => Mode::Borrowed,
                },
            )
            .collect();
        self.params
            .borrow_mut()
            .insert(body.path.clone(), m.clone());
        m
    }

    /// Plans region `ctx`, its arguments held as `args`, and the regions it holds.
    fn region(&self, ctx: &Ctx<'_>, args: Vec<Mode>, out: &mut BTreeMap<String, RegionPlan>) {
        let r = ctx.r;
        let u = Uses::of(r);
        let owned = |e: usize| !u.state[e] && args.get(e).is_none_or(|m| *m == Mode::Owned);
        let mut nodes: Vec<NodePlan> = r
            .nodes
            .iter()
            .enumerate()
            .map(|(k, n)| NodePlan {
                modes: (0..n.inputs.len())
                    .map(|j| match u.slot(&n.inputs[j]) {
                        Some(e) if u.state[e] => Mode::Borrowed,
                        Some(e) => self.mode(ctx, k, j, owned(e), u.last(e) == Some(k)),
                        None => self.mode(ctx, k, j, false, false),
                    })
                    .collect(),
                callee: match (&n.op, n.inputs.first()) {
                    (Op::Apply, Some(f)) => {
                        resolve(ctx, f).map(|(c, m)| format!("{}.{m}/0", c.path))
                    }
                    _ => None,
                },
                ..NodePlan::default()
            })
            .collect();
        let mut plan = RegionPlan {
            args: args.clone(),
            entry_drops: Vec::new(),
            nodes: Vec::new(),
            result_dups: Vec::new(),
        };
        let src = |e: usize| match u.base.iter().rposition(|b| *b <= e) {
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
        for (k, n) in r.nodes.iter().enumerate() {
            let m = &nodes[k].modes;
            match &n.op {
                Op::Lambda => {
                    let body = lambda_ctx(ctx, k);
                    let mut a = self.params(ctx, k);
                    a.resize(body.r.args.len(), Mode::Borrowed);
                    self.region(&body, a, out);
                }
                Op::If | Op::Match(_) => {
                    for i in 0..n.regions.len() {
                        let arm = arm_ctx(ctx, n, k, i);
                        let au = Uses::of(arm.r);
                        let b = arm.up.as_ref().map_or(0, |u| u.first_arg);
                        let mut a: Vec<Mode> = (0..b)
                            .map(|x| match m[0] == Mode::Owned && !au.uses[x].is_empty() {
                                true => Mode::Owned,
                                false => Mode::Borrowed,
                            })
                            .collect();
                        a.extend(m[1..].iter().copied());
                        for (x, e) in arm.r.args.iter().enumerate() {
                            if e.is_state() {
                                a[x] = Mode::Borrowed;
                            }
                        }
                        self.region(&arm, a, out);
                    }
                }
                _ => {}
            }
        }
        plan.nodes = nodes;
        out.insert(ctx.path.clone(), plan);
    }
}

/// The body of the lambda at node `n` of region `ctx`.
fn lambda_ctx<'a>(ctx: &'a Ctx<'a>, n: usize) -> Ctx<'a> {
    let node = &ctx.r.nodes[n];
    let body = &node.regions[0];
    Ctx {
        r: body,
        path: format!("{}.{n}/0", ctx.path),
        up: Some(Up {
            ctx,
            node,
            first_arg: body.args.len().saturating_sub(node.inputs.len()),
            first_input: 0,
        }),
    }
}

/// Arm `i` of the `if` or `match` at node `k` of region `ctx`.
fn arm_ctx<'a>(ctx: &'a Ctx<'a>, node: &'a Node, k: usize, i: usize) -> Ctx<'a> {
    let first_arg = match &node.op {
        Op::Match(ps) => binds(&ps[i]),
        _ => 0,
    };
    Ctx {
        r: &node.regions[i],
        path: format!("{}.{k}/{i}", ctx.path),
        up: Some(Up {
            ctx,
            node,
            first_arg,
            first_input: 1,
        }),
    }
}

/// The lambda node `s` is, as its region and index, when the plan can see it.
fn resolve<'a>(ctx: &'a Ctx<'a>, s: &Src) -> Option<(&'a Ctx<'a>, usize)> {
    match s {
        Src::Out(n, 0) if matches!(ctx.r.nodes[*n].op, Op::Lambda) => Some((ctx, *n)),
        Src::Arg(i) => {
            let up = ctx.up.as_ref()?;
            let s = up
                .node
                .inputs
                .get(up.first_input + i.checked_sub(up.first_arg)?)?;
            resolve(up.ctx, s)
        }
        _ => None,
    }
}

/// A heap cell: its count, 0 once freed, and its children's cells.
struct Cell {
    count: u32,
    kids: Vec<Option<usize>>,
    shared: bool,
}

/// A closure: its cell, its lambda node, the path of its body and its captures.
struct Clo<'g> {
    cell: usize,
    node: &'g Node,
    path: String,
    caps: Vec<Mv<'g>>,
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
    stats: Stats,
    live: u64,
    alone: HashMap<*const Node, Region>,
}

/// Runs graph `g` under `plan`, the kernel running each scalar and family node in `ev`, and
/// checks every count; returns the value and the counts.
pub fn run(g: &Region, plan: &Plan, ev: &mut Evaluator) -> Result<(Value, Stats), String> {
    let mut m = Machine {
        plan,
        ev,
        heap: Vec::new(),
        frames: Vec::new(),
        stats: Stats::default(),
        live: 0,
        alone: HashMap::new(),
    };
    let args = g.args.iter().map(|_| (Mv::State, false)).collect();
    let mut out = m.region(g, "r", args)?;
    let v = out.swap_remove(0);
    m.frames.push(vec![Some((v.clone(), true))]);
    m.check("the end of the run")?;
    m.frames.pop();
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

impl<'g> Machine<'g, '_> {
    fn region(
        &mut self,
        r: &'g Region,
        path: &str,
        args: Vec<(Mv<'g>, bool)>,
    ) -> Result<Vec<Mv<'g>>, String> {
        let rp = self.plan.regions.get(path).ok_or_else(|| {
            format!("memory: region `{path}` has no plan; only the root, lambda bodies and arms do")
        })?;
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
        self.frames.push(frame);
        for &a in &rp.entry_drops {
            let (v, _) = self.take(&u, &Src::Arg(a), path, "an entry drop")?;
            self.dec(v.cell())?;
        }
        self.check(&format!("the entry of `{path}`"))?;
        for (k, node) in r.nodes.iter().enumerate() {
            let at = format!("{path}.{k}");
            let np = &rp.nodes[k];
            let mut ins = Vec::new();
            for s in &node.inputs {
                ins.push(self.read(&u, s, &at)?);
            }
            for &j in &np.dups {
                self.inc(ins[j].cell());
            }
            for (j, s) in node.inputs.iter().enumerate() {
                if np.modes[j] == Mode::Owned && !np.dups.contains(&j) && u.slot(s).is_some() {
                    self.take(&u, s, &at, &format!("input {j}, taken owned"))?;
                }
            }
            let outs = self.node(node, np, &at, ins)?;
            let frame = self.frames.last_mut().expect("the region's frame");
            for (p, v) in outs.into_iter().enumerate() {
                let owned = !node.outputs[p].is_state();
                frame[u.base[k] + p] = Some((v, owned));
            }
            for s in &np.drops {
                let (v, _) = self.take(&u, s, &at, "a drop")?;
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
                self.frames.last_mut().expect("frame")[e] = None;
            }
            self.check(&format!("node {at}"))?;
        }
        let mut out = Vec::new();
        for (i, s) in r.results.iter().enumerate() {
            let v = self.read(&u, s, &format!("{path} result {i}"))?;
            if rp.result_dups.contains(&i) {
                self.inc(v.cell());
            } else if u.slot(s).is_some() && !u.state[u.slot(s).expect("an edge")] {
                self.take(&u, s, path, &format!("result {i}"))?;
            }
            out.push(v);
        }
        let frame = self.frames.pop().expect("the region's frame");
        if let Some(e) = frame.iter().position(|s| matches!(s, Some((_, true)))) {
            return Err(format!(
                "memory: `{path}` ends still owning edge {e}, a leak"
            ));
        }
        Ok(out)
    }

    /// Runs one node on its inputs, as the plan takes them; returns its outputs, owned.
    fn node(
        &mut self,
        node: &'g Node,
        np: &NodePlan,
        at: &str,
        ins: Vec<Mv<'g>>,
    ) -> Result<Vec<Mv<'g>>, String> {
        let data = |m: &Mv<'g>| matches!(m, Mv::Data(..));
        Ok(match &node.op {
            Op::Prim(p) if ins.is_empty() && p.arity().is_some() => vec![Mv::Prim(*p)],
            Op::Prim(Prim::Tuple) if ins.iter().all(data) && !ins.is_empty() => {
                let vals = ins.iter().map(value).collect();
                let cell = self.alloc(ins.iter().map(Mv::cell).collect());
                vec![Mv::Data(Value::Tuple(vals), Some(cell))]
            }
            Op::Prim(Prim::Atom) if ins.iter().all(data) => {
                let v = self.kernel(node, &ins)?;
                let names = match &ins[1] {
                    Mv::Data(Value::Tuple(ns), _) => ns.clone(),
                    _ => Vec::new(),
                };
                match &v {
                    Value::Atom(a) if !a.args.is_empty() && a.args.len() + 2 == ins.len() => {
                        let kids = (0..a.args.len())
                            .map(|i| {
                                let from = match names.is_empty() {
                                    true => i,
                                    false => names
                                        .iter()
                                        .position(|n| *n == Value::Str(a.fields[i].clone().into()))
                                        .expect("a field the atom was made with"),
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
                let v = self.kernel(node, &ins)?;
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
                    let rp = &self.plan.regions[&c.path];
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
                    self.frames.push(held);
                    let out = self.region(&c.node.regions[0], &c.path, args);
                    let held = self.frames.pop().expect("the call's frame");
                    let out = out?;
                    for (v, _) in held.into_iter().flatten() {
                        self.dec(v.cell())?;
                    }
                    out
                }
                _ => {
                    let v = self.kernel(node, &ins)?;
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
                        let t = Term::If(
                            Arc::new(self.term(c, &mut Vec::new())?),
                            Arc::new(Term::Lit(Value::Int(0))),
                            Arc::new(Term::Lit(Value::Int(1))),
                        );
                        match self.ev.run(&t).map_err(|e| e.to_string())? {
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
                        self.region(&node.regions[i], &format!("{at}/{i}"), args)?
                    }
                    Err(v) => self.failed(node, np, &ins, v)?,
                }
            }
            Op::Match(ps) => self.matched(node, ps, np, at, ins)?,
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
                let v = self.kernel(node, &ins)?;
                self.consume(np, &ins)?;
                vec![self.fresh(v), Mv::State]
            }
            _ => {
                let v = self.kernel(node, &ins)?;
                self.consume(np, &ins)?;
                vec![self.fresh(v)]
            }
        })
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
    ) -> Result<Vec<Mv<'g>>, String> {
        let mut lets = Vec::new();
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
        let t = wrap(lets, Term::Match(Arc::new(s), arms));
        let (i, vals) = match self.ev.run(&t).map_err(|e| e.to_string())? {
            Value::Tuple(mut xs) if matches!(xs.first(), Some(Value::Int(i)) if (*i as usize) < ps.len()) =>
            {
                let Value::Int(i) = xs.remove(0) else {
                    unreachable!("checked above")
                };
                (i as usize, xs)
            }
            v => return self.failed(node, np, &ins, v),
        };
        let path = format!("{at}/{i}");
        let arm = &self.plan.regions[&path];
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
                let owned = kept.contains(&b);
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
        self.region(&node.regions[i], &path, args)
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
    fn release(&mut self, cell: Option<usize>, kept: &[&[usize]]) -> Result<(), String> {
        let Some(c) = cell else { return Ok(()) };
        if kept.iter().any(|p| p.is_empty()) {
            return Ok(());
        }
        if self.heap[c].count == 1 {
            self.heap[c].count = 0;
            self.stats.frees += 1;
            self.live -= 1;
            let kids = std::mem::take(&mut self.heap[c].kids);
            for (i, k) in kids.into_iter().enumerate() {
                let sub: Vec<&[usize]> =
                    kept.iter().filter(|p| p[0] == i).map(|p| &p[1..]).collect();
                if sub.is_empty() {
                    self.dec(k)?;
                } else {
                    self.release(k, &sub)?;
                }
            }
        } else {
            for p in kept {
                let k = self.cell_at(cell, p);
                self.inc(k);
            }
            self.dec(cell)?;
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

    /// The value the kernel gives node `node` run alone on `ins`.
    fn kernel(&mut self, node: &'g Node, ins: &[Mv<'g>]) -> Result<Value, String> {
        let mut lets = Vec::new();
        let mut terms = Vec::new();
        for v in ins {
            terms.push(self.term(v, &mut lets)?);
        }
        let t = raise_with(self.alone(node), &terms)?;
        self.ev.run(&wrap(lets, t)).map_err(|e| e.to_string())
    }

    /// A one-node region running `node` on its arguments.
    fn alone(&mut self, node: &'g Node) -> &Region {
        self.alone.entry(node as *const Node).or_insert_with(|| {
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
    fn term(&mut self, v: &Mv<'g>, lets: &mut Vec<Arc<str>>) -> Result<Term, String> {
        Ok(match v {
            Mv::Data(v, _) => Term::Lit(v.clone()),
            Mv::Prim(p) => Term::PrimFn(*p),
            Mv::State => Term::Lit(Value::Tuple(Vec::new())),
            Mv::Source(p) => {
                if !lets.contains(p) {
                    lets.push(p.clone());
                }
                Term::Var(port_var(p))
            }
            Mv::Clo(c) => {
                let c = c.clone();
                let mut terms = Vec::new();
                for v in &c.caps {
                    terms.push(self.term(v, lets)?);
                }
                raise_with(self.alone(c.node), &terms)?
            }
        })
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
        match self.frames.last_mut().expect("frame")[e].take() {
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

    fn tree(&mut self, v: &Value) -> Option<usize> {
        match v {
            Value::Bool(_) | Value::Int(_) | Value::Float(_) => None,
            Value::Tuple(xs) if xs.is_empty() => None,
            Value::Atom(a) if a.args.is_empty() => None,
            Value::Tuple(xs) => {
                let kids = xs.iter().map(|x| self.tree(x)).collect();
                Some(self.alloc(kids))
            }
            Value::Atom(a) => {
                let kids = a.args.iter().map(|x| self.tree(x)).collect();
                Some(self.alloc(kids))
            }
            Value::Str(_) | Value::Big(_) | Value::Rat(_) | Value::Path(_) | Value::Family(_) => {
                Some(self.alloc(Vec::new()))
            }
        }
    }

    fn inc(&mut self, c: Option<usize>) {
        if let Some(c) = c {
            self.stats.increments += 1;
            self.heap[c].count += 1;
            if self.heap[c].count == 2 && !self.heap[c].shared {
                self.heap[c].shared = true;
                self.stats.shared += 1;
            }
        }
    }

    fn dec(&mut self, c: Option<usize>) -> Result<(), String> {
        let Some(c) = c else { return Ok(()) };
        self.stats.decrements += 1;
        if self.heap[c].count == 0 {
            return Err(format!("memory: cell {c} is dropped after it was freed"));
        }
        self.heap[c].count -= 1;
        if self.heap[c].count == 0 {
            self.stats.frees += 1;
            self.live -= 1;
            for k in std::mem::take(&mut self.heap[c].kids) {
                self.dec(k)?;
            }
        }
        Ok(())
    }

    /// Checks that each live cell's count is the number of references to it, from owned
    /// slots in every frame and from live cells, and that no slot holds a freed cell.
    fn check(&self, when: &str) -> Result<(), String> {
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
fn wrap(ports: Vec<Arc<str>>, t: Term) -> Term {
    ports.into_iter().rev().fold(t, |b, p| {
        Term::Let(port_var(&p), Arc::new(Term::Read(p)), Arc::new(b))
    })
}

/// The path of child indices to each binder of `p` inside `v`, which `p` matches, in
/// preorder.
fn binder_paths(p: &Pattern, v: &Value, at: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    let mut sub = |i: usize, q: &Pattern, x: &Value, out: &mut Vec<Vec<usize>>| {
        at.push(i);
        binder_paths(q, x, at, out);
        at.pop();
    };
    match (p, v) {
        (Pattern::Bind(_), _) => out.push(at.clone()),
        (Pattern::Tuple(ps), Value::Tuple(xs)) => {
            for (i, (q, x)) in ps.iter().zip(xs).enumerate() {
                sub(i, q, x, out);
            }
        }
        (Pattern::Atom(_, ps), Value::Atom(a)) => {
            for (i, (q, x)) in ps.iter().zip(&a.args).enumerate() {
                sub(i, q, x, out);
            }
        }
        (Pattern::Fields(_, fs), Value::Atom(a)) => {
            for (f, q) in fs {
                if let Ok(i) = a.fields.binary_search(f) {
                    sub(i, q, &a.args[i], out);
                }
            }
        }
        _ => {}
    }
}

/// Renames each binder of `p`, in preorder, to what `f` gives.
fn rename(p: &mut Pattern, f: &mut dyn FnMut() -> Arc<str>) {
    match p {
        Pattern::Bind(x) => *x = f(),
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter_mut().for_each(|q| rename(q, f)),
        Pattern::Fields(_, fs) => fs.iter_mut().for_each(|(_, q)| rename(q, f)),
        Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
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
