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
use std::fmt::{Display, Write as _};
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::eval::{Made, MadeNode, MadeShape, leaf_at_end, placed_fun_term};
use zed_kernel::paths::{Kept, Paths};
use zed_kernel::term::{Pattern, Prim, Shared, Term};
use zed_kernel::text::prose::counted;
use zed_kernel::value::{Fields, HeldEntry, HeldFamily, SharedParts, Value};
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
    /// The body of the lambda an `apply` calls, when the plan sees it, as its index in
    /// [`Plan::regions`].
    pub callee: Option<usize>,
    /// The plans of the node's regions, as indices in [`Plan::regions`]: a lambda's body, or
    /// each arm of an `if` or a `match`; none for any other node, whose regions the kernel
    /// runs.
    pub regions: Vec<usize>,
}

/// The plan of one region.
#[derive(Clone, PartialEq, Debug)]
pub struct RegionPlan {
    /// Where the region is: region `i` of node `k` of the region at index `up` of
    /// [`Plan::regions`], as `(up, k, i)`; none for the root.
    pub up: Option<(usize, usize, usize)>,
    /// How each argument is held.
    pub args: Vec<Mode>,
    /// The arguments dropped on entry, having no use.
    pub entry_drops: Vec<usize>,
    /// The nodes' plans.
    pub nodes: Vec<NodePlan>,
    /// The results that get a dup.
    pub result_dups: Vec<usize>,
}

/// A memory plan: one [`RegionPlan`] per region the machine runs, and whether `match` fuses
/// its release.
///
/// The regions are numbered in preorder, the root 0, and each region links to the region
/// holding it and each node to its regions, so a region is found from its parent's in O(1).
/// A region's path (`r`, then `r.3/0` for node 3's first region), O(depth) bytes, is worked
/// out from the links for a message only (T14-paths).
#[derive(Clone, PartialEq, Debug)]
pub struct Plan {
    /// The regions' plans, in preorder: a region, then the regions of its nodes in order.
    pub regions: Vec<RegionPlan>,
    /// Whether a `match` that owns its scrutinee releases it fused with its binders' dups.
    pub fuse: bool,
}

impl Plan {
    /// The path of region `at` (`r`, `r.3/0`), worked out from the links up.
    pub fn path(&self, at: usize) -> String {
        PathOf { plan: self, at }.to_string()
    }

    /// The index of the region at `path` (`r`, `r.3/0`), when the plan has one.
    pub fn find(&self, path: &str) -> Option<usize> {
        let mut steps = path.strip_prefix('r')?;
        let mut at = 0;
        self.regions.first()?;
        while !steps.is_empty() {
            let (k, rest) = steps.strip_prefix('.')?.split_once('/')?;
            let (i, rest) = rest.split_at(rest.find('.').unwrap_or(rest.len()));
            let (k, i): (usize, usize) = (k.parse().ok()?, i.parse().ok()?);
            at = *self.regions.get(at)?.nodes.get(k)?.regions.get(i)?;
            steps = rest;
        }
        Some(at)
    }
}

/// The plan of the region at a path, as [`Plan::find`] finds it; panics if there is none.
impl std::ops::Index<&str> for Plan {
    type Output = RegionPlan;

    fn index(&self, path: &str) -> &RegionPlan {
        let at = self.find(path);
        &self.regions[at.unwrap_or_else(|| panic!("the plan has no region `{path}`"))]
    }
}

/// The plan of the region at a path, as [`Plan::find`] finds it; panics if there is none.
impl std::ops::IndexMut<&str> for Plan {
    fn index_mut(&mut self, path: &str) -> &mut RegionPlan {
        let at = self.find(path);
        &mut self.regions[at.unwrap_or_else(|| panic!("the plan has no region `{path}`"))]
    }
}

/// The path of region `at` of `plan`, printed from the links up: O(depth), for a message.
struct PathOf<'p> {
    plan: &'p Plan,
    at: usize,
}

impl Display for PathOf<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut steps = Vec::new();
        let mut at = self.at;
        while let Some((up, k, i)) = self.plan.regions.get(at).and_then(|r| r.up) {
            steps.push((k, i));
            at = up;
        }
        f.write_str("r")?;
        for (k, i) in steps.into_iter().rev() {
            write!(f, ".{k}/{i}")?;
        }
        Ok(())
    }
}

/// The path of node `k` of region `at` of `plan` (`r.3`, `r.3/0.1`), for a message.
struct NodeAt<'p> {
    plan: &'p Plan,
    at: usize,
    k: usize,
}

impl Display for NodeAt<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let path = PathOf {
            plan: self.plan,
            at: self.at,
        };
        write!(f, "{path}.{}", self.k)
    }
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
/// arm or a lambda body consumes an argument) on a stack (step T2-mid). Each region occurrence
/// the planner meets, the root or a region of a node of one met before, gets a number the first
/// time it is met, and what the planner works out about an occurrence is kept by that number
/// (T12-Z4): its edges' uses, whether it consumes each argument it owns, how a lambda body takes
/// its parameters, and which lambda each of its arguments is captured from. Each is worked out
/// once, so a question asked again, from a branch nested above or a second call, costs O(1),
/// and planning is linear in the occurrences and their edges.
// Complexity tradeoff: the naive planner asks again, at each region, whether each region under
// it consumes each argument and what its uses are, and names each planned region by its path:
// O(k·d²) questions for k names read in a nest d deep, and O(d²) bytes of paths (COMPLEXITY.md
// Z4; 71.2 times the instructions for 8 times the depth on the 4-name nest). Here each region
// occurrence gets a number once, by its parent occurrence, node and region index in a map, and
// every answer is kept by that number, and planned regions are numbered in preorder and linked
// to their parents, a path being worked out for a message only: O(occurrences + edges) time
// and memory. Tradeoff: the answers of every occurrence are held until planning ends. Nothing
// is refused. Tests
// `l01_34_memory::chains`.
pub fn plan(g: &Region, fuse: bool) -> Plan {
    let mut p = Planner {
        occs: vec![Occ {
            r: g,
            at: None,
            up: None,
            uses: None,
            params: None,
        }],
        ids: HashMap::new(),
        consumes: HashMap::new(),
        resolved: HashMap::new(),
    };
    let mut regions = Vec::new();
    // Each region still to plan: the occurrence of the region holding it, the node and region
    // it is, and how its arguments are held. They are planned in preorder, so a region's index
    // is known before the regions under it are planned.
    let mut todo: Vec<(usize, usize, usize, Vec<Mode>)> = Vec::new();
    // Each `apply` whose callee the plan sees, as its region's index, its node and the
    // occurrence of the callee's body, which may be planned after it.
    let mut calls = Vec::new();
    let args = vec![Mode::Borrowed; g.args.len()];
    p.region(0, args, None, &mut regions, &mut todo, &mut calls);
    while let Some((c, k, i, args)) = todo.pop() {
        let o = p.sub(c, k, i);
        let up = p.occs[c]
            .at
            .expect("a region is planned before the regions under it");
        p.region(
            o,
            args,
            Some((up, k, i)),
            &mut regions,
            &mut todo,
            &mut calls,
        );
    }
    for (at, k, body) in calls {
        regions[at].nodes[k].callee = Some(
            p.occs[body]
                .at
                .expect("a lambda's body is planned with the region holding the lambda"),
        );
    }
    Plan { regions, fuse }
}

/// A region occurrence: the region, its index in the plan once planned, the way to its
/// enclosing occurrence, and what the planner has worked out about it so far.
struct Occ<'a> {
    r: &'a Region,
    at: Option<usize>,
    up: Option<Up<'a>>,
    /// Its edges and their uses, once a question has needed them.
    uses: Option<Uses>,
    /// How it takes its parameters, for a lambda body, once a question has asked.
    params: Option<Vec<Mode>>,
}

/// Where a region's captures come from: argument `first_arg` on is the node's input
/// `first_input` on, in the enclosing region, occurrence `occ`.
struct Up<'a> {
    occ: usize,
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
    /// The region occurrences met, by number: the root is 0.
    occs: Vec<Occ<'a>>,
    /// The number of region `i` of node `k` of occurrence `o`, by `(o, k, i)`.
    ids: HashMap<(usize, usize, usize), usize>,
    /// Whether occurrence `o` consumes its argument `a` when it owns it, by `(o, a)`.
    consumes: HashMap<(usize, usize), bool>,
    /// The lambda argument `a` of occurrence `o` is captured from, as in [`Planner::resolve`],
    /// by `(o, a)`.
    resolved: HashMap<(usize, usize), Option<(usize, usize)>>,
}

/// A question the planner answers: how the use at input `j` of node `k` of occurrence `ctx`
/// takes an edge (`Owned` is true), whether occurrence `ctx` consumes its argument `a` when it
/// owns it (the answer goes in `Planner::consumes`), or how the lambda body `body` takes its
/// parameters (the answer goes in its `Occ::params`).
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
    /// Whether occurrence `ctx` consumes argument `a`, whose last use is at node `last`: use
    /// `next` on is still to ask about.
    Consumes {
        ctx: usize,
        a: usize,
        next: usize,
        last: Option<usize>,
    },
    /// The mode of argument `j` of an `apply` whose callee is the lambda body `body`.
    Callee { body: usize, j: usize },
    /// The mode of capture `j` of the `if` or `match` at node `k` of occurrence `ctx`, with
    /// `n` arms: arm `i` on is still to ask.
    Arms {
        ctx: usize,
        k: usize,
        j: usize,
        i: usize,
        n: usize,
    },
    /// The mode of the scrutinee of the `match` at node `k` of occurrence `ctx`: binder `b` on
    /// of arm `i`, occurrence `arm` once entered, is still to ask.
    Scrutinee {
        ctx: usize,
        k: usize,
        ps: &'a [Pattern],
        i: usize,
        b: usize,
        arm: Option<usize>,
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

    /// How the lambda at node `n` of occurrence `ctx` takes its parameters.
    fn params(&mut self, ctx: usize, n: usize) -> Vec<Mode> {
        let body = self.sub(ctx, n, 0);
        self.answer(Ask::Params { body });
        self.occs[body]
            .params
            .clone()
            .expect("a Params question records the body's parameters")
    }

    /// The uses of occurrence `o`'s edges, worked out the first time they are asked for.
    fn uses(&mut self, o: usize) -> &Uses {
        let r = self.occs[o].r;
        self.occs[o].uses.get_or_insert_with(|| Uses::of(r))
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
                let node: &'a Node = &self.occs[ctx].r.nodes[k];
                match &node.op {
                    Op::Prim(Prim::Tuple) | Op::Lambda => Step::Done(true),
                    Op::Prim(Prim::Atom) => Step::Done(j >= 2),
                    Op::Push(_) => Step::Done(j == 1),
                    Op::Apply | Op::If if j == 0 => Step::Done(false),
                    Op::Apply => match self.resolve(ctx, &node.inputs[0]) {
                        Some((c, n)) => {
                            let body = self.sub(c, n, 0);
                            waits.push(Wait::Callee { body, j });
                            Step::Ask(Ask::Params { body })
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
                        };
                        self.resume(w, None, waits)
                    }
                    Op::If | Op::Match(_) => {
                        let n = match &node.op {
                            Op::Match(ps) => ps.len(),
                            _ => 2,
                        };
                        let w = Wait::Arms { ctx, k, j, i: 0, n };
                        self.resume(w, None, waits)
                    }
                    _ => Step::Done(false),
                }
            }
            Ask::Consumes { ctx, a } => {
                if let Some(&b) = self.consumes.get(&(ctx, a)) {
                    return Step::Done(b);
                }
                let last = self.uses(ctx).last(a);
                let w = Wait::Consumes {
                    ctx,
                    a,
                    next: 0,
                    last,
                };
                self.resume(w, None, waits)
            }
            Ask::Params { body } => {
                if self.occs[body].params.is_some() {
                    return Step::Done(false);
                }
                let k = self.occs[body].up.as_ref().map_or(0, |u| u.first_arg);
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
                mut next,
                last,
            } => {
                let at = match got {
                    Some(true) => None,
                    _ => self.uses(ctx).uses[a].get(next).copied(),
                };
                let consumed = match at {
                    None => got == Some(true),
                    Some(At::Result(_)) => true,
                    Some(At::Node(k, j)) => {
                        next += 1;
                        waits.push(Wait::Consumes { ctx, a, next, last });
                        return Step::Ask(Ask::Mode {
                            ctx,
                            k,
                            j,
                            owned: true,
                            last: last == Some(k),
                        });
                    }
                };
                self.consumes.insert((ctx, a), consumed);
                Step::Done(consumed)
            }
            Wait::Callee { body, j } => {
                let m = self.occs[body]
                    .params
                    .as_ref()
                    .expect("a Params question records the body's parameters")
                    .get(j - 1)
                    .copied()
                    .unwrap_or(Mode::Owned);
                Step::Done(m == Mode::Owned)
            }
            Wait::Arms {
                ctx,
                k,
                j,
                mut i,
                n,
            } => {
                if got == Some(true) {
                    return Step::Done(true);
                }
                if i == n {
                    return Step::Done(false);
                }
                let arm = self.sub(ctx, k, i);
                let a = self.occs[arm].up.as_ref().map_or(0, |u| u.first_arg) + j - 1;
                i += 1;
                waits.push(Wait::Arms { ctx, k, j, i, n });
                Step::Ask(Ask::Consumes { ctx: arm, a })
            }
            Wait::Scrutinee {
                ctx,
                k,
                ps,
                mut i,
                mut b,
                mut arm,
            } => {
                if got == Some(true) {
                    return Step::Done(true);
                }
                loop {
                    let Some(o) = arm else {
                        if i == ps.len() {
                            return Step::Done(false);
                        }
                        arm = Some(self.sub(ctx, k, i));
                        b = 0;
                        continue;
                    };
                    if b < binds(&ps[i]) {
                        b += 1;
                        if self.uses(o).uses[b - 1].is_empty() {
                            continue;
                        }
                        waits.push(Wait::Scrutinee {
                            ctx,
                            k,
                            ps,
                            i,
                            b,
                            arm,
                        });
                        return Step::Ask(Ask::Consumes { ctx: o, a: b - 1 });
                    }
                    arm = None;
                    i += 1;
                }
            }
            Wait::Params { body, k, mut modes } => {
                if let Some(g) = got {
                    modes.push(mode_of(g));
                }
                // A state argument holds no value, so it is borrowed, as in an arm.
                while modes.len() < k && self.occs[body].r.args[modes.len()].is_state() {
                    modes.push(Mode::Borrowed);
                }
                if modes.len() < k {
                    let a = modes.len();
                    waits.push(Wait::Params { body, k, modes });
                    return Step::Ask(Ask::Consumes { ctx: body, a });
                }
                self.occs[body].params = Some(modes);
                Step::Done(false)
            }
        }
    }

    /// Plans occurrence `ctx`, its arguments held as `args`, region `i` of node `k` of the
    /// region at index `up` of `out` as `(up, k, i)`, or the root: pushes its plan on `out`, the
    /// regions it holds on `todo` and the calls whose callee it sees on `calls`.
    fn region(
        &mut self,
        ctx: usize,
        args: Vec<Mode>,
        up: Option<(usize, usize, usize)>,
        out: &mut Vec<RegionPlan>,
        todo: &mut Vec<(usize, usize, usize, Vec<Mode>)>,
        calls: &mut Vec<(usize, usize, usize)>,
    ) {
        let at = out.len();
        let r: &'a Region = self.occs[ctx].r;
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
            if let (Op::Apply, Some(f)) = (&n.op, n.inputs.first())
                && let Some((c, m)) = self.resolve(ctx, f)
            {
                calls.push((at, k, self.sub(c, m, 0)));
            }
            nodes.push(NodePlan {
                modes,
                ..NodePlan::default()
            });
        }
        let (mut entry_drops, mut result_dups) = (Vec::new(), Vec::new());
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
                        Src::Arg(a) => entry_drops.push(a),
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
                    At::Result(i) => result_dups.push(i),
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
        let plan = RegionPlan {
            up,
            args,
            entry_drops,
            nodes,
            result_dups,
        };
        if let Some((up, k, i)) = up {
            let subs = &mut out[up].nodes[k].regions;
            debug_assert_eq!(subs.len(), i, "a node's regions are planned in order");
            subs.push(at);
        }
        self.occs[ctx].at = Some(at);
        out.push(plan);
    }

    /// The occurrence of region `i` of node `k` of occurrence `ctx`, a lambda's body or an arm
    /// of an `if` or a `match`, numbered the first time it is met.
    fn sub(&mut self, ctx: usize, k: usize, i: usize) -> usize {
        let next = self.occs.len();
        let o = *self.ids.entry((ctx, k, i)).or_insert(next);
        if o == next {
            let c = &self.occs[ctx];
            let node: &'a Node = &c.r.nodes[k];
            let (first_arg, first_input) = match &node.op {
                Op::Lambda => (
                    node.regions[0].args.len().saturating_sub(node.inputs.len()),
                    0,
                ),
                Op::Match(ps) => (binds(&ps[i]), 1),
                _ => (0, 1),
            };
            self.occs.push(Occ {
                r: &node.regions[i],
                at: None,
                up: Some(Up {
                    occ: ctx,
                    node,
                    first_arg,
                    first_input,
                }),
                uses: None,
                params: None,
            });
        }
        o
    }

    /// The lambda node `s` of occurrence `ctx` is, as its occurrence and index, when the plan
    /// can see it. A capture is followed out through the regions holding it, in a loop, and
    /// each argument passed on the way keeps the answer, so a capture `d` regions deep is
    /// followed once and not once per call.
    fn resolve(&mut self, mut ctx: usize, mut s: &'a Src) -> Option<(usize, usize)> {
        let mut passed = Vec::new();
        let found = loop {
            let c = &self.occs[ctx];
            match s {
                Src::Out(n, 0) if matches!(c.r.nodes[*n].op, Op::Lambda) => break Some((ctx, *n)),
                Src::Arg(i) => {
                    if let Some(&f) = self.resolved.get(&(ctx, *i)) {
                        break f;
                    }
                    passed.push((ctx, *i));
                    let Some(up) = c.up.as_ref() else {
                        break None;
                    };
                    let Some(next) = i
                        .checked_sub(up.first_arg)
                        .and_then(|x| up.node.inputs.get(up.first_input + x))
                    else {
                        break None;
                    };
                    s = next;
                    ctx = up.occ;
                }
                _ => break None,
            }
        };
        for at in passed {
            self.resolved.insert(at, found);
        }
        found
    }
}

/// A heap cell: its count, 0 once freed, and its children's cells.
struct Cell {
    count: u32,
    kids: Vec<Option<usize>>,
    shared: bool,
}

/// A closure: its cell, its lambda node and that node's occurrence id, where the node is (node
/// `k` of the region at index `at` of the plan) and its captures.
struct Clo<'g> {
    cell: usize,
    node: &'g Node,
    id: usize,
    at: usize,
    k: usize,
    caps: Vec<Mv<'g>>,
}

/// An atom's name and its field names, sorted, empty for a payload by position.
type AtomName = (Arc<str>, Fields);

/// A tuple or an atom with a part that is no data: a function, or a tuple or an atom that holds
/// one (DESIGN.md step L1.17, QUESTIONS A43). Its cell's kids are its parts' cells, as a data
/// tuple's are, so counting, the fused release and the audit treat the two alike; only reading
/// it as a [`Value`] is not possible, so the machine reads its parts here and never hands it to
/// the kernel as a literal (see [`Machine::term`]).
// Complexity tradeoff: the naive form would put closures inside `Value`, so every data
// structure, its order and its hash would carry them; the kernel keeps a second form
// (`V::Held`) for the same reason. Used: this form, made only when a part is no data, so a data
// tuple keeps its path; building is O(parts), reading a part O(1), and the binders of a
// `match` on it are found by one walk of the pattern, O(pattern). Given up: the kernel picks
// the arm of such a `match` from the value rebuilt as a term, O(size of the value), as it
// already does for a data scrutinee. Nothing is refused. Tests
// `l01_36_cranelift::function_binders`, `l01_36_cranelift::held_values` and
// `bench::held_values` (COMPLEXITY.md row HELD-cells).
struct Held<'g> {
    cell: usize,
    /// What it is.
    shape: HeldKind,
    /// The components of a tuple, the payload of an atom in the order of its field names, or
    /// the entries of a family that are no data, numbered as its [`HeldFamily`] numbers them.
    parts: Vec<Mv<'g>>,
}

/// What a [`Held`] is, as the native runtime's `HeldShape`.
enum HeldKind {
    /// A tuple.
    Tuple,
    /// An atom: its name and its field names, sorted, empty for a payload by position.
    Atom(AtomName),
    /// A family with an entry that is no data (DESIGN.md sec:values_morphisms, row
    /// FAIL-machine-held-family): its keys and its data entries; each other entry is a part.
    Family(Box<HeldFamily>),
}

impl Held<'_> {
    fn is_tuple(&self) -> bool {
        matches!(self.shape, HeldKind::Tuple)
    }

    fn family(&self) -> Option<&HeldFamily> {
        match &self.shape {
            HeldKind::Family(f) => Some(f),
            _ => None,
        }
    }
}

/// A closure the kernel made and gave back, which has no lambda node: its cell, its lambda's
/// parameters and body, the name of each capture and the captures. The native runtime's
/// `Obj::Fun` (rows FAIL-native-fam-result-holds-function, FAIL-machine-held-family). A call
/// of it runs in the kernel.
struct Fun<'g> {
    cell: usize,
    params: Vec<Arc<str>>,
    body: Shared,
    names: Vec<Arc<str>>,
    caps: Vec<Mv<'g>>,
    /// The table the kernel's `place` gave the closure, if any (`MadeFun::placed`).
    placed: Option<Value>,
}

/// Drops `parts`; the closures and held values it alone holds are taken apart through a list,
/// not by recursion: they nest as deep as the program (step T2-mid).
fn drop_parts(mut parts: Vec<Mv<'_>>) {
    while let Some(m) = parts.pop() {
        match m {
            Mv::Clo(rc) => {
                if let Ok(mut c) = Rc::try_unwrap(rc) {
                    parts.append(&mut c.caps);
                }
            }
            Mv::Held(rc) => {
                if let Ok(mut h) = Rc::try_unwrap(rc) {
                    parts.append(&mut h.parts);
                }
            }
            Mv::Fun(rc) => {
                if let Ok(mut f) = Rc::try_unwrap(rc) {
                    parts.append(&mut f.caps);
                }
            }
            _ => {}
        }
    }
}

impl Drop for Fun<'_> {
    fn drop(&mut self) {
        drop_parts(std::mem::take(&mut self.caps));
    }
}

impl Drop for Clo<'_> {
    fn drop(&mut self) {
        drop_parts(std::mem::take(&mut self.caps));
    }
}

impl Drop for Held<'_> {
    fn drop(&mut self) {
        drop_parts(std::mem::take(&mut self.parts));
    }
}

/// A value in the machine.
#[derive(Clone)]
enum Mv<'g> {
    /// Data, with its cell unless it is unboxed or static.
    Data(Value, Option<usize>),
    /// A closure.
    Clo(Rc<Clo<'g>>),
    /// A tuple, an atom or a family that holds a function.
    Held(Rc<Held<'g>>),
    /// A closure the kernel made.
    Fun(Rc<Fun<'g>>),
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
            Mv::Held(h) => Some(h.cell),
            Mv::Fun(f) => Some(f.cell),
            _ => None,
        }
    }

    /// Whether `self` is no data: a function, or a tuple, an atom or a family that holds one.
    /// A port's state is neither.
    fn holds_function(&self) -> bool {
        matches!(
            self,
            Mv::Clo(_) | Mv::Fun(_) | Mv::Prim(_) | Mv::Source(_) | Mv::Held(_)
        )
    }

    /// Whether `self` is an atom that holds a function: a failure, which passes through a
    /// primitive and an `if` as a data atom does.
    fn held_atom(&self) -> bool {
        matches!(self, Mv::Held(h) if matches!(h.shape, HeldKind::Atom(_)))
    }

    /// Whether `self` is a held tuple.
    fn held_tuple(&self) -> bool {
        matches!(self, Mv::Held(h) if h.is_tuple())
    }

    /// Whether `self` is a held family.
    fn held_family(&self) -> bool {
        matches!(self, Mv::Held(h) if h.family().is_some())
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
    /// The occurrence id of the first node of each planned region, by its index in the plan:
    /// the regions are numbered in the plan's order, and node `k` of a region is its first id
    /// plus `k`, so an id depends only on where the node stands in the graph, never on where it
    /// is in memory (step ADDR-memory).
    first: Vec<usize>,
    /// The one-node region of each node occurrence the kernel has run, by its occurrence id.
    alone: Vec<Option<Region>>,
}

/// Runs graph `g` under `plan`, the kernel running each scalar and family node in `ev`, and
/// checks every count; returns the value and the counts.
pub fn run(g: &Region, plan: &Plan, ev: &mut Evaluator) -> Result<(Value, Stats), String> {
    let mut first = Vec::with_capacity(plan.regions.len());
    let mut ids = 0;
    for rp in &plan.regions {
        first.push(ids);
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
        first,
        alone: (0..ids).map(|_| None).collect(),
    };
    let args = g.args.iter().map(|_| (Mv::State, false)).collect();
    let mut out = m.region(g, args)?;
    let v = out.swap_remove(0);
    m.push_frame(vec![Some((v.clone(), true))]);
    m.check(&"the end of the run")?;
    m.pop_frame();
    m.dec(v.cell())?;
    if m.live != 0 {
        return Err(format!(
            "memory: {} live after the result is dropped",
            counted(m.live, "cell")
        ));
    }
    match v {
        Mv::Data(v, _) => Ok((v, m.stats)),
        Mv::Held(_) => {
            Err(KernelError::Type("the program's result holds a function".into()).to_string())
        }
        _ => Err(KernelError::Type("the program's result is a function".into()).to_string()),
    }
}

/// A part waiting in [`Machine::release`]: one to drop, or one with its nodes in [`Kept`] on
/// the way to a kept binder.
enum Part {
    Drop(Option<usize>),
    Keep(Option<usize>, Vec<usize>),
}

/// A region the machine is running: its index `at` in the plan, its plan, the occurrence id of
/// its first node, its edges' uses, the node it is at, and whether that node, an `apply`, holds
/// a frame of the arguments it passes owned to a callee that borrows them.
struct Running<'g> {
    r: &'g Region,
    at: usize,
    first: usize,
    rp: &'g RegionPlan,
    u: Uses,
    k: usize,
    held: bool,
}

/// What a node gives: its outputs, or a region to run, at index `at` in the plan, whose
/// results are its outputs.
enum Out<'g> {
    Done(Vec<Mv<'g>>),
    Call {
        r: &'g Region,
        at: usize,
        args: Vec<(Mv<'g>, bool)>,
        held: bool,
    },
}

impl<'g> Machine<'g, '_> {
    /// Runs region `r` on `args`, and the regions its nodes call, on a stack of running
    /// regions: calls and arms nest as deep as the program and its run (step T2-mid).
    fn region(&mut self, r: &'g Region, args: Vec<(Mv<'g>, bool)>) -> Result<Vec<Mv<'g>>, String> {
        if self.plan.regions.is_empty() {
            return Err(
                "memory: region `r` has no plan; only the root, lambda bodies and arms do".into(),
            );
        }
        let mut stack = vec![self.enter(r, 0, args)?];
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
            match self.node(node, top.first + top.k, top.at, top.k, ins)? {
                Out::Done(outs) => self.finish(top, outs)?,
                Out::Call { r, at, args, held } => {
                    top.held = held;
                    let callee = self.enter(r, at, args)?;
                    stack.push(callee);
                }
            }
        }
    }

    /// The index in the plan of region `i` of node `k` of the region at index `at`.
    fn sub(&self, at: usize, k: usize, i: usize) -> Result<usize, String> {
        self.plan.regions[at].nodes[k]
            .regions
            .get(i)
            .copied()
            .ok_or_else(|| {
                format!(
                    "memory: region `{}/{i}` has no plan; only the root, lambda bodies and arms do",
                    self.node_at(at, k)
                )
            })
    }

    /// The path of the region at index `at` of the plan, for a message.
    fn path(&self, at: usize) -> PathOf<'g> {
        PathOf {
            plan: self.plan,
            at,
        }
    }

    /// The path of node `k` of the region at index `at` of the plan, for a message.
    fn node_at(&self, at: usize, k: usize) -> NodeAt<'g> {
        NodeAt {
            plan: self.plan,
            at,
            k,
        }
    }

    /// Enters region `r`, at index `at` of the plan, on `args`: checks how they arrive, and
    /// makes its frame.
    fn enter(
        &mut self,
        r: &'g Region,
        at: usize,
        args: Vec<(Mv<'g>, bool)>,
    ) -> Result<Running<'g>, String> {
        let (rp, path) = (&self.plan.regions[at], self.path(at));
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
            let (v, _) = self.take(&u, &Src::Arg(a), &path, &"an entry drop")?;
            self.dec(v.cell())?;
        }
        self.check(&format_args!("the entry of `{path}`"))?;
        Ok(Running {
            r,
            at,
            first: self.first[at],
            rp,
            u,
            k: 0,
            held: false,
        })
    }

    /// Reads the inputs of the node region `run` is at, as its plan takes them.
    fn inputs(&mut self, run: &Running<'g>) -> Result<Vec<Mv<'g>>, String> {
        let (node, np, u) = (&run.r.nodes[run.k], &run.rp.nodes[run.k], &run.u);
        let at = self.node_at(run.at, run.k);
        let mut ins = Vec::new();
        for s in &node.inputs {
            ins.push(self.read(u, s, &at)?);
        }
        let mut dup = vec![false; node.inputs.len()];
        for &j in &np.dups {
            dup[j] = true;
            self.inc(ins[j].cell());
        }
        for (j, s) in node.inputs.iter().enumerate() {
            if np.modes[j] == Mode::Owned && !dup[j] && u.slot(s).is_some() {
                self.take(u, s, &at, &format_args!("input {j}, taken owned"))?;
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
        let (k, node, np, u) = (run.k, &run.r.nodes[run.k], &run.rp.nodes[run.k], &run.u);
        let at = self.node_at(run.at, k);
        for (p, v) in outs.into_iter().enumerate() {
            let owned = !node.outputs[p].is_state();
            self.set(u.base[k] + p, Some((v, owned)));
        }
        for s in &np.drops {
            let (v, _) = self.take(u, s, &at, &"a drop")?;
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
        self.check(&format_args!("node {at}"))?;
        run.k += 1;
        Ok(())
    }

    /// Leaves region `run`, all its nodes run: gives its results and drops its frame.
    fn leave(&mut self, run: &Running<'g>) -> Result<Vec<Mv<'g>>, String> {
        let (r, rp, u, path) = (run.r, run.rp, &run.u, self.path(run.at));
        let dup: HashSet<usize> = rp.result_dups.iter().copied().collect();
        let mut out = Vec::new();
        for (i, s) in r.results.iter().enumerate() {
            let v = self.read(u, s, &format_args!("{path} result {i}"))?;
            if dup.contains(&i) {
                self.inc(v.cell());
            } else if u.slot(s).is_some() && !u.state[u.slot(s).expect("an edge")] {
                self.take(u, s, &path, &format_args!("result {i}"))?;
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

    /// Runs one node, occurrence `id`, node `k` of the region at index `at` of the plan, on its
    /// inputs, as the plan takes them; returns its outputs, owned.
    fn node(
        &mut self,
        node: &'g Node,
        id: usize,
        at: usize,
        k: usize,
        ins: Vec<Mv<'g>>,
    ) -> Result<Out<'g>, String> {
        let plan = self.plan;
        let np = &plan.regions[at].nodes[k];
        let here = self.node_at(at, k);
        let data = |m: &Mv<'g>| matches!(m, Mv::Data(..));
        Ok(Out::Done(match &node.op {
            Op::Prim(p) if ins.is_empty() && p.arity().is_some() => vec![Mv::Prim(*p)],
            // A tuple or an atom with a part that is no data is a held value, its parts moved
            // into its cell as a data tuple's are (DESIGN.md step L1.17).
            Op::Prim(Prim::Tuple) if ins.iter().any(Mv::holds_function) => {
                let kids = ins.iter().map(Mv::cell).collect();
                vec![self.held(HeldKind::Tuple, kids, ins)]
            }
            // A display with an entry that is no data is a held family, as native code makes
            // it (`held_entries` in zed-native's hooks.rs); a key that is no data, or entries
            // the kernel refuses, are the kernel's error.
            Op::Prim(Prim::Entries) if ins.iter().any(Mv::holds_function) => {
                match held_entries(&ins) {
                    Some((f, parts)) => {
                        for p in &parts {
                            self.inc(p.cell());
                        }
                        let kids = parts.iter().map(Mv::cell).collect();
                        let m = self.held(HeldKind::Family(Box::new(f)), kids, parts);
                        self.consume(np, &ins)?;
                        vec![m]
                    }
                    None => vec![self.slow(node, id, np, &ins)?],
                }
            }
            // A held family read: the entry, owned, or what the kernel gives where it is not
            // this one's to make.
            Op::Prim(p) if family_at(*p, &ins).is_some() => match self.family_read(*p, &ins) {
                Some(m) => {
                    self.consume(np, &ins)?;
                    vec![m]
                }
                None => vec![self.slow(node, id, np, &ins)?],
            },
            Op::Prim(Prim::Atom)
                if ins.len() > 2
                    && ins[..2].iter().all(data)
                    && ins[2..].iter().any(Mv::holds_function) =>
            {
                match self.held_shape(node, id, &ins) {
                    Some((atom, order)) => {
                        let parts: Vec<Mv<'g>> =
                            order.iter().map(|&i| ins[2 + i].clone()).collect();
                        let kids = parts.iter().map(Mv::cell).collect();
                        vec![self.held(HeldKind::Atom(atom), kids, parts)]
                    }
                    // The kernel refuses the atom: its error.
                    None => vec![self.slow(node, id, np, &ins)?],
                }
            }
            // A held tuple read at a key: the part, or what the kernel gives for a key outside
            // it (`#outOfBounds`, or a data atom key given back).
            Op::Prim(Prim::TupleGet | Prim::At) if ins.len() == 2 && ins[0].held_tuple() => {
                match read_held(&ins[0], &ins[1]) {
                    Some(m) => {
                        let m = m.clone();
                        self.give(np, &ins, m)?
                    }
                    None => vec![self.slow(node, id, np, &ins)?],
                }
            }
            // Any other primitive given a held value: an atom that holds a function passes
            // through as a failure does, and anything else is the kernel's error.
            Op::Prim(p) if ins.iter().any(|m| matches!(m, Mv::Held(_))) => match passed(*p, &ins) {
                Some(m) => {
                    let m = m.clone();
                    self.give(np, &ins, m)?
                }
                None => vec![self.slow(node, id, np, &ins)?],
            },
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
                    Value::Atom(a) if !a.args().is_empty() && a.args().len() + 2 == ins.len() => {
                        let at: BTreeMap<&Value, usize> =
                            names.iter().enumerate().map(|(i, n)| (n, i)).collect();
                        let kids = (0..a.args().len())
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
                    // A key outside the tuple is `#outOfBounds`, a fresh value.
                    (Mv::Data(Value::Tuple(_), Some(c)), Mv::Data(Value::Int(i), _))
                        if let Some(kid) = usize::try_from(*i)
                            .ok()
                            .and_then(|i| self.heap[*c].kids.get(i).copied()) =>
                    {
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
                    at,
                    k,
                    caps: ins,
                }))]
            }
            Op::Apply => match &ins[0] {
                Mv::Clo(c)
                    if c.node.regions[0].args.len() == c.node.inputs.len() + ins.len() - 1 =>
                {
                    // The body's plan first: a body with no plan is reported as such, not as a
                    // call to the wrong region.
                    let body = self.sub(c.at, c.k, 0)?;
                    if let Some(want) = np.callee
                        && want != body
                    {
                        return Err(format!(
                            "memory: {here}: the plan calls `{}`, and the callee is `{}/0`",
                            self.path(want),
                            self.node_at(c.at, c.k)
                        ));
                    }
                    let rp = &plan.regions[body];
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
                                    "memory: {here}: argument {i} is passed borrowed to `{}`, \
                                     which consumes it",
                                    self.path(body)
                                ));
                            }
                        }
                    }
                    args.extend(c.caps.iter().map(|v| (v.clone(), false)));
                    self.push_frame(held);
                    let callee: &'g Node = c.node;
                    return Ok(Out::Call {
                        r: &callee.regions[0],
                        at: body,
                        args,
                        held: true,
                    });
                }
                _ => {
                    // A held family applied to a key is read at it, as the kernel applies it;
                    // a primitive called on one reads it as the primitive's node does.
                    let read = family_called(&ins).map(|(p, a)| self.family_read(p, &ins[a..]));
                    let mut out = match (read, called(&ins)) {
                        (Some(Some(m)), _) => {
                            self.consume(np, &ins)?;
                            vec![m]
                        }
                        (None, Some(m)) => {
                            let m = m.clone();
                            self.give(np, &ins, m)?
                        }
                        _ => vec![self.slow(node, id, np, &ins)?],
                    };
                    out.resize(node.outputs.len(), Mv::State);
                    out
                }
            },
            // An atom that holds a function passes through an `if` as any failure does.
            Op::If if ins[0].held_atom() => {
                let m = ins[0].clone();
                let mut out = self.give(np, &ins, m)?;
                out.extend(node.outputs[1..].iter().map(|_| Mv::State));
                out
            }
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
                        return Ok(Out::Call {
                            r: &node.regions[i],
                            at: self.sub(at, k, i)?,
                            args,
                            held: false,
                        });
                    }
                    Err(v) => self.failed(node, np, &ins, v)?,
                }
            }
            Op::Match(ps) => return self.matched(node, ps, at, k, ins),
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
            Op::Push(_) => vec![self.slow(node, id, np, &ins)?, Mv::State],
            _ => vec![self.slow(node, id, np, &ins)?],
        }))
    }

    /// A `match`: the kernel picks the arm and binds its values, and the machine finds the
    /// binders' cells inside the scrutinee's and releases the scrutinee.
    ///
    /// A function scrutinee (a closure, a primitive or a lookup port) is no data, so the
    /// kernel cannot give it back in a tuple. A pattern that matches a function binds it
    /// whole or not at all (data holds no function), so the kernel gives `()` in each
    /// binder's place and each binder of the arm is the scrutinee itself, at the empty path.
    fn matched(
        &mut self,
        node: &'g Node,
        ps: &[Pattern],
        at: usize,
        k: usize,
        ins: Vec<Mv<'g>>,
    ) -> Result<Out<'g>, String> {
        let plan = self.plan;
        let np = &plan.regions[at].nodes[k];
        let data = matches!(ins[0], Mv::Data(..));
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
                xs.push(if data {
                    Term::Var(x.clone())
                } else {
                    Term::Lit(Value::tuple(Vec::new()))
                });
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
        let sub = self.sub(at, k, i)?;
        let arm = &plan.regions[sub];
        // Each binder's node in `paths`; a function scrutinee is bound whole, at the root, and
        // a held one is walked: the kernel cannot give its parts back, which may be functions.
        let mut paths = Paths::default();
        let mut nodes = Vec::new();
        let mut parts = Vec::new();
        match &ins[0] {
            Mv::Data(v, _) => {
                let mut found = Vec::new();
                binder_paths(&ps[i], v, Paths::ROOT, &mut paths, &mut found);
                nodes.extend(found.into_iter().map(|(n, _)| n));
            }
            Mv::Held(_) => held_binders(&ps[i], &ins[0], &mut paths, &mut nodes, &mut parts),
            _ => nodes.resize(vals.len(), Paths::ROOT),
        }
        // Binder `b`, of kernel value `v`, with cell `cell`; for a function scrutinee, the
        // scrutinee; for a held one, its part. A part that is no data and that the arm does
        // not own is never read (an owned scrutinee is released before the arm, with what the
        // arm does not keep), so it is a placeholder holding no cell.
        let bound = |b: usize, v: Value, cell: Option<usize>, owned: bool| match &ins[0] {
            Mv::Data(..) => Mv::Data(v, cell),
            Mv::Held(_) => match &parts[b] {
                Mv::Data(v, _) => Mv::Data(v.clone(), cell),
                _ if !owned && np.modes[0] == Mode::Owned => Mv::State,
                m => m.clone(),
            },
            m => m.clone(),
        };
        let scrut = ins[0].cell();
        // The cell at each node, from its parent's: a parent comes before its children.
        let mut cell_of: Vec<Option<usize>> = Vec::with_capacity(paths.below().len() + 1);
        cell_of.push(scrut);
        for &(up, i) in paths.below() {
            cell_of.push(cell_of[up].and_then(|c| self.heap[c].kids.get(i).copied().flatten()));
        }
        let cells: Vec<Option<usize>> = (0..vals.len())
            .map(|b| nodes.get(b).and_then(|&n| cell_of[n]))
            .collect();
        let mut args = Vec::new();
        if np.modes[0] == Mode::Owned {
            let kept: Vec<usize> = (0..vals.len())
                .filter(|b| arm.args[*b] == Mode::Owned)
                .collect();
            if self.plan.fuse {
                let kept_nodes: Vec<usize> =
                    kept.iter().filter_map(|b| nodes.get(*b).copied()).collect();
                self.release(scrut, &Kept::new(&paths, &kept_nodes))?;
            } else {
                for b in &kept {
                    self.inc(cells[*b]);
                }
                self.dec(scrut)?;
            }
            for (b, v) in vals.into_iter().enumerate() {
                let owned = arm.args[b] == Mode::Owned;
                args.push((
                    bound(b, v, if owned { cells[b] } else { None }, owned),
                    owned,
                ));
            }
        } else {
            for (b, v) in vals.into_iter().enumerate() {
                if arm.args[b] == Mode::Owned {
                    return Err(format!(
                        "memory: {}: the scrutinee is borrowed, and arm {i} owns binder {b}",
                        self.node_at(at, k)
                    ));
                }
                args.push((bound(b, v, cells[b], false), false));
            }
        }
        args.extend((1..ins.len()).map(|j| (ins[j].clone(), np.modes[j] == Mode::Owned)));
        Ok(Out::Call {
            r: &node.regions[i],
            at: sub,
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

    /// Fused release of the scrutinee `cell`, keeping the cells at the kept binders of `tree`.
    /// O(cells freed + nodes of the paths): each node on the way to a kept binder is read once,
    /// where a list of paths read each path from the top, O(d²) for a binder at each of `d`
    /// levels (HEAP-binder-memory).
    ///
    /// The scrutinee nests as deep as the program, so the parts still to drop or release wait
    /// on a stack, in order (step T2-mid).
    fn release(&mut self, cell: Option<usize>, tree: &Kept<'_>) -> Result<(), String> {
        let mut stack = vec![Part::Keep(cell, vec![Paths::ROOT])];
        while let Some(part) = stack.pop() {
            let (cell, at) = match part {
                Part::Drop(cell) => {
                    self.dec(cell)?;
                    continue;
                }
                Part::Keep(cell, at) => (cell, at),
            };
            let Some(c) = cell else { continue };
            if at.iter().any(|&x| tree.kept(x)) {
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
                // Each child node goes to the part it reads, in one step.
                let mut sub = vec![Vec::new(); kids.len()];
                for kid in at.iter().flat_map(|&x| tree.kids(x)) {
                    let i = tree.part(kid);
                    let Some(s) = sub.get_mut(i) else {
                        return Err(format!(
                            "memory: a kept path reads part {i} of a cell of {} parts",
                            kids.len()
                        ));
                    };
                    s.push(kid);
                }
                for (k, sub) in kids.into_iter().zip(sub).rev() {
                    stack.push(if sub.is_empty() {
                        Part::Drop(k)
                    } else {
                        Part::Keep(k, sub)
                    });
                }
            } else {
                for &x in &at {
                    self.inc_kept(c, tree, x);
                }
                self.dec(cell)?;
            }
        }
        Ok(())
    }

    /// Gives each kept binder below node `x` of `tree`, which is at cell `c`, a reference.
    /// A part with no cell stops the walk below it: nothing below it is counted. Paths nest as
    /// deep as patterns, so the nodes in progress are on a stack.
    fn inc_kept(&mut self, c: usize, tree: &Kept<'_>, x: usize) {
        let mut todo: Vec<(usize, usize)> = tree.kids(x).map(|k| (c, k)).collect();
        while let Some((holder, k)) = todo.pop() {
            let part = self.heap[holder].kids.get(tree.part(k)).copied().flatten();
            if tree.kept(k) {
                self.inc(part);
            } else if let Some(p) = part {
                todo.extend(tree.kids(k).map(|k| (p, k)));
            }
        }
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

    /// The kernel runs node `node`, occurrence `id`, on `ins`, the owned inputs are dropped, and
    /// the value is allocated. The value may be a function or hold one, a family of functions
    /// a `map` made included (row FAIL-machine-held-family): the kernel gives it apart from its
    /// run ([`Made`]), and [`Machine::alloc_made`] allocates it, as native code's `slow` does.
    fn slow(
        &mut self,
        node: &'g Node,
        id: usize,
        np: &NodePlan,
        ins: &[Mv<'g>],
    ) -> Result<Mv<'g>, String> {
        let q = self.kernel_term(node, id, ins)?;
        let m = self.ev.run_made(&q).map_err(|e| e.to_string())?;
        self.consume(np, ins)?;
        Ok(self.alloc_made(m))
    }

    /// Allocates the value `m`: each node in order, a part before what holds it, data as
    /// [`Machine::fresh`] makes it, a closure as an [`Mv::Fun`] and a held value as an
    /// [`Mv::Held`], whose parts move into its cell; a node held at more places than one gets
    /// a reference for each place past the first. As native code's `alloc_made`.
    // Complexity tradeoff: the naive way hands the kernel's value to `fresh`, which takes data
    // only. Here each node is allocated once, O(nodes + parts), plus data as `fresh` costs.
    // Tradeoff: a closure the kernel gave back is an `Mv::Fun`, with no lambda node, so a call
    // of it runs in the kernel. Nothing is refused.
    fn alloc_made(&mut self, m: Made) -> Mv<'g> {
        let mut vals: Vec<Mv<'g>> = Vec::with_capacity(m.nodes.len());
        let mut used = vec![false; m.nodes.len()];
        for node in m.nodes {
            // Node `i`'s value for one more place: the first takes the reference it was made
            // with.
            let mut parts = |this: &mut Self, ids: &mut dyn Iterator<Item = usize>| {
                ids.map(|i| {
                    let v = vals[i].clone();
                    if std::mem::replace(&mut used[i], true) {
                        this.inc(v.cell());
                    }
                    v
                })
                .collect::<Vec<Mv<'g>>>()
            };
            let v = match node {
                MadeNode::Data(v) => self.fresh(v),
                MadeNode::Prim(p) => Mv::Prim(p),
                MadeNode::Source(p) => Mv::Source(p),
                MadeNode::Fun(f) => {
                    let (names, ids): (Vec<Arc<str>>, Vec<usize>) = f.caps.into_iter().unzip();
                    let caps = parts(self, &mut ids.into_iter());
                    let cell = self.alloc(caps.iter().map(Mv::cell).collect());
                    Mv::Fun(Rc::new(Fun {
                        cell,
                        params: f.params,
                        body: f.body,
                        names,
                        caps,
                        placed: f.placed,
                    }))
                }
                MadeNode::Held(shape, ids) => {
                    let ps = parts(self, &mut ids.into_iter());
                    let shape = match shape {
                        MadeShape::Tuple => HeldKind::Tuple,
                        MadeShape::Atom(n, f) => HeldKind::Atom((n, f)),
                        MadeShape::Family(f) => HeldKind::Family(Box::new(f)),
                    };
                    let kids = ps.iter().map(Mv::cell).collect();
                    self.held(shape, kids, ps)
                }
            };
            vals.push(v);
        }
        vals.pop().expect("a value has a node")
    }

    /// What primitive `p` gives on `ins`, which hold a held family where [`family_at`] says, as
    /// the kernel's `Machine::held_family` gives it, owned; `None` where the kernel gives an
    /// error, which is then the kernel's to give. As native code's `family_read`.
    // Complexity tradeoff: the naive read hands the family to the kernel, O(n) per read to build
    // its term, and an entry that is a function cannot come back as the machine's own value.
    // Here each read is one lookup in the family's keys, O(log n), and `first` and `last`
    // descend one level per step, O(depth · log n). Tradeoff: the kernel's rules for these
    // reads are written a third time (kernel, native code, here); the three-way tests in
    // `l01_36_cranelift::held_values` check that they agree.
    fn family_read(&mut self, p: Prim, ins: &[Mv<'g>]) -> Option<Mv<'g>> {
        enum Got<'a, 'g> {
            Part(&'a Mv<'g>),
            Data(Value),
            Pair(Value, &'a Mv<'g>),
        }
        let at = family_at(p, ins).expect("a held family operand");
        // The key read, or the entry tuple stepped from.
        let other = (ins.len() == 2).then(|| &ins[1 - at]);
        let key = match (p, other) {
            (_, None) => None,
            (Prim::EntryAfter | Prim::EntryBefore, Some(e)) => match e {
                Mv::Held(h) => match (h.is_tuple(), &h.parts[..]) {
                    (true, [Mv::Data(k, _), _]) => Some(k.clone()),
                    _ => return None,
                },
                Mv::Data(Value::Tuple(e), _) if e.len() == 2 => Some(e[0].clone()),
                _ => return None,
            },
            (_, Some(k)) => {
                // A key that is a failure passes through.
                if k.held_atom() {
                    let k = k.clone();
                    self.inc(k.cell());
                    return Some(k);
                }
                match k {
                    Mv::Data(k @ Value::Atom(_), _) => return Some(self.fresh(k.clone())),
                    Mv::Data(k, _) => Some(k.clone()),
                    _ => return None,
                }
            }
        };
        let Mv::Held(h) = &ins[at] else {
            unreachable!("`family_at` found a held family")
        };
        let f = h.family().expect("a held family");
        let entry = |e: HeldEntry<'_>| match e {
            HeldEntry::Data(v) => Got::Data(v.clone()),
            HeldEntry::Part(i) => Got::Part(&h.parts[i]),
        };
        let pair = |k: &Value, e: HeldEntry<'_>| match e {
            HeldEntry::Data(v) => Got::Data(Value::tuple(vec![k.clone(), v.clone()])),
            HeldEntry::Part(i) => Got::Pair(k.clone(), &h.parts[i]),
        };
        let none = || Got::Data(Value::tuple(Vec::new()));
        let got = match p {
            Prim::Get | Prim::TupleGet | Prim::At | Prim::Has => {
                let k = key.expect("a key");
                match (p, f.get(&k)) {
                    (Prim::Has, e) => Got::Data(Value::Bool(e.is_some())),
                    (_, Some(e)) => entry(e),
                    (Prim::At, None) => Got::Data(Value::atom("outOfBounds")),
                    (_, None) => Got::Data(Value::atom("notFound")),
                }
            }
            Prim::Count => Got::Data(Value::Int(f.len() as i64)),
            Prim::FirstEntry | Prim::LastEntry => match f.end(p == Prim::LastEntry) {
                Some((k, e)) => pair(k, e),
                None => none(),
            },
            Prim::EntryAfter | Prim::EntryBefore => {
                match f.beside(&key.expect("a key"), p == Prim::EntryAfter) {
                    Some((k, e)) => pair(k, e),
                    None => none(),
                }
            }
            Prim::First | Prim::Last => {
                // A part that is a held family is a level beneath its key: descend into it.
                let last = p == Prim::Last;
                let mut cur: &Held<'g> = h;
                loop {
                    let f = cur.family().expect("only held families are entered");
                    match f.end(last) {
                        None => break Got::Data(Value::atom("none")),
                        Some((_, HeldEntry::Data(Value::Family(inner)))) => {
                            break Got::Data(leaf_at_end(inner, last));
                        }
                        Some((_, HeldEntry::Data(v))) => break Got::Data(v.clone()),
                        Some((_, HeldEntry::Part(i))) => match &cur.parts[i] {
                            Mv::Held(n) if n.family().is_some() => cur = n,
                            m => break Got::Part(m),
                        },
                    }
                }
            }
            _ => unreachable!("`family_at` names these primitives only"),
        };
        Some(match got {
            Got::Data(v) => self.fresh(v),
            Got::Part(m) => {
                let m = m.clone();
                self.inc(m.cell());
                m
            }
            Got::Pair(k, m) => {
                let k = self.fresh(k);
                let m = m.clone();
                self.inc(m.cell());
                let kids = vec![k.cell(), m.cell()];
                self.held(HeldKind::Tuple, kids, vec![k, m])
            }
        })
    }

    /// The node gives `m`, a part of its inputs or one of them: `m` gets a reference before
    /// the owned inputs are dropped, so dropping them frees nothing `m` holds.
    fn give(&mut self, np: &NodePlan, ins: &[Mv<'g>], m: Mv<'g>) -> Result<Vec<Mv<'g>>, String> {
        self.inc(m.cell());
        self.consume(np, ins)?;
        Ok(vec![m])
    }

    /// A new held tuple, atom or family of `parts`, which move into its cell, whose kids are
    /// `kids`.
    fn held(&mut self, shape: HeldKind, kids: Vec<Option<usize>>, parts: Vec<Mv<'g>>) -> Mv<'g> {
        let cell = self.alloc(kids);
        Mv::Held(Rc::new(Held { cell, shape, parts }))
    }

    /// The name and field names of the atom node `node`, occurrence `id`, makes on `ins`, and
    /// for each place of its payload the input it holds (from 0, after the name and the field
    /// names): the kernel makes the atom with marks, its payload's positions, in the payload's
    /// place, so its rules (field order, a repeated name refused) are the kernel's, as the
    /// kernel's own held atom is made. `None` when the kernel refuses the atom.
    fn held_shape(
        &mut self,
        node: &'g Node,
        id: usize,
        ins: &[Mv<'g>],
    ) -> Option<(AtomName, Vec<usize>)> {
        let n = ins.len() - 2;
        let mut marks: Vec<Mv<'g>> = ins[..2].to_vec();
        marks.extend((0..n).map(|i| Mv::Data(Value::Int(i as i64), None)));
        let Ok(Value::Atom(a)) = self.kernel(node, id, &marks) else {
            return None;
        };
        let order = a
            .args()
            .iter()
            .map(|m| match m {
                Value::Int(i) => usize::try_from(*i).ok().filter(|&i| i < n),
                _ => None,
            })
            .collect::<Option<Vec<usize>>>()?;
        (order.len() == n).then(|| ((a.name.clone(), a.fields.clone()), order))
    }

    /// The value the kernel gives node `node`, occurrence `id`, run alone on `ins`.
    fn kernel(&mut self, node: &'g Node, id: usize, ins: &[Mv<'g>]) -> Result<Value, String> {
        let t = self.kernel_term(node, id, ins)?;
        self.ev.run(&t).map_err(|e| e.to_string())
    }

    /// The kernel term of node `node`, occurrence `id`, run alone on `ins`.
    fn kernel_term(&mut self, node: &'g Node, id: usize, ins: &[Mv<'g>]) -> Result<Term, String> {
        let mut lets = Lets::default();
        let mut terms = Vec::new();
        for v in ins {
            terms.push(self.term(v, &mut lets)?);
        }
        let t = raise_with(self.alone(node, id), &terms)?;
        Ok(wrap(lets, t))
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

    /// The kernel term for `v`; a lookup port is read once, by a `let` in `lets`. A held value
    /// is the tuple or atom primitive on its parts' terms, so the kernel makes it again as its
    /// own held value; a [`Term::Lit`] holds data only.
    ///
    /// Closures capture closures, and held values hold them, as deep as the program, so the
    /// values entered wait on a stack with the terms of their parts so far. Each closure's and
    /// held value's term is built once, in `lets.built`.
    fn term(&mut self, v: &Mv<'g>, lets: &mut Lets) -> Result<Term, String> {
        let mut stack: Vec<(Mv<'g>, Vec<HeldPart>)> = Vec::new();
        let mut got = enter_term(v, lets, &mut stack);
        loop {
            let Some((m, terms)) = stack.last_mut() else {
                return Ok(got.expect("a term").into_term());
            };
            terms.extend(got.take());
            let parts = match m {
                Mv::Clo(c) => &c.caps,
                Mv::Fun(f) => &f.caps,
                Mv::Held(h) => &h.parts,
                _ => unreachable!("only closures and held values are entered"),
            };
            match parts.get(terms.len()) {
                Some(p) => {
                    let p = p.clone();
                    got = enter_term(&p, lets, &mut stack);
                }
                None => {
                    let (m, terms) = stack.pop().expect("an entered value");
                    let t = match &m {
                        Mv::Clo(c) => HeldPart::closure(raise_with(
                            self.alone(c.node, c.id),
                            &HeldPart::terms(terms),
                        )?)?,
                        Mv::Fun(f) => HeldPart::closure(placed_fun_term(
                            &f.params,
                            &f.body,
                            &f.names,
                            HeldPart::terms(terms),
                            f.placed.as_ref(),
                        ))?,
                        // Bound once, outside the node's term, as native code binds it: a
                        // use, however often the term runs it, reads the one value.
                        Mv::Held(h) => {
                            let key = h.cell as u64;
                            let made = match &h.shape {
                                HeldKind::Tuple => held_term(None, key, terms),
                                HeldKind::Atom((n, f)) => held_term(Some((n, f)), key, terms),
                                HeldKind::Family(f) => held_family_term(f, key, terms),
                            };
                            let (x, part) = HeldPart::held(key);
                            lets.held.push((x, made));
                            part
                        }
                        _ => unreachable!("only closures and held values are entered"),
                    };
                    lets.built.insert(m.cell().expect("a cell"), t.clone());
                    got = Some(t);
                }
            }
        }
    }

    fn read(&self, u: &Uses, s: &Src, at: &dyn Display) -> Result<Mv<'g>, String> {
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
    fn take(
        &mut self,
        u: &Uses,
        s: &Src,
        at: &dyn Display,
        why: &dyn Display,
    ) -> Result<(Mv<'g>, bool), String> {
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

    /// A fresh value: its cells allocated, a sequence the value holds in several places one
    /// cell counted once per holder, and every other part of a tuple or an atom its own.
    fn fresh(&mut self, v: Value) -> Mv<'g> {
        let c = self.tree(&v);
        Mv::Data(v, c)
    }

    /// The cells of `v`, each part's before its whole's, on a stack of the tuples and atoms
    /// entered with their shared sequence and the cells of their parts so far: values nest as
    /// deep as the program. A shared sequence met again is the cell made for it, so a value
    /// whose levels each hold the one below twice is a cell per level, not one per path
    /// (COMPLEXITY.md R9).
    // Complexity tradeoff: the naive form gives each occurrence of a part its own cell, 2^d
    // cells for d levels each holding the one below twice (R9). Here the cell of each shared
    // sequence is kept in `made` by the sequence's identity (`Value::shared_parts`) and counted
    // once per holder: O(distinct sequences + holders). Tradeoffs: one map entry per shared
    // sequence for the call; equal sequences built apart get cells of their own, as the native
    // heap's `fresh` does, so the counts of the two agree. Nothing is refused. Tests
    // `l01_36_cranelift::shared_values`.
    fn tree(&mut self, v: &Value) -> Option<usize> {
        type Entered<'v> = (&'v [Value], Option<SharedParts<'v>>, Vec<Option<usize>>);
        let mut stack: Vec<Entered<'_>> = Vec::new();
        // The cell of each shared sequence made so far, by the sequence's identity.
        let mut made: HashMap<SharedParts<'_>, usize> = HashMap::new();
        let mut next = v;
        loop {
            let shared = next.shared_parts();
            let mut got = match next {
                _ if let Some(&c) = shared.and_then(|k| made.get(&k)) => {
                    self.inc(Some(c));
                    Some(c)
                }
                Value::Bool(_) | Value::Int(_) | Value::Float(_) | Value::Float32(_) => None,
                Value::Tuple(xs) if xs.is_empty() => None,
                Value::Atom(a) if a.args().is_empty() => None,
                Value::Tuple(xs) => {
                    stack.push((xs, shared, Vec::with_capacity(xs.len())));
                    next = &xs[0];
                    continue;
                }
                Value::Atom(a) => {
                    stack.push((a.args(), shared, Vec::with_capacity(a.args().len())));
                    next = &a.args()[0];
                    continue;
                }
                Value::Str(_)
                | Value::Big(_)
                | Value::Rat(_)
                | Value::Path(_)
                | Value::Family(_) => Some(self.alloc(Vec::new())),
            };
            loop {
                let Some((xs, _, kids)) = stack.last_mut() else {
                    return got;
                };
                let xs: &[Value] = xs;
                kids.push(got);
                if let Some(x) = xs.get(kids.len()) {
                    next = x;
                    break;
                }
                let (_, shared, kids) = stack.pop().expect("a tuple or atom");
                let c = self.alloc(kids);
                if let Some(k) = shared {
                    made.insert(k, c);
                }
                got = Some(c);
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
    // Complexity tradeoff: the naive check runs the full audit after each step, O(heap) per
    // step and O(steps · heap) in all (COMPLEXITY.md Z14). Here the machine keeps the cells
    // each step touches and their reference counts (`refs`, `holds`) up to date as it goes, and
    // the check reads only those cells, O(cells touched) per step; the full audit runs only
    // when one of them is wrong, to name every fault. Precondition: every write to a count or a
    // reference records its cell in `touched`; a write that did not would go unchecked until a
    // later fault. Nothing is refused. Tests `l01_36_cranelift::scaling`.
    fn check(&mut self, when: &dyn Display) -> Result<(), String> {
        let touched = std::mem::take(&mut self.touched);
        let wrong = touched.iter().any(|&c| {
            self.heap[c].count != self.refs[c] || (self.heap[c].count == 0 && self.holds[c] > 0)
        });
        if wrong { self.audit(when) } else { Ok(()) }
    }

    /// Checks that each live cell's count is the number of references to it, from owned
    /// slots in every frame and from live cells, and that no slot holds a freed cell.
    fn audit(&self, when: &dyn Display) -> Result<(), String> {
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
                    counted(u64::from(refs[c]), "reference")
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

/// The input that primitive `p` gives back on `ins`, one of which is a held value, when `p`
/// passes an atom that holds a function through as a failure: every input is data or such an
/// atom, and it is the one failure among them, as the kernel decides (`Machine::held` in
/// zed-kernel's eval.rs). `None` where the kernel makes a value or stops: a tuple and an atom,
/// which the node makes, `==` and `!=`, a keypath, a wrong number of inputs, a held tuple, and
/// several failures, which `#errs` cannot hold.
fn passed<'a, 'g>(p: Prim, ins: &'a [Mv<'g>]) -> Option<&'a Mv<'g>> {
    if matches!(
        p,
        Prim::Tuple | Prim::Atom | Prim::Eq | Prim::Ne | Prim::Path
    ) || p.arity().is_some_and(|n| n != ins.len())
        || !ins
            .iter()
            .all(|m| matches!(m, Mv::Data(..)) || m.held_atom())
    {
        return None;
    }
    let failure = |m: &&Mv<'g>| matches!(m, Mv::Data(Value::Atom(_), _)) || m.held_atom();
    if ins.iter().filter(failure).count() != 1 {
        return None;
    }
    ins.iter().find(|m| m.held_atom())
}

/// What a call `ins[0](ins[1..])` of a held value gives, as the kernel calls one: a held tuple
/// at one key, its part (a key outside it is the kernel's value), and an atom that holds a
/// function, itself, as any atom called. A primitive called on a held value passes it as
/// [`passed`] does. `None` where the kernel decides.
fn called<'a, 'g>(ins: &'a [Mv<'g>]) -> Option<&'a Mv<'g>> {
    match (&ins[0], &ins[1..]) {
        (t, [k]) if t.held_tuple() => read_held(t, k),
        (m, _) if m.held_atom() => Some(m),
        (Mv::Prim(Prim::TupleGet | Prim::At), [t, k]) if t.held_tuple() => read_held(t, k),
        (Mv::Prim(p), args) if args.iter().any(|m| matches!(m, Mv::Held(_))) => passed(*p, args),
        _ => None,
    }
}

/// The entries of display `ins`, key then value, as a held family and its parts, each value
/// that holds a function a part; `None` when a key is no data or the kernel refuses the
/// entries, which is then the kernel's error to give. As native code's `held_entries`.
// Complexity tradeoff: the naive display hands every entry to the kernel, O(n log n) and the
// family given back apart (`Machine::alloc_made`). Here the keys and data entries are read out
// of their values and the family built by the kernel's own rules ([`HeldFamily::new`]), the
// same O(n log n) without a term, as native code builds it, so the two count alike.
fn held_entries<'g>(ins: &[Mv<'g>]) -> Option<(HeldFamily, Vec<Mv<'g>>)> {
    let mut entries = Vec::with_capacity(ins.len() / 2);
    let mut parts = Vec::new();
    for kv in ins.chunks(2) {
        let [Mv::Data(k, _), v] = kv else {
            return None;
        };
        match v {
            Mv::Data(v, _) => entries.push((k.clone(), Some(v.clone()))),
            Mv::State => return None,
            v => {
                parts.push(v.clone());
                entries.push((k.clone(), None));
            }
        }
    }
    let Ok(Some(f)) = HeldFamily::new(entries) else {
        return None;
    };
    Some((f, parts))
}

/// The position in `ins` of the held family primitive `p` reads, when it reads one.
fn family_at(p: Prim, ins: &[Mv<'_>]) -> Option<usize> {
    let (at, n) = match p {
        Prim::Get | Prim::TupleGet | Prim::At | Prim::EntryAfter | Prim::EntryBefore => (0, 2),
        Prim::Has => (1, 2),
        Prim::Count | Prim::FirstEntry | Prim::LastEntry | Prim::First | Prim::Last => (0, 1),
        _ => return None,
    };
    (ins.len() == n && ins[at].held_family()).then_some(at)
}

/// The primitive a call `ins[0](ins[1..])` reads a held family with, and where its operands
/// start in `ins`: `Get` for the family applied to one key, or the primitive called.
fn family_called(ins: &[Mv<'_>]) -> Option<(Prim, usize)> {
    if ins.len() == 2 && family_at(Prim::Get, ins).is_some() {
        return Some((Prim::Get, 0));
    }
    let Mv::Prim(p) = ins.first()? else {
        return None;
    };
    family_at(*p, &ins[1..]).map(|_| (*p, 1))
}

/// What held tuple `t` read at key `k` gives when it is not the kernel's to make: the part at
/// an integer key inside the tuple, or `k` itself when it is an atom that holds a function.
/// `None` for any other key: `#outOfBounds`, a data atom given back, or an error, which the
/// kernel gives.
fn read_held<'a, 'g>(t: &'a Mv<'g>, k: &'a Mv<'g>) -> Option<&'a Mv<'g>> {
    match (t, k) {
        (Mv::Held(h), Mv::Data(Value::Int(i), _)) => {
            usize::try_from(*i).ok().and_then(|i| h.parts.get(i))
        }
        (_, k) if k.held_atom() => Some(k),
        _ => None,
    }
}

/// The variable the lookup port `p` is bound to by `wrap`; native code names its ports so
/// too, as [`HeldPart::port`] does.
pub fn port_var(p: &str) -> Arc<str> {
    format!("\0port {p}").into()
}

/// The variable a held value with key `key` is bound to by `wrap`; native code names its
/// held values so too.
pub fn cell_var(key: u64) -> Arc<str> {
    format!("\0cell {key}").into()
}

/// `t` with each held value in `lets` made first, each before the ones that hold it, and each
/// lookup port read before them all.
fn wrap(lets: Lets, t: Term) -> Term {
    let t = (lets.held.into_iter().rev()).fold(t, |b, (x, made)| {
        Term::Let(x, Shared::new(made), Shared::new(b))
    });
    lets.order.into_iter().rev().fold(t, |b, p| {
        Term::Let(port_var(&p), Shared::new(Term::Read(p)), Shared::new(b))
    })
}

/// The lookup ports a kernel term reads, each once, in the order first met, and the term of
/// each closure it holds.
#[derive(Default)]
struct Lets {
    seen: HashSet<Arc<str>>,
    order: Vec<Arc<str>>,
    /// The term of each closure and held value met, by its cell (`Clo::cell`, `Held::cell`),
    /// which no other value of the run has: a closure captured on many paths is built once, so
    /// the term is a graph the size of the closures, not a tree of every path (COMPLEXITY.md
    /// R9). A closure's term is a `let` of its lambda, whose parts are shared, so a copy costs
    /// a few words; a held value's is its variable ([`cell_var`]), as cheap to copy.
    // Complexity tradeoff: the naive build walks a closure once per path to it, 2^d for d
    // levels each capturing the level below twice (R9: 4 times per 2 levels). Here each
    // closure's term is built once per kernel call and kept by `Clo::cell` (the machine never
    // reuses a cell), and every later use is a copy sharing the body: O(closures + captures).
    // Tradeoff: one map entry per closure for the call. Nothing is refused. Tests
    // `l01_36_cranelift::shared_closures` and
    // zed-native's `hooks::tests::a_closure_captured_twice_at_each_level_is_built_once`.
    built: HashMap<usize, HeldPart>,
    /// Each held value met, its variable ([`cell_var`]) and the term that makes it, in the
    /// order finished, so a value's parts come before it; [`wrap`] binds each once, outside
    /// the node's term, as native code's `Lets::held` does. Why the early build cannot fail or
    /// change the result: native code's `Lets::held`.
    // Complexity tradeoff: the naive term puts the making of a held value where the node uses
    // it, and the node's term may run that place once per entry: a family the kernel makes
    // with a held value at each of n keys made n values, n cells where native code made one,
    // and O(n · parts) time (test `l01_36_cranelift::held_values::a_held_tuple_at_each_key_of_
    // a_family_is_one_cell`). Here each is made once per kernel call, O(parts). Tradeoff: a
    // held value on a path the node does not take is made anyway, O(its parts), no more than
    // building its term cost.
    held: Vec<(Arc<str>, Term)>,
}

/// The term of `v` when it has one already or has no parts; otherwise enters `v` on `stack`.
fn enter_term<'g>(
    v: &Mv<'g>,
    lets: &mut Lets,
    stack: &mut Vec<(Mv<'g>, Vec<HeldPart>)>,
) -> Option<HeldPart> {
    match v {
        Mv::Clo(_) | Mv::Fun(_) | Mv::Held(_) => {
            let got = lets.built.get(&v.cell().expect("a cell")).cloned();
            if got.is_none() {
                stack.push((v.clone(), Vec::new()));
            }
            got
        }
        v => Some(flat_term(v, lets)),
    }
}

/// The term that makes a held tuple (`atom` `None`) or atom again from its parts' terms
/// `parts`: the tuple primitive, or the atom primitive on its name and its field names in the
/// order of its parts, in a `let` named by `key`, which no other held value of the term has.
/// The native runtime builds its held values' terms with it too.
pub fn held_term(atom: Option<(&Arc<str>, &Fields)>, key: u64, parts: Vec<HeldPart>) -> Term {
    let made = match atom {
        None => Term::Prim(Prim::Tuple, HeldPart::terms(parts)),
        Some((name, fields)) => {
            let names = fields.iter().map(|f| Value::str(f)).collect();
            let mut args = vec![Term::Lit(Value::str(name)), Term::Lit(Value::tuple(names))];
            args.extend(parts.into_iter().map(HeldPart::into_term));
            Term::Prim(Prim::Atom, args)
        }
    };
    held_let(key, made)
}

/// The term that makes the held family `f` again from its parts' terms `parts`: the display
/// primitive on its entries in key order, each data entry a literal and part `i` the term
/// `parts[i]`, in a `let` named by `key`, as [`held_term`]. The native runtime's.
pub fn held_family_term(f: &HeldFamily, key: u64, parts: Vec<HeldPart>) -> Term {
    let mut parts: Vec<Option<Term>> = parts.into_iter().map(|p| Some(p.into_term())).collect();
    let mut args = Vec::with_capacity(2 * f.len());
    for (k, e) in f.iter() {
        args.push(Term::Lit(k.clone()));
        args.push(match e {
            HeldEntry::Data(v) => Term::Lit(v.clone()),
            HeldEntry::Part(i) => parts[i].take().expect("each part once"),
        });
    }
    held_let(key, Term::Prim(Prim::Entries, args))
}

/// A `let` of the value `made`, so a copy of the term, one per holder, shares its parts.
fn held_let(key: u64, made: Term) -> Term {
    let x: Arc<str> = format!("\0held {key}").into();
    Term::Let(x.clone(), Shared::new(made), Shared::new(Term::Var(x)))
}

/// The term of a part of a held value, as the term that makes the value again ([`held_term`],
/// [`held_family_term`]) reads it. Those terms are made before the node that uses the value,
/// on paths it may not take, so evaluating a part must run no function, read no port and not
/// stop (the proof at native code's `Lets::held`). The field is private: a part is made only by
/// the five constructors below, one for each kind of term with that property, so a held value's
/// term takes no other input. The first four hold their property by their type; the fifth,
/// [`HeldPart::closure`], checks the term it is given and refuses any other (row
/// PROOF-early-build-input-kinds).
#[derive(Clone, Debug)]
pub struct HeldPart(Term);

impl HeldPart {
    /// 1. Data: a literal.
    pub fn data(v: Value) -> HeldPart {
        HeldPart(Term::Lit(v))
    }

    /// 2. A primitive used as a value.
    pub fn prim(p: Prim) -> HeldPart {
        HeldPart(Term::PrimFn(p))
    }

    /// 3. The variable of the lookup port `p`, which the term's outer `let`s read once, before
    ///    every held value is made.
    pub fn port(p: &str) -> HeldPart {
        HeldPart(Term::Var(port_var(p)))
    }

    /// 4. The variable ([`cell_var`]) of the held value with key `key`, made before the values
    ///    that hold it. The variable is given too, for the `let` that binds the value: the two
    ///    share one name.
    // Complexity tradeoff: each call of `cell_var` formats the name and copies it into an
    // `Arc`, two allocations; calling it once for the `let` and once for the part, as
    // 714b348c1 did, cost two more allocations per held value made (counted with a counting
    // `malloc` on executables of the l03_02 benchmarks: +2 for a program holding one value,
    // +4 for one holding two, at every size; PERF-held-part-collect-alloc). Making it once and
    // cloning the `Arc` costs one reference count. Nothing is refused.
    pub fn held(key: u64) -> (Arc<str>, HeldPart) {
        let x = cell_var(key);
        (x.clone(), HeldPart(Term::Var(x)))
    }

    /// 5. The term of a closure: a lambda, as `raise_node` of a lambda node and `fun_term` give
    ///    it, or `let x = <lambda> in x`, as `raise_with` of a one-node region gives it.
    ///    Evaluating either makes a closure and calls nothing. Any other term may run code when
    ///    it is evaluated, so it is refused: lowering a lambda to another form is a fault of
    ///    zedc, and the refusal stops the run before the held value is made.
    ///    A closure with a parameter list is `place(table, closure)` or
    ///    `place(table, closure, fill)` (`placed_fun_term`): a literal, a lambda, and the term
    ///    of a closure, a lambda or a variable bound to one, so it too calls nothing.
    pub fn closure(t: Term) -> Result<HeldPart, String> {
        let lambda = |t: &Term| match t {
            Term::Lam(..) => true,
            Term::Let(x, e, b) => {
                matches!(&**e, Term::Lam(..)) && matches!(&**b, Term::Var(y) if y == x)
            }
            _ => false,
        };
        let placed = |xs: &[Term]| match xs {
            [Term::Lit(_), f] => lambda(f),
            [Term::Lit(_), f, fill] => lambda(f) && (lambda(fill) || matches!(fill, Term::Var(_))),
            _ => false,
        };
        let ok = match &t {
            Term::Prim(Prim::Place, xs) => placed(xs),
            t => lambda(t),
        };
        if ok {
            Ok(HeldPart(t))
        } else {
            Err(format!(
                "zedc made the term of a closure as `{t}`, which is not a lambda. A value that \
                 holds the closure is made before the code that uses it, so making it from this \
                 term could run code the program does not run there. This is a fault of zedc, \
                 not of the program; the run stops here instead."
            ))
        }
    }

    /// The part's term.
    pub fn into_term(self) -> Term {
        self.0
    }

    /// The terms of `parts`, in order.
    // Complexity tradeoff: a copy into a new vector is O(parts) words; `HeldPart` is one
    // `Term`, so the standard library's collect of a map over a vector's own iterator reuses
    // the vector's memory and only moves each part out, O(parts) with no allocation (its
    // in-place collect, which it does for items of equal size and alignment but does not
    // promise; without it the cost is the copy, O(parts)). The zed-native test
    // `hooks::tests::the_terms_of_held_parts_are_made_in_the_parts_own_vector` fails if a
    // compiler stops reusing it (PERF-held-part-collect-alloc). Nothing is refused.
    pub fn terms(parts: Vec<HeldPart>) -> Vec<Term> {
        parts.into_iter().map(HeldPart::into_term).collect()
    }
}

/// The kernel term for `v`, which is not a closure or a held value; a lookup port is read
/// once, by a `let` in `lets`.
fn flat_term(v: &Mv<'_>, lets: &mut Lets) -> HeldPart {
    match v {
        Mv::Data(v, _) => HeldPart::data(v.clone()),
        Mv::Prim(p) => HeldPart::prim(*p),
        Mv::State => HeldPart::data(Value::tuple(Vec::new())),
        Mv::Source(p) => {
            if lets.seen.insert(p.clone()) {
                lets.order.push(p.clone());
            }
            HeldPart::port(p)
        }
        Mv::Clo(_) | Mv::Fun(_) | Mv::Held(_) => {
            unreachable!("a closure's or held value's term is built on the stack of `term`")
        }
    }
}

/// The node in `paths` of each binder of `p` inside `v`, which `p` matches, in preorder,
/// appended to `out`; `paths` gets a node for each part entered, below its root, the whole of
/// `v`. O(size of `p`): a binder records one node, not a copy of the path above it
/// (HEAP-binder-memory).
///
/// Patterns nest as deep as the program, so the parts still to visit wait on a stack, each
/// with its node (step T2-mid).
fn binder_paths<'v>(
    p: &Pattern,
    v: &'v Value,
    root: usize,
    paths: &mut Paths,
    out: &mut Vec<(usize, &'v Value)>,
) {
    let mut stack: Vec<(usize, &Pattern, &Value)> = vec![(root, p, v)];
    // The node of part `i` of the value at node `up`.
    let mut enter = |up: usize, i: usize| paths.push(up, i);
    while let Some((at, p, v)) = stack.pop() {
        let start = stack.len();
        match (p, v) {
            (Pattern::Bind(_), v) => out.push((at, v)),
            (Pattern::Tuple(ps), Value::Tuple(xs)) => {
                let parts = ps.iter().zip(xs.iter()).enumerate();
                stack.extend(parts.map(|(i, (q, x))| (enter(at, i), q, x)));
            }
            (Pattern::Atom(_, ps), Value::Atom(a)) => {
                let parts = ps.iter().zip(a.args().iter()).enumerate();
                stack.extend(parts.map(|(i, (q, x))| (enter(at, i), q, x)));
            }
            (Pattern::Fields(_, fs), Value::Atom(a)) => {
                stack.extend(fs.iter().filter_map(|(f, q)| {
                    let i = a.fields.binary_search(f).ok()?;
                    Some((enter(at, i), q, &a.args()[i]))
                }));
            }
            _ => {}
        }
        // The first part on top, for preorder.
        stack[start..].reverse();
    }
}

/// The node in `paths` of each binder of `p` inside held value `m`, which `p` matches, in
/// preorder, appended to `nodes`, and the binder's part, appended to `parts`: a data part as
/// [`binder_paths`] reads it, with no cell (the caller finds the cell from the node). O(size of
/// `p`), on a stack of the parts still to visit.
fn held_binders<'g>(
    p: &Pattern,
    m: &Mv<'g>,
    paths: &mut Paths,
    nodes: &mut Vec<usize>,
    parts: &mut Vec<Mv<'g>>,
) {
    let mut stack: Vec<(usize, &Pattern, &Mv<'g>)> = vec![(Paths::ROOT, p, m)];
    let mut found = Vec::new();
    while let Some((at, p, m)) = stack.pop() {
        let start = stack.len();
        match (p, m) {
            (Pattern::Bind(_), m) => {
                nodes.push(at);
                parts.push(match m {
                    Mv::Data(v, _) => Mv::Data(v.clone(), None),
                    m => m.clone(),
                });
            }
            (p, Mv::Data(v, _)) => {
                found.clear();
                binder_paths(p, v, at, paths, &mut found);
                for &(n, v) in &found {
                    nodes.push(n);
                    parts.push(Mv::Data(v.clone(), None));
                }
            }
            // A held family matches no tuple or atom pattern, so is never entered.
            (Pattern::Tuple(ps) | Pattern::Atom(_, ps), Mv::Held(h)) if h.family().is_none() => {
                for (i, (q, x)) in ps.iter().zip(&h.parts).enumerate() {
                    stack.push((paths.push(at, i), q, x));
                }
            }
            (Pattern::Fields(_, fs), Mv::Held(h)) => {
                let names: &[Arc<str>] = match &h.shape {
                    HeldKind::Atom((_, f)) => f,
                    _ => &[],
                };
                for (f, q) in fs {
                    if let Ok(i) = names.binary_search(f) {
                        stack.push((paths.push(at, i), q, &h.parts[i]));
                    }
                }
            }
            _ => {}
        }
        // The first part on top, for preorder.
        stack[start..].reverse();
    }
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
