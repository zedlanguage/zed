//! Kernel → ZIR lowering (step L1.33), and the inverse map back to a kernel term.
//!
//! [`lower`] turns a closed kernel term into a graph whose root region yields the term's
//! value. Where DESIGN.md does not say, step L1.33 decides:
//!
//! - **One node per operation, constants on edges.** A literal is a constant input, a `let`
//!   binds a name to an edge and makes no node, and its name becomes a hint facet `name` on
//!   that edge. A prelude word applied to its arguments is a `prim` node; passed as a value it
//!   is a `prim` node with no inputs, not a lambda that calls it, since the kernel tells the two
//!   apart: a fold of `+` itself sums exactly, and of `(a, b) -> a + b` rounds at each step. A call of a literal lambda,
//!   `((x) -> e)(a)`, binds `x` to `a`'s edge and lowers `e` in place.
//! - **Captures on demand.** A name bound outside the region being built enters it as a
//!   capture, through every region between, in the order the body first reads it, and once
//!   however often it is read. The regions of one node share one capture list, the union of
//!   theirs in order, so each region is renumbered to it after it is built.
//! - **State edges on demand.** The first read of or push to a port takes its state edge,
//!   which enters a region as a capture and leaves it as a result, after the values. Only
//!   `match` and `port` regions carry state (step L1.31), so a `match` or `if` whose arms touch
//!   different ports passes each port's state through the arm that does not touch it, and the
//!   root region is a `port` region when the term uses a port and a `function` region when not.
//! - **A function that uses a port threads its state.** A `let`-bound lambda whose body reads
//!   or pushes a port, or calls such a function, is inlined at its call when its name occurs
//!   once in the term. Otherwise it is one `lambda` node whose region takes a state argument
//!   for each of those ports after its parameters and returns their states after its value,
//!   and each call is an `apply` that passes the current states in and takes the new ones
//!   out. So each body is lowered once, and a chain of such functions, each calling the one
//!   before twice, is linear in size, not exponential as inlining every call would make it
//!   (DESIGN.md Part G). Used as a value, such a function is an error, since a call through
//!   an unknown function could not thread the states.
//! - **CSE by content address.** A node is entered in its region under the key of its
//!   canonical form ([`super::canon::node_key`], hashed from the keys of its regions, so
//!   equal keys mean equal normal forms of the one-node regions holding the nodes), and a
//!   second node with that key is not added: its uses read the first. Nodes that differ
//!   only in hints, binder names or facet order are one node. A read, a push, or a node an
//!   effect passes through is never merged, since its state input is used once.
//! - **Edges carry `_` and no facts but hints.** The checker's types and the store's domains
//!   reach the graph in a later step; the lowering keeps the term's structure exactly.
//!
//! [`raise`] maps a graph back to a kernel term: each node a `let`, each
//! region a lambda body or a match arm. Evaluating the raised term gives the original term's
//! value, which is how the tests check the lowering against the interpreter.

use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap, HashSet, btree_map};
use std::fmt::Write;
use std::mem;
use std::sync::Arc;

use zed_kernel::num::{TooLarge, bytes_of};
use zed_kernel::term::{FixKind, Pattern, Prim, Shared, Term};
use zed_kernel::types::Type;

use super::legalize::{Swapped, written};
use super::validate::validate;
use super::{Edge, Node, Op, Region, RegionKind, Src, canon, kind_name, op_name};
use crate::address::ContentAddress;
use crate::canon::Facet;

/// The binding of each name in scope while lowering, kept persistently so that a closure keeps
/// the scope it was defined in at no cost.
type Scope<'t> = imbl::HashMap<Arc<str>, Val<'t>>;

/// What a name is bound to while lowering.
#[derive(Clone)]
enum Val<'t> {
    /// An edge of the region at the given depth of the frame stack.
    Src(Src, usize),
    /// A prelude word, not yet a node.
    Prim(Prim),
    /// A function that uses a port, called only by name.
    Closure(Arc<Closure<'t>>),
}

/// A `let`-bound lambda whose body uses `ports`, in the order of their first use.
struct Closure<'t> {
    params: &'t [Arc<str>],
    ports: Vec<Arc<str>>,
    call: Call<'t>,
}

/// How a call of a [`Closure`] lowers.
enum Call<'t> {
    /// Its body in place, under the bindings it was defined under: the name occurs once.
    Inline { body: At<'t>, env: Scope<'t> },
    /// An `apply` of its `lambda` node's output, in the region at depth `at`.
    Node { fun: Src, at: usize },
}

/// A region being built.
struct Frame {
    region: Region,
    /// The arguments before the captures.
    fixed: usize,
    /// Where each capture comes from in the enclosing region, in argument order.
    captures: Vec<Src>,
    /// The argument that holds each edge already captured: the depth of the region it comes
    /// from and its key there.
    brought: HashMap<(usize, (usize, usize)), Src>,
    /// The current state edge of each port the region has touched.
    states: HashMap<Arc<str>, Src>,
    /// The nodes entered with each key, by their shapes.
    seen: HashMap<ContentAddress, BTreeMap<canon::Shape, usize>>,
    /// The keys of each node's regions, in node order.
    keys: Vec<Vec<ContentAddress>>,
    /// The numbers of each node's regions in [`canon::Regions`], in node order.
    numbers: Vec<Vec<usize>>,
}

impl Frame {
    fn new(kind: RegionKind, args: Vec<Edge>) -> Frame {
        Frame {
            fixed: args.len(),
            region: Region {
                kind,
                args,
                nodes: Vec::new(),
                results: Vec::new(),
            },
            captures: Vec::new(),
            brought: HashMap::new(),
            states: HashMap::new(),
            seen: HashMap::new(),
            keys: Vec::new(),
            numbers: Vec::new(),
        }
    }
}

/// A finished region with what its node needs to know about it.
struct Built {
    region: Region,
    fixed: usize,
    captures: Vec<Src>,
    states: HashMap<Arc<str>, Src>,
    values: usize,
    keys: Vec<Vec<ContentAddress>>,
    numbers: Vec<Vec<usize>>,
}

struct Lower<'t> {
    frames: Vec<Frame>,
    scope: Scope<'t>,
    fresh: usize,
    /// How often each name occurs in the term, binders of the same name counted together.
    uses: HashMap<Arc<str>, usize>,
    /// The [`Uses`] of each lambda body met so far, by occurrence id.
    bodies: Bodies,
    places: Places,
    /// The first refusal of the memory to write a constant for a key ([`canon::Shape::of`],
    /// [`canon::Regions::enter`]); after it no node is looked up, and [`lower`] reports it.
    refused: Option<TooLarge>,
    /// The regions finished so far, each distinct one numbered once.
    regions: canon::Regions,
}

/// What a lambda body uses from outside it: a port it reads or pushes, or a name free in it.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Use {
    Port(Arc<str>),
    Free(Arc<str>),
}

/// The distinct [`Use`]s of a lambda body, in the order of their first occurrence.
type Uses = Arc<[Use]>;

/// The [`Uses`] of each lambda body, by its occurrence id in [`Places`].
type Bodies = HashMap<usize, Uses>;

/// A subterm of the term being lowered with its occurrence id in [`Places`].
#[derive(Clone, Copy)]
struct At<'t> {
    t: &'t Term,
    id: usize,
}

/// Occurrence ids of the subterms of the term being lowered, given by one walk from the root,
/// so they depend only on where a subterm stands in the term, never on where it is in memory
/// (step ADDR-keys). The root is 0, and the parts of occurrence `i`, in the order of [`parts`],
/// are `first[i]`, `first[i] + 1`, and so on.
// Complexity tradeoff: a subterm shared at several places of the term (an `Arc` held twice)
// gets an id at each, so the numbering costs the term's size as a tree, not its number of
// distinct subterms: a term of `d` levels whose two parts share one subterm costs `2^d`. Every
// term gets the right ids; only such a term pays more. Lowering itself walks the term as a
// tree, so it already pays that size (it did before ADDR-keys), and the numbering keeps the
// order of the whole. Tests: `l01_33_lowering::scaling` (`lowering_a_wide_match_scales` and the
// rest, unchanged) and `l01_33_lowering::ports::ports_are_kept_by_place_not_address`;
// COMPLEXITY.md K40. A complete solution needs hash-consed term ids, so that a shared subterm
// is numbered once and the lowering walks it once.
struct Places {
    first: Vec<usize>,
}

impl Places {
    /// The ids of the subterms of `t`, calling `f` on `t` and every subterm. A term nests as
    /// deep as its program, so the subterms still to number are kept on a heap stack.
    fn new(t: &Term, f: &mut dyn FnMut(&Term)) -> Places {
        let mut first = vec![0];
        let mut todo = vec![(t, 0)];
        let mut ps = Vec::new();
        while let Some((t, i)) = todo.pop() {
            f(t);
            parts(t, &mut ps);
            let next = first.len();
            first[i] = next;
            first.resize(next + ps.len(), 0);
            todo.extend(ps.drain(..).enumerate().map(|(j, p)| (p, next + j)));
        }
        Places { first }
    }

    /// The id of the first part of `at`.
    fn first(&self, at: At<'_>) -> usize {
        self.first[at.id]
    }

    /// `t`, part `j` of `at` in the order of [`parts`], with its id.
    fn part<'t>(&self, at: At<'t>, j: usize, t: &'t Term) -> At<'t> {
        At {
            t,
            id: self.first(at) + j,
        }
    }
}

/// The graph of the closed term `t`, validated. A prelude word is read only where the term
/// binds it, as [`crate::interp::prelude`] does.
pub fn lower(t: &Term) -> Result<Region, String> {
    let mut uses: HashMap<Arc<str>, usize> = HashMap::new();
    let places = Places::new(t, &mut |s| {
        if let Term::Var(x) = s {
            *uses.entry(x.clone()).or_default() += 1;
        }
    });
    let mut l = Lower {
        frames: vec![Frame::new(RegionKind::Function, Vec::new())],
        scope: Scope::new(),
        fresh: 0,
        uses,
        bodies: HashMap::new(),
        places,
        refused: None,
        regions: canon::Regions::default(),
    };
    let out = l.term(At { t, id: 0 }).and_then(|v| l.src(v));
    // A refused constant is the error, whatever lowering found after it.
    if let Some(e) = l.refused {
        return Err(format!(
            "a constant is so large that the system refused the {} bytes of memory asked to \
             build and write it for its content address",
            bytes_of(&e.bits)
        ));
    }
    let out = out?;
    let f = l.frames.pop().expect("the root frame");
    let mut root = f.region;
    root.results.push(out);
    for a in &root.args {
        if let Edge::State(p) = a {
            let s = f.states.get(p).expect("a port's state");
            root.results.push(s.clone());
        }
    }
    if root.args.iter().any(Edge::is_state) {
        root.kind = RegionKind::Port;
    }
    validate(&root).map_err(|e| format!("the lowered graph is invalid: {e}"))?;
    Ok(root)
}

impl<'t> Lower<'t> {
    fn top(&self) -> usize {
        self.frames.len() - 1
    }

    fn frame(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("a frame")
    }

    fn fresh(&mut self) -> Arc<str> {
        self.fresh += 1;
        format!("\0lower{}", self.fresh).into()
    }

    fn bind(&mut self, x: Arc<str>, v: Val<'t>) {
        self.scope.insert(x, v);
    }

    /// Restores the scope `mark`, taken before the bindings since.
    fn unbind(&mut self, mark: Scope<'t>) {
        self.scope = mark;
    }

    /// Replaces the scope by `env`, returning the old one.
    fn swap_scope(&mut self, env: Scope<'t>) -> Scope<'t> {
        std::mem::replace(&mut self.scope, env)
    }

    fn lookup(&self, x: &str) -> Result<Val<'t>, String> {
        match self.scope.get(x) {
            Some(v) => Ok(v.clone()),
            None => Err(format!(
                "`{x}` is not bound, and a term lowers only when every name it reads is bound \
                 in it or is a prelude word"
            )),
        }
    }

    /// `v` as an edge of the current region.
    fn src(&mut self, v: Val<'t>) -> Result<Src, String> {
        match v {
            Val::Src(s, at) => Ok(self.bring(s, at)),
            Val::Prim(p) => self.prim_fn(p),
            Val::Closure(c) => Err(format!(
                "a function of {} that uses the ports {} is used as a value: a call threads \
                 the states of those ports, and only a call by the function's name knows them, \
                 so such a function is only called",
                plural(c.params.len(), "parameter"),
                c.ports
                    .iter()
                    .map(|p| format!("`{p}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
        }
    }

    /// The edge `s` of the region at depth `at`, captured into each region down to the top.
    fn bring(&mut self, s: Src, at: usize) -> Src {
        if matches!(s, Src::Const(_)) {
            return s;
        }
        // Each region holds an edge once, however often it is read, so a region's arguments
        // do not grow with the reads below it. The walk stops at the nearest region that has
        // the edge, and every region it passes takes the edge, so a read costs O(1) amortized.
        let key = (at, captured(&s));
        let top = self.frames.len() - 1;
        let mut from = top;
        while from > at && !self.frames[from].brought.contains_key(&key) {
            from -= 1;
        }
        let mut s = match self.frames[from].brought.get(&key) {
            Some(held) if from > at => held.clone(),
            _ => s,
        };
        for k in from + 1..=top {
            s = self.capture(k, s);
            self.frames[k].brought.insert(key, s.clone());
        }
        s
    }

    /// The argument of frame `k` that receives `s`, an edge of frame `k - 1`.
    fn capture(&mut self, k: usize, s: Src) -> Src {
        let edge = self.frames[k - 1].region.edge(&s);
        let f = &mut self.frames[k];
        f.captures.push(s);
        f.region.args.push(edge);
        Src::Arg(f.region.args.len() - 1)
    }

    /// The current state edge of port `p` in frame `k`, taken from the enclosing regions.
    fn state(&mut self, k: usize, p: &Arc<str>) -> Result<Src, String> {
        // The frames nest as deep as the program, so the nearest frame holding `p` is found by
        // a loop, and every frame from there up to `k` takes the edge, as the recursion did.
        let mut from = k;
        while from > 0 && !self.frames[from].states.contains_key(p) {
            let kind = self.frames[from].region.kind;
            if !matches!(kind, RegionKind::Match | RegionKind::Port) {
                return Err(format!(
                    "port `{p}` is used inside a {} region, and a state edge enters only a \
                     match or port region or the region of a `let`-bound lambda (step L1.31): \
                     a port is read or pushed outside loops and families, and a function that \
                     uses one is bound by `let` and called by its name",
                    kind_name(kind)
                ));
            }
            from -= 1;
        }
        let mut s = match self.frames[from].states.get(p) {
            Some(s) => s.clone(),
            None => {
                let root = &mut self.frames[0].region;
                root.args.push(Edge::State(p.clone()));
                let s = Src::Arg(root.args.len() - 1);
                self.frames[0].states.insert(p.clone(), s.clone());
                s
            }
        };
        for j in from + 1..=k {
            let f = &mut self.frames[j];
            f.captures.push(s);
            f.region.args.push(Edge::State(p.clone()));
            s = Src::Arg(f.region.args.len() - 1);
            f.states.insert(p.clone(), s.clone());
        }
        Ok(s)
    }

    fn set_state(&mut self, p: &Arc<str>, s: Src) {
        self.frame().states.insert(p.clone(), s);
    }

    /// Adds `node` to the current region, or finds the node with its content address. A node
    /// that takes a state edge never repeats one, since each state edge is used once, so the
    /// effects stay apart without a test of their own.
    /// Adds `node`, whose regions have the keys `keys` and the numbers `numbers` in
    /// [`canon::Regions`], unless a node of equal normal form
    /// is there. The nodes of one key are kept by their [`canon::Shape`], so a key never decides
    /// equality alone and two distinct nodes whose keys collide stay two (step L1.37a). An add
    /// costs one hash lookup and `O(log k)` shape comparisons for `k` nodes of its key, each at
    /// most the bytes of the smaller node's operation, inputs and outputs: `k` is one but for a collision of 256-bit keys, and
    /// about n/256 for n nodes in the `short-addresses` build (8-bit keys).
    fn add(&mut self, node: Node, keys: Vec<ContentAddress>, numbers: Vec<usize>) -> usize {
        let shape = match (&self.refused, canon::Shape::of(&node, numbers.clone())) {
            (None, Ok(shape)) => shape,
            (refused, shape) => {
                // A constant was refused: the graph is not returned, so the node is kept
                // without the lookup, which would write the refused constant again.
                if let (None, Err(e)) = (refused, shape) {
                    self.refused = Some(e);
                }
                let f = self.frame();
                f.region.nodes.push(node);
                f.keys.push(keys);
                f.numbers.push(numbers);
                return f.region.nodes.len() - 1;
            }
        };
        let key = shape.key(&keys);
        let f = self.frame();
        match f.seen.entry(key).or_default().entry(shape) {
            btree_map::Entry::Occupied(e) => *e.get(),
            btree_map::Entry::Vacant(e) => {
                f.region.nodes.push(node);
                f.keys.push(keys);
                f.numbers.push(numbers);
                *e.insert(f.region.nodes.len() - 1)
            }
        }
    }

    /// A one-output node with no region.
    fn leaf(&mut self, op: Op, inputs: Vec<Src>) -> Val<'t> {
        let n = self.add(
            Node {
                op,
                inputs,
                outputs: vec![top()],
                regions: Vec::new(),
            },
            Vec::new(),
            Vec::new(),
        );
        Val::Src(Src::Out(n, 0), self.top())
    }

    /// The node `op` with inputs `fixed` and regions `built`, their captures merged.
    fn node(&mut self, op: Op, fixed: Vec<Src>, built: Vec<Built>) -> Val<'t> {
        // The union of the regions' captures, in order, with the position of each.
        let mut caps: Vec<Src> = Vec::new();
        let mut at: HashMap<(usize, usize), usize> = HashMap::new();
        for b in &built {
            for c in &b.captures {
                at.entry(captured(c)).or_insert_with(|| {
                    caps.push(c.clone());
                    caps.len() - 1
                });
            }
        }
        let edges: Vec<Edge> = {
            let parent = &self.frame().region;
            caps.iter().map(|c| parent.edge(c)).collect()
        };
        let ports: Vec<(usize, Arc<str>)> = edges
            .iter()
            .enumerate()
            .filter_map(|(i, e)| match e {
                Edge::State(p) => Some((i, p.clone())),
                Edge::Value(_) => None,
            })
            .collect();
        let values = built.first().map_or(1, |b| b.values);
        let mut regions = Vec::new();
        let mut keys = Vec::new();
        let mut numbers = Vec::new();
        for b in built {
            let map: Vec<usize> = (0..b.fixed)
                .chain(b.captures.iter().map(|c| b.fixed + at[&captured(c)]))
                .collect();
            let mut r = b.region;
            renumber(&mut r, &map);
            r.args.truncate(b.fixed);
            r.args.extend(edges.iter().cloned());
            for (i, p) in &ports {
                let fin = match b.states.get(p) {
                    // The node that last used the port, never an argument.
                    Some(s) => s.clone(),
                    None => Src::Arg(b.fixed + i),
                };
                r.results.push(fin);
            }
            match self.regions.enter(&r, &b.keys, b.numbers) {
                Ok((k, number)) => {
                    keys.push(k);
                    numbers.push(number);
                }
                Err(e) => {
                    // Any key and number will do: the graph is not returned after a refusal.
                    self.refused.get_or_insert(e);
                    keys.push(ContentAddress([0; 32]));
                    numbers.push(0);
                }
            }
            regions.push(Arc::new(r));
        }
        let mut outputs = vec![top(); values];
        outputs.extend(ports.iter().map(|(_, p)| Edge::State(p.clone())));
        let mut inputs = fixed;
        inputs.extend(caps);
        let n = self.add(
            Node {
                op,
                inputs,
                outputs,
                regions,
            },
            keys,
            numbers,
        );
        for (j, (_, p)) in ports.iter().enumerate() {
            self.set_state(p, Src::Out(n, values + j));
        }
        Val::Src(Src::Out(n, 0), self.top())
    }

    /// A prelude word as a function value: a `prim` node with no inputs.
    fn prim_fn(&mut self, p: Prim) -> Result<Src, String> {
        if p.arity().is_none() {
            return Err(format!(
                "the primitive `{}` takes any number of arguments, so with no inputs its node \
                 is a call, not the function; call it instead of passing it as a value",
                p.written()
            ));
        }
        let Val::Src(s, _) = self.leaf(Op::Prim(p), Vec::new()) else {
            unreachable!("a leaf is an edge")
        };
        Ok(s)
    }

    /// The ports `b`, a lambda body, reads or pushes, itself or by calling a function free in
    /// it that does, in the order of their first use in the text.
    fn ports(&mut self, b: At<'_>) -> Vec<Arc<str>> {
        let uses = body_uses(b, &mut self.bodies, &self.places);
        let mut out: Vec<Arc<str>> = Vec::new();
        let mut seen: HashSet<Arc<str>> = HashSet::new();
        for u in uses.iter() {
            match u {
                Use::Port(p) => {
                    if seen.insert(p.clone()) {
                        out.push(p.clone());
                    }
                }
                Use::Free(x) => {
                    if let Ok(Val::Closure(c)) = self.lookup(x) {
                        for p in &c.ports {
                            if seen.insert(p.clone()) {
                                out.push(p.clone());
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// The value of `t`, lowered into the current region. A term nests as deep as its program,
    /// so the walk keeps the work still to do on heap stacks (step T2-mid): it does what the
    /// recursive walk did, in the same order, so the graph is the same.
    fn term(&mut self, t: At<'t>) -> Result<Val<'t>, String> {
        let mut s = Stacks {
            jobs: vec![Job::Term(t)],
            vals: Vec::new(),
            srcs: Vec::new(),
            built: Vec::new(),
        };
        while let Some(job) = s.jobs.pop() {
            self.step(job, &mut s)?;
        }
        Ok(s.vals.pop().expect("the term's value"))
    }

    /// Schedules the lowering of `t`, or lowers it now when it holds no term.
    fn enter(&mut self, here: At<'t>, s: &mut Stacks<'t>) -> Result<(), String> {
        let at = self.top();
        let region = |kind, params: &'t [Arc<str>], body: At<'t>| Job::Region {
            kind,
            params: Params::Names(Cow::Borrowed(params)),
            ports: Vec::new(),
            body: Body::Term(body),
        };
        match here.t {
            Term::Lit(v) => s.vals.push(Val::Src(Src::Const(v.clone()), at)),
            Term::Var(x) => {
                let v = self.lookup(x)?;
                s.vals.push(v);
            }
            Term::PrimFn(p) => s.vals.push(Val::Prim(*p)),
            Term::Let(x, e, body) => {
                let e = self.places.part(here, 0, e);
                let body = self.places.part(here, 1, body);
                let b = match e.t {
                    Term::Lam(_, b) => Some(self.places.part(e, 0, b)),
                    _ => None,
                };
                let ports = match b {
                    Some(b) => self.ports(b),
                    None => Vec::new(),
                };
                s.jobs.push(Job::Let { x, body });
                match (e.t, b) {
                    (Term::Lam(ps, _), Some(b)) if !ports.is_empty() => {
                        if self.uses.get(x).is_none_or(|&n| n <= 1) {
                            let call = Call::Inline {
                                body: b,
                                env: self.scope.clone(),
                            };
                            s.vals.push(Val::Closure(Arc::new(Closure {
                                params: ps,
                                ports,
                                call,
                            })));
                        } else {
                            // Two owners: the region returns the ports' states, and the closure
                            // threads them through each call.
                            s.jobs.push(Job::Closure {
                                params: ps,
                                ports: ports.clone(),
                            });
                            s.jobs.push(Job::Region {
                                kind: RegionKind::Function,
                                params: Params::Names(Cow::Borrowed(ps)),
                                ports,
                                body: Body::Term(b),
                            });
                        }
                    }
                    _ => s.jobs.push(Job::Term(e)),
                }
            }
            Term::Lam(ps, body) => {
                s.jobs.push(Job::Node {
                    op: Op::Lambda,
                    fixed: 0,
                    regions: 1,
                });
                let body = self.places.part(here, 0, body);
                s.jobs.push(region(RegionKind::Function, ps, body));
            }
            Term::App(f, args) => {
                let f = self.places.part(here, 0, f);
                let first = self.places.first(here) + 1;
                self.apply(f, Args::Terms(args, first), s)
            }
            Term::Prim(p, args) => {
                if let Some(k) = p.arity()
                    && k != args.len()
                {
                    return Err(format!(
                        "the primitive `{}` takes {} and is given {}",
                        p.written(),
                        plural(k, "argument"),
                        args.len()
                    ));
                }
                s.jobs.push(Job::Leaf(Op::Prim(*p), args.len()));
                s.args(Args::Terms(args, self.places.first(here)), true);
            }
            Term::If(c, a, b) => {
                let p = |j, t| self.places.part(here, j, t);
                let (c, a, b) = (p(0, c), p(1, a), p(2, b));
                s.jobs.push(Job::Node {
                    op: Op::If,
                    fixed: 1,
                    regions: 2,
                });
                s.jobs.push(region(RegionKind::Match, &[], b));
                s.jobs.push(region(RegionKind::Match, &[], a));
                s.srcs(&[c]);
            }
            Term::Match(scrutinee, arms) => {
                let ps = arms.iter().map(|(p, _)| p.clone()).collect();
                s.jobs.push(Job::Node {
                    op: Op::Match(ps),
                    fixed: 1,
                    regions: arms.len(),
                });
                for (j, (p, body)) in arms.iter().enumerate().rev() {
                    s.jobs.push(Job::Region {
                        kind: RegionKind::Match,
                        params: Params::Names(Cow::Owned(names(p))),
                        ports: Vec::new(),
                        body: Body::Term(self.places.part(here, 1 + j, body)),
                    });
                }
                s.srcs(&[self.places.part(here, 0, scrutinee)]);
            }
            Term::Fam { domain, var, body } => {
                let (domain, body) = (
                    self.places.part(here, 0, domain),
                    self.places.part(here, 1, body),
                );
                s.jobs.push(Job::Node {
                    op: Op::Fam,
                    fixed: 1,
                    regions: 1,
                });
                s.jobs.push(region(
                    RegionKind::Function,
                    std::slice::from_ref(var),
                    body,
                ));
                s.srcs(&[domain]);
            }
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            } => {
                let p = |j, t| self.places.part(here, j, t);
                s.jobs.push(Job::Leaf(Op::Reindex(witness.clone()), 3));
                s.srcs(&[p(0, family), p(1, kf), p(2, vf)]);
            }
            Term::Discard { family, sel } => {
                let p = |j, t| self.places.part(here, j, t);
                s.jobs.push(Job::Leaf(Op::Discard, 2));
                s.srcs(&[p(0, family), p(1, sel)]);
            }
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            } => {
                let p = |j, t| self.places.part(here, j, t);
                let leaf = Op::Fold {
                    depth: *depth,
                    identity: identity.is_some(),
                    ev: ev.clone(),
                };
                match identity {
                    Some(id) => {
                        s.jobs.push(Job::Leaf(leaf, 3));
                        s.srcs(&[p(0, family), p(1, op), p(2, id)]);
                    }
                    None => {
                        s.jobs.push(Job::Leaf(leaf, 2));
                        s.srcs(&[p(0, family), p(1, op)]);
                    }
                }
            }
            Term::Fix {
                init,
                step,
                this,
                key,
                kind,
                ev,
            } => {
                let p = |j, t| self.places.part(here, j, t);
                let (init, step) = (p(0, init), p(1, step));
                match kind {
                    FixKind::Lattice { join } => {
                        let op = Op::Fix {
                            lattice: true,
                            ev: ev.clone(),
                        };
                        s.jobs.push(Job::Node {
                            op,
                            fixed: 2,
                            regions: 1,
                        });
                        s.jobs.push(Job::Region {
                            kind: RegionKind::Loop,
                            params: Params::Fresh,
                            ports: Vec::new(),
                            body: Body::Apply(step),
                        });
                        s.srcs(&[init, p(2, join)]);
                    }
                    FixKind::Definedness => {
                        let op = Op::Fix {
                            lattice: false,
                            ev: ev.clone(),
                        };
                        s.jobs.push(Job::Node {
                            op,
                            fixed: 1,
                            regions: 1,
                        });
                        s.jobs.push(Job::Region {
                            kind: RegionKind::Loop,
                            params: Params::Names(Cow::Owned(vec![this.clone(), key.clone()])),
                            ports: Vec::new(),
                            body: Body::Term(step),
                        });
                        s.srcs(&[init]);
                    }
                }
            }
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => {
                s.jobs.push(Job::Node {
                    op: Op::Gen(*pos),
                    fixed: 1,
                    regions: 2,
                });
                let p = |j, t| self.places.part(here, j, t);
                for f in [p(2, guard), p(1, step)] {
                    s.jobs.push(Job::Region {
                        kind: RegionKind::Loop,
                        params: Params::Fresh,
                        ports: Vec::new(),
                        body: Body::Apply(f),
                    });
                }
                s.srcs(&[p(0, init)]);
            }
            Term::Read(p) => {
                let st = self.state(at, p)?;
                let n = self.add(
                    Node {
                        op: Op::Read(p.clone()),
                        inputs: vec![st],
                        outputs: vec![top(), Edge::State(p.clone())],
                        regions: Vec::new(),
                    },
                    Vec::new(),
                    Vec::new(),
                );
                self.set_state(p, Src::Out(n, 1));
                s.vals.push(Val::Src(Src::Out(n, 0), at));
            }
            Term::Push(p, v) => {
                s.jobs.push(Job::Push(p));
                s.srcs(&[self.places.part(here, 0, v)]);
            }
        }
        Ok(())
    }

    /// Schedules the call of `f` with `args`. A literal lambda called with as many arguments as
    /// it has parameters binds them and lowers its body in place.
    fn apply(&self, f: At<'t>, args: Args<'t>, s: &mut Stacks<'t>) {
        if let Term::Lam(ps, body) = f.t
            && ps.len() == args.len()
        {
            let body = self.places.part(f, 0, body);
            s.jobs.push(Job::Bound { params: ps, body });
            s.args(args, false);
        } else {
            s.jobs.push(Job::Call(args));
            s.jobs.push(Job::Term(f));
        }
    }

    /// Calls the function value on top of `s.vals` with `args`.
    fn call(&mut self, args: Args<'t>, s: &mut Stacks<'t>) -> Result<(), String> {
        let n = args.len();
        match s.vals.pop().expect("the called value") {
            Val::Prim(p) if p.arity().is_none_or(|k| k == n) => {
                s.jobs.push(Job::Leaf(Op::Prim(p), n));
                s.args(args, true);
            }
            Val::Closure(c) => {
                if c.params.len() != n {
                    return Err(format!(
                        "a function of {} that uses a port is called with {}",
                        plural(c.params.len(), "parameter"),
                        plural(n, "argument")
                    ));
                }
                let fun = match &c.call {
                    Call::Inline { .. } => None,
                    Call::Node { fun, at } => Some(self.bring(fun.clone(), *at)),
                };
                match fun {
                    None => {
                        s.jobs.push(Job::Inline(c));
                        s.args(args, false);
                    }
                    Some(fun) => {
                        s.srcs.push(fun);
                        s.jobs.push(Job::Apply(c, n + 1));
                        s.args(args, true);
                    }
                }
            }
            fv => {
                let fun = self.src(fv)?;
                s.srcs.push(fun);
                s.jobs.push(Job::Leaf(Op::Apply, n + 1));
                s.args(args, true);
            }
        }
        Ok(())
    }

    /// Begins a region of `kind` whose arguments are `params` and then the states of `ports`,
    /// which it returns after its value, `body`.
    fn begin(
        &mut self,
        kind: RegionKind,
        params: Params<'t>,
        ports: Vec<Arc<str>>,
        body: Body<'t>,
        s: &mut Stacks<'t>,
    ) {
        let params = match params {
            Params::Names(ps) => ps,
            Params::Fresh => Cow::Owned(vec![self.fresh()]),
        };
        let mut args: Vec<Edge> = params.iter().map(|_| top()).collect();
        args.extend(ports.iter().map(|p| Edge::State(p.clone())));
        let mut frame = Frame::new(kind, args);
        for (j, p) in ports.iter().enumerate() {
            frame.states.insert(p.clone(), Src::Arg(params.len() + j));
        }
        self.frames.push(frame);
        let depth = self.top();
        let mark = self.scope.clone();
        for (i, p) in params.iter().enumerate() {
            self.bind(p.clone(), Val::Src(Src::Arg(i), depth));
        }
        s.jobs.push(Job::EndRegion { ports, mark });
        s.jobs.push(Job::Src);
        match body {
            Body::Term(t) => s.jobs.push(Job::Term(t)),
            Body::Apply(f) => {
                let x = params.first().expect("a loop's one parameter").clone();
                self.apply(f, Args::Name(x), s);
            }
        }
    }

    fn step(&mut self, job: Job<'t>, s: &mut Stacks<'t>) -> Result<(), String> {
        match job {
            Job::Term(t) => return self.enter(t, s),
            Job::Var(x) => {
                let v = self.lookup(&x)?;
                s.vals.push(v);
            }
            Job::Src => {
                let v = s.vals.pop().expect("a value");
                let e = self.src(v)?;
                s.srcs.push(e);
            }
            Job::Restore(mark) => self.unbind(mark),
            Job::Let { x, body } => {
                let v = s.vals.pop().expect("the bound value");
                if let Val::Src(Src::Out(n, p), d) = &v
                    && *d == self.top()
                {
                    let e = &mut self.frame().region.nodes[*n].outputs[*p];
                    if let Edge::Value(e) = e
                        && !e.facets.iter().any(|f| f.hint && &*f.kind == "name")
                    {
                        e.facets.push(Facet {
                            hint: true,
                            kind: "name".into(),
                            value: zed_kernel::Value::Str(x.clone().into()),
                        });
                    }
                }
                let mark = self.scope.clone();
                self.bind(x.clone(), v);
                s.jobs.push(Job::Restore(mark));
                s.jobs.push(Job::Term(body));
            }
            Job::Closure { params, ports } => {
                let built = s.built.pop().expect("the function's region");
                let Val::Src(fun, at) = self.node(Op::Lambda, Vec::new(), vec![built]) else {
                    unreachable!("a node's output")
                };
                s.vals.push(Val::Closure(Arc::new(Closure {
                    params,
                    ports,
                    call: Call::Node { fun, at },
                })));
            }
            Job::Bound { params, body } => {
                let vs = take(&mut s.vals, params.len());
                let mark = self.scope.clone();
                for (p, v) in params.iter().cloned().zip(vs) {
                    self.bind(p, v);
                }
                s.jobs.push(Job::Restore(mark));
                s.jobs.push(Job::Term(body));
            }
            Job::Call(args) => self.call(args, s)?,
            Job::Inline(c) => {
                let &Call::Inline { body, ref env } = &c.call else {
                    unreachable!("only an inlined function is called in place")
                };
                let vs = take(&mut s.vals, c.params.len());
                let saved = self.swap_scope(env.clone());
                for (p, v) in c.params.iter().cloned().zip(vs) {
                    self.bind(p, v);
                }
                s.jobs.push(Job::Restore(saved));
                s.jobs.push(Job::Term(body));
            }
            Job::Apply(c, n) => {
                let at = self.top();
                let mut ins = take(&mut s.srcs, n);
                let mut outputs = vec![top()];
                for p in &c.ports {
                    ins.push(self.state(at, p)?);
                    outputs.push(Edge::State(p.clone()));
                }
                let k = self.add(
                    Node {
                        op: Op::Apply,
                        inputs: ins,
                        outputs,
                        regions: Vec::new(),
                    },
                    Vec::new(),
                    Vec::new(),
                );
                for (j, p) in c.ports.iter().enumerate() {
                    self.set_state(p, Src::Out(k, 1 + j));
                }
                s.vals.push(Val::Src(Src::Out(k, 0), at));
            }
            Job::Leaf(op, n) => {
                let ins = take(&mut s.srcs, n);
                let v = self.leaf(op, ins);
                s.vals.push(v);
            }
            Job::Region {
                kind,
                params,
                ports,
                body,
            } => self.begin(kind, params, ports, body, s),
            Job::EndRegion { ports, mark } => {
                self.unbind(mark);
                let out = s.srcs.pop().expect("the region's value");
                let mut f = self.frames.pop().expect("the region's frame");
                f.region.results.push(out);
                for p in &ports {
                    let st = f.states.get(p).expect("a port taken");
                    f.region.results.push(st.clone());
                }
                s.built.push(Built {
                    region: f.region,
                    fixed: f.fixed,
                    captures: f.captures,
                    states: f.states,
                    values: 1,
                    keys: f.keys,
                    numbers: f.numbers,
                });
            }
            Job::Node { op, fixed, regions } => {
                let built = take(&mut s.built, regions);
                let fixed = take(&mut s.srcs, fixed);
                let v = self.node(op, fixed, built);
                s.vals.push(v);
            }
            Job::Push(p) => {
                let v = s.srcs.pop().expect("the pushed value");
                let at = self.top();
                let st = self.state(at, p)?;
                let n = self.add(
                    Node {
                        op: Op::Push(p.clone()),
                        inputs: vec![st, v],
                        outputs: vec![top(), Edge::State(p.clone())],
                        regions: Vec::new(),
                    },
                    Vec::new(),
                    Vec::new(),
                );
                self.set_state(p, Src::Out(n, 1));
                s.vals.push(Val::Src(Src::Out(n, 0), at));
            }
        }
        Ok(())
    }
}

/// Where the body of a region being built comes from.
enum Body<'t> {
    /// A term of the program.
    Term(At<'t>),
    /// `f` applied to the region's one parameter: the step or guard of a loop.
    Apply(At<'t>),
}

/// The parameters of a region being built.
enum Params<'t> {
    Names(Cow<'t, [Arc<str>]>),
    /// One fresh name, drawn when the region begins, as the recursive walk drew it.
    Fresh,
}

/// The arguments of a call.
enum Args<'t> {
    /// Terms of the program, the first of the given occurrence id and the others of the ids
    /// after it.
    Terms(&'t [Term], usize),
    /// One argument: the value bound to the name.
    Name(Arc<str>),
}

impl Args<'_> {
    fn len(&self) -> usize {
        match self {
            Args::Terms(ts, _) => ts.len(),
            Args::Name(_) => 1,
        }
    }
}

/// A step of [`Lower::term`]. A step that lowers a term pushes its value on [`Stacks::vals`],
/// [`Job::Src`] moves the top value to [`Stacks::srcs`] as an edge of the current region, and a
/// region, once built, waits on [`Stacks::built`] for its node.
enum Job<'t> {
    Term(At<'t>),
    /// The value bound to the name.
    Var(Arc<str>),
    Src,
    /// Restores the scope taken before the bindings since.
    Restore(Scope<'t>),
    /// Binds `x` to the top value and lowers `body` under it.
    Let {
        x: &'t Arc<str>,
        body: At<'t>,
    },
    /// The closure of a `let`-bound function from its built region: a `lambda` node.
    Closure {
        params: &'t [Arc<str>],
        ports: Vec<Arc<str>>,
    },
    /// Binds `params` to the top values and lowers `body`: a call of a literal lambda.
    Bound {
        params: &'t [Arc<str>],
        body: At<'t>,
    },
    /// Calls the top value with `args`.
    Call(Args<'t>),
    /// Lowers the closure's body in place, its parameters bound to the top values.
    Inline(Arc<Closure<'t>>),
    /// The `apply` of the closure's `lambda` node on the top edges, the function's first.
    Apply(Arc<Closure<'t>>, usize),
    /// A one-output node of no region on the top edges.
    Leaf(Op, usize),
    /// Begins a region.
    Region {
        kind: RegionKind,
        params: Params<'t>,
        ports: Vec<Arc<str>>,
        body: Body<'t>,
    },
    /// Ends the region begun last, its value the top edge.
    EndRegion {
        ports: Vec<Arc<str>>,
        mark: Scope<'t>,
    },
    /// The node `op` with the top `fixed` edges as inputs and the top `regions` regions.
    Node {
        op: Op,
        fixed: usize,
        regions: usize,
    },
    /// Pushes the top edge to the port.
    Push(&'t Arc<str>),
}

/// The stacks of [`Lower::term`].
struct Stacks<'t> {
    jobs: Vec<Job<'t>>,
    vals: Vec<Val<'t>>,
    srcs: Vec<Src>,
    built: Vec<Built>,
}

impl<'t> Stacks<'t> {
    /// Lowers `ts` in turn, each to an edge.
    fn srcs(&mut self, ts: &[At<'t>]) {
        for &t in ts.iter().rev() {
            self.jobs.push(Job::Src);
            self.jobs.push(Job::Term(t));
        }
    }

    /// Lowers `args` in turn, each to a value, or to an edge when `edges`.
    fn args(&mut self, args: Args<'t>, edges: bool) {
        match args {
            Args::Terms(ts, first) => {
                for (j, t) in ts.iter().enumerate().rev() {
                    if edges {
                        self.jobs.push(Job::Src);
                    }
                    self.jobs.push(Job::Term(At { t, id: first + j }));
                }
            }
            Args::Name(x) => {
                if edges {
                    self.jobs.push(Job::Src);
                }
                self.jobs.push(Job::Var(x));
            }
        }
    }
}

/// The top `n` items of `v`, in order.
fn take<T>(v: &mut Vec<T>, n: usize) -> Vec<T> {
    v.split_off(v.len() - n)
}
/// The key of a captured edge: a constant is never captured.
fn captured(s: &Src) -> (usize, usize) {
    match s {
        Src::Arg(i) => (usize::MAX, *i),
        Src::Out(n, p) => (*n, *p),
        Src::Const(_) => unreachable!("a constant is never captured"),
    }
}

/// An edge of type `_` with no facts.
fn top() -> Edge {
    Edge::value(Type::top())
}

fn plural(n: usize, thing: &str) -> String {
    if n == 1 {
        format!("1 {thing}")
    } else {
        format!("{n} {thing}s")
    }
}

/// The names pattern `p` binds, in preorder. A pattern nests as deep as its program, so the
/// patterns still to read are kept on a heap stack.
fn names(p: &Pattern) -> Vec<Arc<str>> {
    let mut out = Vec::new();
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Bind(x) => out.push(x.clone()),
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter().rev()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter().rev().map(|(_, q)| q)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
    out
}

/// The [`Uses`] of the lambda body `b`, each body's found once: a lambda inside `b` adds the
/// uses of its own body, less the names bound around it in `b`.
fn body_uses(b: At<'_>, bodies: &mut Bodies, places: &Places) -> Uses {
    if let Some(u) = bodies.get(&b.id) {
        return u.clone();
    }
    // A body waits at a lambda whose body is not yet known while that body is walked; lambdas
    // nest as deep as the program, so the waiting walks are kept on a heap stack.
    let mut walks = vec![UseWalk::new(b)];
    loop {
        let w = walks.last_mut().expect("a walk");
        match w.todo.pop() {
            Some(Visit::Lam(ps, inner)) => match bodies.get(&inner.id) {
                Some(u) => {
                    w.bind(ps);
                    u.iter().for_each(|u| w.add(u.clone()));
                    w.unbind(ps);
                }
                None => {
                    w.todo.push(Visit::Lam(ps, inner));
                    walks.push(UseWalk::new(inner));
                }
            },
            Some(v) => w.visit(v, places),
            None => {
                let w = walks.pop().expect("a walk");
                let u: Uses = w.out.into();
                bodies.insert(w.body.id, u.clone());
                if walks.is_empty() {
                    return u;
                }
            }
        }
    }
}

/// A step of a [`UseWalk`].
enum Visit<'t> {
    Term(At<'t>),
    /// `t` under the binders `xs`.
    Under(Cow<'t, [Arc<str>]>, At<'t>),
    Unbind(Cow<'t, [Arc<str>]>),
    /// A lambda of parameters `ps` and body `b`: the uses of `b` less `ps`.
    Lam(&'t [Arc<str>], At<'t>),
}

/// The walk of one lambda body for [`body_uses`].
struct UseWalk<'t> {
    body: At<'t>,
    /// How many binders in the body are around the current subterm, for each name.
    bound: HashMap<Arc<str>, usize>,
    seen: HashSet<Use>,
    out: Vec<Use>,
    todo: Vec<Visit<'t>>,
    /// The parts of the subterm being visited, reused from one to the next.
    parts: Vec<&'t Term>,
}

impl<'t> UseWalk<'t> {
    fn new(body: At<'t>) -> UseWalk<'t> {
        UseWalk {
            body,
            bound: HashMap::new(),
            seen: HashSet::new(),
            out: Vec::new(),
            todo: vec![Visit::Term(body)],
            parts: Vec::new(),
        }
    }

    fn add(&mut self, u: Use) {
        if let Use::Free(x) = &u
            && self.bound.contains_key(x)
        {
            return;
        }
        if self.seen.insert(u.clone()) {
            self.out.push(u);
        }
    }

    fn bind(&mut self, xs: &[Arc<str>]) {
        for x in xs {
            *self.bound.entry(x.clone()).or_default() += 1;
        }
    }

    fn unbind(&mut self, xs: &[Arc<str>]) {
        for x in xs {
            let n = self.bound.get_mut(x).expect("a bound name");
            *n -= 1;
            if *n == 0 {
                self.bound.remove(x);
            }
        }
    }

    /// Does `v`, or schedules the visits of its parts; [`Visit::Lam`] is [`body_uses`]'s.
    fn visit(&mut self, v: Visit<'t>, places: &Places) {
        let here = match v {
            Visit::Term(t) => t,
            Visit::Under(xs, t) => {
                self.bind(&xs);
                self.todo.push(Visit::Unbind(xs));
                self.todo.push(Visit::Term(t));
                return;
            }
            Visit::Unbind(xs) => {
                self.unbind(&xs);
                return;
            }
            Visit::Lam(..) => unreachable!("body_uses visits a lambda"),
        };
        let p = |j, t| places.part(here, j, t);
        let one = |x: &'t Arc<str>| Cow::Borrowed(std::slice::from_ref(x));
        match here.t {
            Term::Lit(_) | Term::PrimFn(_) => {}
            Term::Var(x) => self.add(Use::Free(x.clone())),
            Term::Read(q) => self.add(Use::Port(q.clone())),
            Term::Lam(ps, b) => self.todo.push(Visit::Lam(ps, p(0, b))),
            Term::Let(x, e, b) => {
                self.todo.push(Visit::Under(one(x), p(1, b)));
                self.todo.push(Visit::Term(p(0, e)));
            }
            Term::Match(s, arms) => {
                for (j, (q, a)) in arms.iter().enumerate().rev() {
                    self.todo
                        .push(Visit::Under(Cow::Owned(names(q)), p(1 + j, a)));
                }
                self.todo.push(Visit::Term(p(0, s)));
            }
            Term::Fam { domain, var, body } => {
                self.todo.push(Visit::Under(one(var), p(1, body)));
                self.todo.push(Visit::Term(p(0, domain)));
            }
            Term::Fix {
                init,
                step,
                this,
                key,
                kind: FixKind::Definedness,
                ..
            } => {
                let xs = Cow::Owned(vec![this.clone(), key.clone()]);
                self.todo.push(Visit::Under(xs, p(1, step)));
                self.todo.push(Visit::Term(p(0, init)));
            }
            // The rest bind no name: their parts are visited in turn.
            t => {
                if let Term::Push(q, _) = t {
                    self.add(Use::Port(q.clone()));
                }
                parts(t, &mut self.parts);
                let first = places.first(here);
                let parts = self.parts.drain(..).enumerate().rev();
                self.todo
                    .extend(parts.map(|(j, t)| Visit::Term(At { t, id: first + j })));
            }
        }
    }
}

/// Pushes the parts of `t` on `todo`, in the order of its fields.
fn parts<'a>(t: &'a Term, todo: &mut Vec<&'a Term>) {
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => {}
        Term::Lam(_, b) => todo.push(b),
        Term::App(g, args) => {
            todo.push(g);
            todo.extend(args);
        }
        Term::Prim(_, args) => todo.extend(args),
        Term::Let(_, e, b) => todo.extend([&**e, b]),
        Term::If(c, a, b) => todo.extend([&**c, a, b]),
        Term::Match(s, arms) => {
            todo.push(s);
            todo.extend(arms.iter().map(|(_, a)| a));
        }
        Term::Fam { domain, body, .. } => todo.extend([&**domain, body]),
        Term::Reindex { family, kf, vf, .. } => todo.extend([&**family, kf, vf]),
        Term::Discard { family, sel } => todo.extend([&**family, sel]),
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => {
            todo.extend([&**family, op]);
            todo.extend(identity.as_deref());
        }
        Term::Fix {
            init, step, kind, ..
        } => {
            todo.extend([&**init, step]);
            if let FixKind::Lattice { join } = kind {
                todo.push(join);
            }
        }
        Term::Gen {
            init, step, guard, ..
        } => todo.extend([&**init, step, guard]),
        Term::Push(_, v) => todo.push(v),
    }
}

/// `s` with its argument index mapped by `map`.
fn renumbered(s: &Src, map: &[usize]) -> Src {
    match s {
        Src::Arg(i) => Src::Arg(map[*i]),
        s => s.clone(),
    }
}

/// Maps the argument indices `r`'s own nodes and results read; inner regions are isolated.
fn renumber(r: &mut Region, map: &[usize]) {
    for n in &mut r.nodes {
        for s in &mut n.inputs {
            *s = renumbered(s, map);
        }
    }
    for s in &mut r.results {
        *s = renumbered(s, map);
    }
}

/// The kernel term a graph computes: each node a `let`, in the region's order, and each region
/// the body of a lambda, a family, a loop or a match arm. A read or a push is the kernel's
/// `Read` or `Push`; a state edge carries no value, so it becomes `()`, and the order of the
/// `let`s, which is the order of the nodes, keeps the order of the effects.
pub fn raise(g: &Region) -> Result<Term, String> {
    if g.results.is_empty() || g.results.len() != 1 + g.args.len() {
        return Err(format!(
            "the root region has {} and {}, and a term's root has one value and a state \
             result for each state argument",
            plural(g.args.len(), "argument"),
            plural(g.results.len(), "result")
        ));
    }
    let units = vec![unit(); g.args.len()];
    raise_from(Raising::region(g, units, Caps::Given(&[]), 0), "r", None)
}

/// The term region `r` computes, its arguments being `args`: [`raise`] for a region that is
/// not a root, such as a function's body with its captured values (step L1.34).
pub fn raise_with(r: &Region, args: &[Term]) -> Result<Term, String> {
    raise_from(
        Raising::region(r, Vec::new(), Caps::Given(args), 0),
        "r",
        None,
    )
}

/// The term `node` computes alone, its inputs being `ins`. It reads the node's regions and
/// no copy of them, so a caller holding a node of any depth pays only for the node's own
/// inputs and, when the term runs, what it raises.
///
/// `node` is node `number` of a legalized graph whose swapped nodes are `swapped`
/// ([`super::legalize::Legalized`]): a swapped node, `node` or one in its regions, is raised
/// as the operator the program wrote on its inputs in written order, so the kernel's refusal
/// names what the program wrote.
pub fn raise_node(
    node: &Node,
    number: usize,
    swapped: &Swapped,
    ins: &[Term],
) -> Result<Term, String> {
    let at = "r.0";
    let first = swapped.contains(number);
    let mut written = Written {
        swapped,
        next: number + 1,
    };
    raise_from(
        Raising::node(node, Cow::Borrowed(ins), at, 0, first)?,
        at,
        Some(&mut written),
    )
}

/// The swapped nodes of a legalized graph, and the number of the next node raised.
struct Written<'s> {
    swapped: &'s Swapped,
    next: usize,
}

fn unit() -> Term {
    Term::Lit(zed_kernel::Value::tuple(Vec::new()))
}

fn fresh_name(fresh: &mut usize) -> Arc<str> {
    *fresh += 1;
    format!("\0raise{fresh}").into()
}

/// Where a region being raised finds the arguments after its own.
enum Caps<'g> {
    Given(&'g [Term]),
    /// The inputs of the node at this depth of the stack, from this index on: the inputs the
    /// region captures, read where they are, not copied.
    Node(usize, usize),
}

/// A part of the graph being raised. A graph nests as deep as its program, so the parts being
/// raised are kept on a heap stack (step T2-mid), each region under the node that holds it.
enum Raising<'g> {
    Region {
        r: &'g Region,
        /// The region's own arguments, before those of `caps`.
        own: Vec<Term>,
        caps: Caps<'g>,
        /// A `let` for each node raised so far, in node order.
        lets: Vec<(Arc<str>, Term)>,
        /// The length of the path before this region's part of it.
        mark: usize,
    },
    Node {
        node: &'g Node,
        ins: Cow<'g, [Term]>,
        /// The terms of the node's regions raised so far.
        subs: Vec<Term>,
        /// The names drawn for those regions' binders, in order.
        names: Vec<Arc<str>>,
        /// The arms' patterns, their binders renamed, of a `match`.
        pats: Vec<Pattern>,
        /// Whether legalization swapped the node: it is raised as the operator written.
        swapped: bool,
        mark: usize,
    },
}

impl<'g> Raising<'g> {
    fn region(r: &'g Region, own: Vec<Term>, caps: Caps<'g>, mark: usize) -> Raising<'g> {
        Raising::Region {
            r,
            own,
            caps,
            lets: Vec::new(),
            mark,
        }
    }

    /// The node `node` at the path `at`, unless its op has no kernel term.
    fn node(
        node: &'g Node,
        ins: Cow<'g, [Term]>,
        at: &str,
        mark: usize,
        swapped: bool,
    ) -> Result<Raising<'g>, String> {
        if let op @ (Op::Derived(_) | Op::Rec | Op::Wave) = &node.op {
            return Err(format!(
                "{at}: `{}` has no kernel term here; the lowering does not make it",
                op_name(op)
            ));
        }
        Ok(Raising::Node {
            node,
            ins,
            subs: Vec::new(),
            names: Vec::new(),
            pats: Vec::new(),
            swapped,
            mark,
        })
    }

    fn mark(&self) -> usize {
        match self {
            Raising::Region { mark, .. } | Raising::Node { mark, .. } => *mark,
        }
    }
}

/// What a step of [`raise_from`] gives: a part to raise next, or the term of the top part.
enum Raised<'g> {
    Enter(Raising<'g>),
    Done(Term),
}

/// The term of `first`, at the path `path`. Fresh names are drawn in the order a recursive walk
/// would draw them: a node's binders, then each of its regions in turn, then the node's `let`.
/// With `written`, nodes are numbered as they are entered, `first` being the one before
/// `written.next`, and a swapped node is raised as the operator written.
fn raise_from<'g>(
    first: Raising<'g>,
    path: &str,
    mut written: Option<&mut Written<'_>>,
) -> Result<Term, String> {
    let mut path = path.to_string();
    let mut fresh = 0;
    let mut stack = vec![first];
    loop {
        let depth = stack.len() - 1;
        let (below, top) = stack.split_at_mut(depth);
        let next = match &mut top[0] {
            Raising::Region {
                r, own, caps, lets, ..
            } => {
                let r: &'g Region = r;
                let caps: &[Term] = match caps {
                    Caps::Given(c) => c,
                    Caps::Node(d, from) => match &below[*d] {
                        Raising::Node { ins, .. } => &ins[*from..],
                        Raising::Region { .. } => unreachable!("a region's node holds it"),
                    },
                };
                let term_of = |s: &Src, lets: &[(Arc<str>, Term)]| match s {
                    Src::Arg(i) => match own.get(*i) {
                        Some(t) => t.clone(),
                        None => caps[*i - own.len()].clone(),
                    },
                    Src::Out(n, p) if r.nodes[*n].outputs[*p].is_state() => unit(),
                    Src::Out(n, _) => Term::Var(lets[*n].0.clone()),
                    Src::Const(v) => Term::Lit(v.clone()),
                };
                let k = lets.len();
                match r.nodes.get(k) {
                    Some(node) => {
                        let ins: Vec<Term> = node.inputs.iter().map(|s| term_of(s, lets)).collect();
                        let mark = path.len();
                        write!(path, ".{k}").expect("a String takes any text");
                        let swapped = written.as_deref_mut().is_some_and(|w| {
                            w.next += 1;
                            w.swapped.contains(w.next - 1)
                        });
                        let raising = Raising::node(node, Cow::Owned(ins), &path, mark, swapped)?;
                        Raised::Enter(raising)
                    }
                    None => {
                        let body = term_of(&r.results[0], lets);
                        Raised::Done(mem::take(lets).into_iter().rev().fold(body, |b, (x, e)| {
                            Term::Let(x, Shared::new(e), Shared::new(b))
                        }))
                    }
                }
            }
            Raising::Node {
                node,
                ins,
                subs,
                names,
                pats,
                swapped,
                ..
            } => {
                let node: &'g Node = node;
                let i = subs.len();
                if i < regions_raised(&node.op) {
                    let (own, from) = open(node, ins.len(), i, names, pats, &mut fresh);
                    let mark = path.len();
                    write!(path, "/{i}").expect("a String takes any text");
                    let caps = Caps::Node(depth, from);
                    Raised::Enter(Raising::region(&node.regions[i], own, caps, mark))
                } else {
                    Raised::Done(close(
                        node,
                        mem::take(ins),
                        mem::take(subs),
                        mem::take(names),
                        mem::take(pats),
                        *swapped,
                    ))
                }
            }
        };
        match next {
            Raised::Enter(part) => stack.push(part),
            Raised::Done(t) => {
                let done = stack.pop().expect("the part raised");
                path.truncate(done.mark());
                match stack.last_mut() {
                    None => return Ok(t),
                    Some(Raising::Region { lets, .. }) => lets.push((fresh_name(&mut fresh), t)),
                    Some(Raising::Node { subs, .. }) => subs.push(t),
                }
            }
        }
    }
}

/// How many regions of a node of `op` its term holds; an op of no kernel term is refused before.
fn regions_raised(op: &Op) -> usize {
    match op {
        Op::Lambda | Op::Fam | Op::Fix { .. } => 1,
        Op::If | Op::Gen(_) => 2,
        Op::Match(ps) => ps.len(),
        Op::Prim(_)
        | Op::Apply
        | Op::Reindex(_)
        | Op::Discard
        | Op::Fold { .. }
        | Op::Read(_)
        | Op::Push(_)
        | Op::Derived(_)
        | Op::Rec
        | Op::Wave => 0,
    }
}

/// The arguments of region `i` of `node`, which has `inputs` inputs: the terms of its own,
/// binders drawn fresh, and the index of the first input it captures.
fn open(
    node: &Node,
    inputs: usize,
    i: usize,
    names: &mut Vec<Arc<str>>,
    pats: &mut Vec<Pattern>,
    fresh: &mut usize,
) -> (Vec<Term>, usize) {
    let mut name = |names: &mut Vec<Arc<str>>| {
        let x = fresh_name(fresh);
        names.push(x.clone());
        Term::Var(x)
    };
    match &node.op {
        Op::Lambda => {
            let lead = &node.regions[0].args[..node.regions[0].args.len() - inputs];
            let vars = lead
                .iter()
                .map(|e| if e.is_state() { unit() } else { name(names) })
                .collect();
            (vars, 0)
        }
        Op::If => (Vec::new(), 1),
        Op::Match(ps) => {
            let mut p = ps[i].clone();
            let mut xs = Vec::new();
            rename(&mut p, &mut || {
                let x = fresh_name(fresh);
                xs.push(Term::Var(x.clone()));
                x
            });
            pats.push(p);
            (xs, 1)
        }
        Op::Fam | Op::Gen(_) => (vec![name(names)], 1),
        Op::Fix { lattice: true, .. } => (vec![name(names)], 2),
        Op::Fix { lattice: false, .. } => (vec![name(names), name(names)], 1),
        op => unreachable!("`{}` has no region in its term", op_name(op)),
    }
}

/// The term `node` computes, its inputs being `ins` and its regions' terms `subs`: the inputs
/// moved into the term when they are owned, copied only when the caller keeps them. A node
/// legalization `swapped` is the operator the program wrote on its inputs in written order.
fn close(
    node: &Node,
    ins: Cow<'_, [Term]>,
    subs: Vec<Term>,
    names: Vec<Arc<str>>,
    pats: Vec<Pattern>,
    swapped: bool,
) -> Term {
    let a = |i: usize| Shared::new(ins[i].clone());
    let mut subs = subs.into_iter();
    let mut names = names.into_iter();
    let mut sub = || Shared::new(subs.next().expect("each region raised"));
    let mut name = || names.next().expect("each binder named");
    match &node.op {
        Op::Prim(p) if ins.is_empty() && p.arity().is_some() => Term::PrimFn(*p),
        Op::Prim(p) if swapped => {
            let mut ins = ins.into_owned();
            ins.reverse();
            Term::Prim(written(*p), ins)
        }
        Op::Prim(p) => Term::Prim(*p, ins.into_owned()),
        // A state edge has no term: the kernel orders effects by evaluation. The states
        // are the last inputs, one for each output after the value.
        Op::Apply => {
            let mut ins = ins.into_owned();
            ins.truncate(ins.len() + 1 - node.outputs.len());
            let f = ins.remove(0);
            Term::App(Shared::new(f), ins)
        }
        Op::Lambda => Term::Lam(names.collect(), sub()),
        Op::If => Term::If(a(0), sub(), sub()),
        Op::Match(_) => Term::Match(a(0), pats.into_iter().zip(subs).collect()),
        Op::Fam => Term::Fam {
            domain: a(0),
            var: name(),
            body: sub(),
        },
        Op::Reindex(w) => Term::Reindex {
            family: a(0),
            kf: a(1),
            vf: a(2),
            witness: w.clone(),
        },
        Op::Discard => Term::Discard {
            family: a(0),
            sel: a(1),
        },
        Op::Fold {
            depth,
            identity,
            ev,
        } => Term::Fold {
            family: a(0),
            op: a(1),
            identity: identity.then(|| a(2)),
            depth: *depth,
            ev: ev.clone(),
        },
        Op::Fix { lattice: true, ev } => Term::Fix {
            init: a(0),
            step: Shared::new(Term::Lam(vec![name()], sub())),
            this: "".into(),
            key: "".into(),
            kind: FixKind::Lattice { join: a(1) },
            ev: ev.clone(),
        },
        Op::Fix { lattice: false, ev } => Term::Fix {
            init: a(0),
            step: sub(),
            this: name(),
            key: name(),
            kind: FixKind::Definedness,
            ev: ev.clone(),
        },
        Op::Gen(pos) => Term::Gen {
            init: a(0),
            step: Shared::new(Term::Lam(vec![name()], sub())),
            guard: Shared::new(Term::Lam(vec![name()], sub())),
            pos: *pos,
        },
        Op::Read(p) => Term::Read(p.clone()),
        Op::Push(p) => Term::Push(p.clone(), a(1)),
        op @ (Op::Derived(_) | Op::Rec | Op::Wave) => {
            unreachable!("`{}` is refused before its regions", op_name(op))
        }
    }
}

/// Renames each binder of `p`, in preorder, to what `f` gives. A pattern nests as deep as its
/// program, so the patterns still to rename are kept on a heap stack.
fn rename(p: &mut Pattern, f: &mut dyn FnMut() -> Arc<str>) {
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Bind(x) => *x = f(),
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter_mut().rev()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter_mut().rev().map(|(_, q)| q)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
}
