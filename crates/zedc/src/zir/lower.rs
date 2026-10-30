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
//!   capture, through every region between, in the order the body first reads it. The regions
//!   of one node share one capture list, the union of theirs in order, so each region is
//!   renumbered to it after it is built.
//! - **State edges on demand.** The first read of or push to a port takes its state edge,
//!   which enters a region as a capture and leaves it as a result, after the values. Only
//!   `match` and `port` regions carry state (step L1.31), so a `match` or `if` whose arms touch
//!   different ports passes each port's state through the arm that does not touch it, and the
//!   root region is a `port` region when the term uses a port and a `function` region when not.
//! - **A function that uses a port is inlined.** A function region carries no state, so a
//!   `let`-bound lambda whose body reads or pushes a port, or calls such a function, makes no
//!   node, and each call lowers its body in place. L1 has no recursion, so this ends; used as a
//!   value, such a function is an error.
//! - **CSE by content address.** A node is entered in its region under the address of its
//!   canonical form ([`super::canon::address`] of a one-node region), and a
//!   second node with that address is not added: its uses read the first. Nodes that differ
//!   only in hints, binder names or facet order are one node. A read, a push, or a node an
//!   effect passes through is never merged, since its state input is used once.
//! - **Edges carry `_` and no facts but hints.** The checker's types and the store's domains
//!   reach the graph in a later step; the lowering keeps the term's structure exactly.
//!
//! [`raise`] maps a graph back to a kernel term: each node a `let`, each
//! region a lambda body or a match arm. Evaluating the raised term gives the original term's
//! value, which is how the tests check the lowering against the interpreter.

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::term::{FixKind, Pattern, Prim, Term};
use zed_kernel::types::Type;

use super::{Edge, Node, Op, Region, RegionKind, Src, canon, kind_name, op_name, validate};
use crate::address::ContentAddress;
use crate::canon::Facet;

/// What a name is bound to while lowering.
#[derive(Clone)]
enum Val {
    /// An edge of the region at the given depth of the frame stack.
    Src(Src, usize),
    /// A prelude word, not yet a node.
    Prim(Prim),
    /// A function that uses a port, inlined at each call.
    Closure(Arc<Closure>),
}

/// A `let`-bound lambda whose body uses a port, with the bindings it was defined under.
struct Closure {
    params: Vec<Arc<str>>,
    body: Arc<Term>,
    env: Vec<(Arc<str>, Val)>,
}

/// A region being built.
struct Frame {
    region: Region,
    /// The arguments before the captures.
    fixed: usize,
    /// Where each capture comes from in the enclosing region, in argument order.
    captures: Vec<Src>,
    /// The current state edge of each port the region has touched.
    states: Vec<(Arc<str>, Src)>,
    /// The nodes entered by content address.
    seen: HashMap<ContentAddress, usize>,
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
            states: Vec::new(),
            seen: HashMap::new(),
        }
    }
}

/// A finished region with what its node needs to know about it.
struct Built {
    region: Region,
    fixed: usize,
    captures: Vec<Src>,
    states: Vec<(Arc<str>, Src)>,
    values: usize,
}

struct Lower {
    frames: Vec<Frame>,
    scope: Vec<(Arc<str>, Val)>,
    fresh: usize,
}

/// The graph of the closed term `t`, validated. A prelude word is read only where the term
/// binds it, as [`crate::interp::prelude`] does.
pub fn lower(t: &Term) -> Result<Region, String> {
    let mut l = Lower {
        frames: vec![Frame::new(RegionKind::Function, Vec::new())],
        scope: Vec::new(),
        fresh: 0,
    };
    let v = l.term(t)?;
    let out = l.src(v)?;
    let f = l.frames.pop().expect("the root frame");
    let mut root = f.region;
    root.results.push(out);
    for a in &root.args {
        if let Edge::State(p) = a {
            let (_, s) = f
                .states
                .iter()
                .find(|(q, _)| q == p)
                .expect("a port's state");
            root.results.push(s.clone());
        }
    }
    if root.args.iter().any(Edge::is_state) {
        root.kind = RegionKind::Port;
    }
    validate(&root).map_err(|e| format!("the lowered graph is invalid: {e}"))?;
    Ok(root)
}

impl Lower {
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

    fn lookup(&self, x: &str) -> Result<Val, String> {
        match self.scope.iter().rev().find(|(n, _)| &**n == x) {
            Some((_, v)) => Ok(v.clone()),
            None => Err(format!(
                "`{x}` is not bound, and a term lowers only when every name it reads is bound \
                 in it or is a prelude word"
            )),
        }
    }

    /// `v` as an edge of the current region.
    fn src(&mut self, v: Val) -> Result<Src, String> {
        match v {
            Val::Src(s, at) => Ok(self.bring(s, at)),
            Val::Prim(p) => self.prim_fn(p),
            Val::Closure(c) => Err(format!(
                "a function of {} that uses a port is used as a value: a function region \
                 carries no state edge, so such a function is only called, and each call is \
                 inlined",
                plural(c.params.len(), "parameter")
            )),
        }
    }

    /// The edge `s` of the region at depth `at`, captured into each region down to the top.
    fn bring(&mut self, s: Src, at: usize) -> Src {
        if matches!(s, Src::Const(_)) {
            return s;
        }
        let mut s = s;
        for k in at + 1..self.frames.len() {
            s = self.capture(k, s);
        }
        s
    }

    /// The argument of frame `k` that receives `s`, an edge of frame `k - 1`. A name read twice
    /// is captured twice; [`Lower::node`] merges the repeats.
    fn capture(&mut self, k: usize, s: Src) -> Src {
        let edge = self.frames[k - 1].region.edge(&s);
        let f = &mut self.frames[k];
        f.captures.push(s);
        f.region.args.push(edge);
        Src::Arg(f.region.args.len() - 1)
    }

    /// The current state edge of port `p` in frame `k`, taken from the enclosing regions.
    fn state(&mut self, k: usize, p: &Arc<str>) -> Result<Src, String> {
        if let Some((_, s)) = self.frames[k].states.iter().find(|(q, _)| q == p) {
            return Ok(s.clone());
        }
        let s = if k == 0 {
            let root = &mut self.frames[0].region;
            root.args.push(Edge::State(p.clone()));
            Src::Arg(root.args.len() - 1)
        } else {
            let kind = self.frames[k].region.kind;
            if !matches!(kind, RegionKind::Match | RegionKind::Port) {
                return Err(format!(
                    "port `{p}` is used inside a {} region, and a state edge enters only a \
                     match or port region (step L1.31): a port is read or pushed outside \
                     functions, loops and families, or in a function inlined there",
                    kind_name(kind)
                ));
            }
            let outer = self.state(k - 1, p)?;
            let f = &mut self.frames[k];
            f.captures.push(outer);
            f.region.args.push(Edge::State(p.clone()));
            Src::Arg(f.region.args.len() - 1)
        };
        self.frames[k].states.push((p.clone(), s.clone()));
        Ok(s)
    }

    fn set_state(&mut self, p: &Arc<str>, s: Src) {
        let f = self.frame();
        match f.states.iter_mut().find(|(q, _)| q == p) {
            Some(e) => e.1 = s,
            None => f.states.push((p.clone(), s)),
        }
    }

    /// Adds `node` to the current region, or finds the node with its content address. A node
    /// that takes a state edge never repeats one, since each state edge is used once, so the
    /// effects stay apart without a test of their own.
    fn add(&mut self, node: Node) -> usize {
        let key = canon::address(&Region {
            kind: RegionKind::Function,
            args: Vec::new(),
            nodes: vec![node.clone()],
            results: Vec::new(),
        });
        let f = self.frame();
        if let Some(&n) = f.seen.get(&key) {
            return n;
        }
        f.region.nodes.push(node);
        let n = f.region.nodes.len() - 1;
        f.seen.insert(key, n);
        n
    }

    /// A one-output node with no region.
    fn leaf(&mut self, op: Op, inputs: Vec<Src>) -> Val {
        let n = self.add(Node {
            op,
            inputs,
            outputs: vec![top()],
            regions: Vec::new(),
        });
        Val::Src(Src::Out(n, 0), self.top())
    }

    fn values(&mut self, ts: &[Term]) -> Result<Vec<Src>, String> {
        ts.iter()
            .map(|t| {
                let v = self.term(t)?;
                self.src(v)
            })
            .collect()
    }

    fn value(&mut self, t: &Term) -> Result<Src, String> {
        let v = self.term(t)?;
        self.src(v)
    }

    /// Builds a region of `kind` whose first arguments are `params`, yielding `body`.
    fn region(
        &mut self,
        kind: RegionKind,
        params: &[Arc<str>],
        body: &Term,
    ) -> Result<Built, String> {
        let args = params.iter().map(|_| top()).collect();
        self.frames.push(Frame::new(kind, args));
        let depth = self.top();
        let mark = self.scope.len();
        for (i, p) in params.iter().enumerate() {
            self.scope.push((p.clone(), Val::Src(Src::Arg(i), depth)));
        }
        let out = self.value(body);
        self.scope.truncate(mark);
        let mut f = self.frames.pop().expect("the region's frame");
        f.region.results.push(out?);
        Ok(Built {
            region: f.region,
            fixed: f.fixed,
            captures: f.captures,
            states: f.states,
            values: 1,
        })
    }

    /// The node `op` with inputs `fixed` and regions `built`, their captures merged.
    fn node(&mut self, op: Op, fixed: Vec<Src>, built: Vec<Built>) -> Val {
        // The union of the regions' captures, in order.
        let mut caps: Vec<Src> = Vec::new();
        for b in &built {
            for c in &b.captures {
                if !caps.contains(c) {
                    caps.push(c.clone());
                }
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
        for b in built {
            let map: Vec<usize> = (0..b.fixed)
                .chain(
                    b.captures
                        .iter()
                        .map(|c| b.fixed + caps.iter().position(|d| d == c).expect("merged")),
                )
                .collect();
            let mut r = b.region;
            renumber(&mut r, &map);
            r.args.truncate(b.fixed);
            r.args.extend(edges.iter().cloned());
            for (i, p) in &ports {
                let fin = match b.states.iter().find(|(q, _)| q == p) {
                    // The node that last used the port, never an argument.
                    Some((_, s)) => s.clone(),
                    None => Src::Arg(b.fixed + i),
                };
                r.results.push(fin);
            }
            regions.push(r);
        }
        let mut outputs = vec![top(); values];
        outputs.extend(ports.iter().map(|(_, p)| Edge::State(p.clone())));
        let mut inputs = fixed;
        inputs.extend(caps);
        let n = self.add(Node {
            op,
            inputs,
            outputs,
            regions,
        });
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
                super::text::spell(p)
            ));
        }
        let Val::Src(s, _) = self.leaf(Op::Prim(p), Vec::new()) else {
            unreachable!("a leaf is an edge")
        };
        Ok(s)
    }

    /// Whether `t`, a lambda body, reads or pushes a port or calls a function that does.
    fn effectful(&self, t: &Term) -> bool {
        let mut hit = false;
        visit(t, &mut |s| match s {
            Term::Read(_) | Term::Push(..) => hit = true,
            Term::Var(x) => {
                if let Ok(Val::Closure(_)) = self.lookup(x) {
                    hit = true;
                }
            }
            _ => {}
        });
        hit
    }

    fn term(&mut self, t: &Term) -> Result<Val, String> {
        let at = self.top();
        Ok(match t {
            Term::Lit(v) => Val::Src(Src::Const(v.clone()), at),
            Term::Var(x) => self.lookup(x)?,
            Term::PrimFn(p) => Val::Prim(*p),
            Term::Let(x, e, body) => {
                let v = match &**e {
                    Term::Lam(ps, b) if self.effectful(b) => Val::Closure(Arc::new(Closure {
                        params: ps.clone(),
                        body: b.clone(),
                        env: self.scope.clone(),
                    })),
                    e => self.term(e)?,
                };
                if let Val::Src(Src::Out(n, p), d) = &v
                    && *d == at
                {
                    let e = &mut self.frame().region.nodes[*n].outputs[*p];
                    if let Edge::Value(e) = e
                        && !e.facets.iter().any(|f| f.hint && &*f.kind == "name")
                    {
                        e.facets.push(Facet {
                            hint: true,
                            kind: "name".into(),
                            value: zed_kernel::Value::Str(x.clone()),
                        });
                    }
                }
                self.scope.push((x.clone(), v));
                let out = self.term(body);
                self.scope.pop();
                out?
            }
            Term::Lam(ps, body) => {
                let b = self.region(RegionKind::Function, ps, body)?;
                self.node(Op::Lambda, Vec::new(), vec![b])
            }
            Term::App(f, args) => {
                if let Term::Lam(ps, body) = &**f
                    && ps.len() == args.len()
                {
                    let vs = args
                        .iter()
                        .map(|a| self.term(a))
                        .collect::<Result<Vec<_>, _>>()?;
                    return self.bound(ps, vs, body);
                }
                match self.term(f)? {
                    Val::Prim(p) if p.arity().is_none_or(|k| k == args.len()) => {
                        let ins = self.values(args)?;
                        self.leaf(Op::Prim(p), ins)
                    }
                    Val::Closure(c) => {
                        if c.params.len() != args.len() {
                            return Err(format!(
                                "a function of {} that uses a port is called with {}",
                                plural(c.params.len(), "parameter"),
                                plural(args.len(), "argument")
                            ));
                        }
                        let vs = args
                            .iter()
                            .map(|a| self.term(a))
                            .collect::<Result<Vec<_>, _>>()?;
                        let saved = std::mem::replace(&mut self.scope, c.env.clone());
                        let out = self.bound(&c.params, vs, &c.body);
                        self.scope = saved;
                        out?
                    }
                    fv => {
                        let mut ins = vec![self.src(fv)?];
                        ins.extend(self.values(args)?);
                        self.leaf(Op::Apply, ins)
                    }
                }
            }
            Term::Prim(p, args) => {
                if let Some(k) = p.arity()
                    && k != args.len()
                {
                    return Err(format!(
                        "the primitive `{}` takes {} and is given {}",
                        super::text::spell(*p),
                        plural(k, "argument"),
                        args.len()
                    ));
                }
                let ins = self.values(args)?;
                self.leaf(Op::Prim(*p), ins)
            }
            Term::If(c, a, b) => {
                let c = self.value(c)?;
                let ra = self.region(RegionKind::Match, &[], a)?;
                let rb = self.region(RegionKind::Match, &[], b)?;
                self.node(Op::If, vec![c], vec![ra, rb])
            }
            Term::Match(s, arms) => {
                let s = self.value(s)?;
                let mut built = Vec::new();
                for (p, body) in arms {
                    built.push(self.region(RegionKind::Match, &names(p), body)?);
                }
                let ps = arms.iter().map(|(p, _)| p.clone()).collect();
                self.node(Op::Match(ps), vec![s], built)
            }
            Term::Fam { domain, var, body } => {
                let d = self.value(domain)?;
                let b = self.region(RegionKind::Function, std::slice::from_ref(var), body)?;
                self.node(Op::Fam, vec![d], vec![b])
            }
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            } => {
                let ins = vec![self.value(family)?, self.value(kf)?, self.value(vf)?];
                self.leaf(Op::Reindex(witness.clone()), ins)
            }
            Term::Discard { family, sel } => {
                let ins = vec![self.value(family)?, self.value(sel)?];
                self.leaf(Op::Discard, ins)
            }
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            } => {
                let mut ins = vec![self.value(family)?, self.value(op)?];
                if let Some(id) = identity {
                    ins.push(self.value(id)?);
                }
                let op = Op::Fold {
                    depth: *depth,
                    identity: identity.is_some(),
                    ev: ev.clone(),
                };
                self.leaf(op, ins)
            }
            Term::Fix {
                init,
                step,
                this,
                key,
                kind,
                ev,
            } => match kind {
                FixKind::Lattice { join } => {
                    let fixed = vec![self.value(init)?, self.value(join)?];
                    let x = self.fresh();
                    let body = Term::App(step.clone(), vec![Term::Var(x.clone())]);
                    let b = self.region(RegionKind::Loop, &[x], &body)?;
                    let op = Op::Fix {
                        lattice: true,
                        ev: ev.clone(),
                    };
                    self.node(op, fixed, vec![b])
                }
                FixKind::Definedness => {
                    let fixed = vec![self.value(init)?];
                    let names = [this.clone(), key.clone()];
                    let b = self.region(RegionKind::Loop, &names, step)?;
                    let op = Op::Fix {
                        lattice: false,
                        ev: ev.clone(),
                    };
                    self.node(op, fixed, vec![b])
                }
            },
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => {
                let fixed = vec![self.value(init)?];
                let mut built = Vec::new();
                for f in [step, guard] {
                    let x = self.fresh();
                    let body = Term::App(f.clone(), vec![Term::Var(x.clone())]);
                    built.push(self.region(RegionKind::Loop, &[x], &body)?);
                }
                self.node(Op::Gen(*pos), fixed, built)
            }
            Term::Read(p) => {
                let s = self.state(at, p)?;
                let n = self.add(Node {
                    op: Op::Read(p.clone()),
                    inputs: vec![s],
                    outputs: vec![top(), Edge::State(p.clone())],
                    regions: Vec::new(),
                });
                self.set_state(p, Src::Out(n, 1));
                Val::Src(Src::Out(n, 0), at)
            }
            Term::Push(p, v) => {
                let v = self.value(v)?;
                let s = self.state(at, p)?;
                let n = self.add(Node {
                    op: Op::Push(p.clone()),
                    inputs: vec![s, v],
                    outputs: vec![top(), Edge::State(p.clone())],
                    regions: Vec::new(),
                });
                self.set_state(p, Src::Out(n, 1));
                Val::Src(Src::Out(n, 0), at)
            }
        })
    }

    /// `body` with `params` bound to `vals`, lowered in the current region.
    fn bound(&mut self, params: &[Arc<str>], vals: Vec<Val>, body: &Term) -> Result<Val, String> {
        let mark = self.scope.len();
        self.scope.extend(params.iter().cloned().zip(vals));
        let out = self.term(body);
        self.scope.truncate(mark);
        out
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

/// The names pattern `p` binds, in preorder.
fn names(p: &Pattern) -> Vec<Arc<str>> {
    let mut out = Vec::new();
    fn go(p: &Pattern, out: &mut Vec<Arc<str>>) {
        match p {
            Pattern::Bind(x) => out.push(x.clone()),
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter().for_each(|q| go(q, out)),
            Pattern::Fields(_, fs) => fs.iter().for_each(|(_, q)| go(q, out)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
    go(p, &mut out);
    out
}

/// Calls `f` on `t` and every subterm, in preorder.
fn visit(t: &Term, f: &mut dyn FnMut(&Term)) {
    f(t);
    let mut each = |ts: &[&Term]| ts.iter().for_each(|t| visit(t, f));
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => {}
        Term::Lam(_, b) => each(&[b]),
        Term::App(g, args) => {
            each(&[g]);
            args.iter().for_each(|a| visit(a, f));
        }
        Term::Prim(_, args) => args.iter().for_each(|a| visit(a, f)),
        Term::Let(_, e, b) => each(&[e, b]),
        Term::If(c, a, b) => each(&[c, a, b]),
        Term::Match(s, arms) => {
            each(&[s]);
            arms.iter().for_each(|(_, a)| visit(a, f));
        }
        Term::Fam { domain, body, .. } => each(&[domain, body]),
        Term::Reindex { family, kf, vf, .. } => each(&[family, kf, vf]),
        Term::Discard { family, sel } => each(&[family, sel]),
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => {
            each(&[family, op]);
            identity.iter().for_each(|i| visit(i, f));
        }
        Term::Fix {
            init, step, kind, ..
        } => {
            each(&[init, step]);
            if let FixKind::Lattice { join } = kind {
                visit(join, f);
            }
        }
        Term::Gen {
            init, step, guard, ..
        } => each(&[init, step, guard]),
        Term::Push(_, v) => each(&[v]),
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
    let mut n = 0;
    raise_region(g, &units, &mut n, "r")
}

fn unit() -> Term {
    Term::Lit(zed_kernel::Value::Tuple(Vec::new()))
}

fn raise_region(r: &Region, args: &[Term], fresh: &mut usize, path: &str) -> Result<Term, String> {
    let name = |fresh: &mut usize| -> Arc<str> {
        *fresh += 1;
        format!("\0raise{fresh}").into()
    };
    let mut lets: Vec<(Arc<str>, Term)> = Vec::new();
    let mut outs: Vec<Arc<str>> = Vec::new();
    let term_of = |s: &Src, outs: &[Arc<str>]| match s {
        Src::Arg(i) => args[*i].clone(),
        Src::Out(n, p) if r.nodes[*n].outputs[*p].is_state() => unit(),
        Src::Out(n, _) => Term::Var(outs[*n].clone()),
        Src::Const(v) => Term::Lit(v.clone()),
    };
    for (k, node) in r.nodes.iter().enumerate() {
        let at = format!("{path}.{k}");
        let ins: Vec<Term> = node.inputs.iter().map(|s| term_of(s, &outs)).collect();
        let a = |i: usize| Arc::new(ins[i].clone());
        let sub = |i: usize, fixed: Vec<Term>, from: usize, fresh: &mut usize| {
            let mut xs = fixed;
            xs.extend(ins[from..].iter().cloned());
            raise_region(&node.regions[i], &xs, fresh, &format!("{at}/{i}"))
        };
        let t = match &node.op {
            Op::Prim(p) if ins.is_empty() && p.arity().is_some() => Term::PrimFn(*p),
            Op::Prim(p) => Term::Prim(*p, ins.clone()),
            Op::Apply => Term::App(a(0), ins[1..].to_vec()),
            Op::Lambda => {
                let k = node.regions[0].args.len() - ins.len();
                let ps: Vec<Arc<str>> = (0..k).map(|_| name(fresh)).collect();
                let vars = ps.iter().map(|p| Term::Var(p.clone())).collect();
                Term::Lam(ps, Arc::new(sub(0, vars, 0, fresh)?))
            }
            Op::If => Term::If(
                a(0),
                Arc::new(sub(0, Vec::new(), 1, fresh)?),
                Arc::new(sub(1, Vec::new(), 1, fresh)?),
            ),
            Op::Match(ps) => {
                let mut arms = Vec::new();
                for (i, p) in ps.iter().enumerate() {
                    let mut p = p.clone();
                    let mut xs = Vec::new();
                    rename(&mut p, &mut || {
                        let x = name(fresh);
                        xs.push(Term::Var(x.clone()));
                        x
                    });
                    arms.push((p, sub(i, xs, 1, fresh)?));
                }
                Term::Match(a(0), arms)
            }
            Op::Fam => {
                let var = name(fresh);
                let body = sub(0, vec![Term::Var(var.clone())], 1, fresh)?;
                Term::Fam {
                    domain: a(0),
                    var,
                    body: Arc::new(body),
                }
            }
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
            Op::Fix { lattice: true, ev } => {
                let x = name(fresh);
                let body = sub(0, vec![Term::Var(x.clone())], 2, fresh)?;
                Term::Fix {
                    init: a(0),
                    step: Arc::new(Term::Lam(vec![x], Arc::new(body))),
                    this: "".into(),
                    key: "".into(),
                    kind: FixKind::Lattice { join: a(1) },
                    ev: ev.clone(),
                }
            }
            Op::Fix { lattice: false, ev } => {
                let (this, key) = (name(fresh), name(fresh));
                let xs = vec![Term::Var(this.clone()), Term::Var(key.clone())];
                Term::Fix {
                    init: a(0),
                    step: Arc::new(sub(0, xs, 1, fresh)?),
                    this,
                    key,
                    kind: FixKind::Definedness,
                    ev: ev.clone(),
                }
            }
            Op::Gen(pos) => {
                let mut fs = Vec::new();
                for i in 0..2 {
                    let x = name(fresh);
                    let body = sub(i, vec![Term::Var(x.clone())], 1, fresh)?;
                    fs.push(Arc::new(Term::Lam(vec![x], Arc::new(body))));
                }
                let guard = fs.pop().expect("two regions");
                let step = fs.pop().expect("two regions");
                Term::Gen {
                    init: a(0),
                    step,
                    guard,
                    pos: *pos,
                }
            }
            Op::Read(p) => Term::Read(p.clone()),
            Op::Push(p) => Term::Push(p.clone(), a(1)),
            op @ (Op::Derived(_) | Op::Rec | Op::Wave) => {
                return Err(format!(
                    "{at}: `{}` has no kernel term here; the lowering does not make it",
                    op_name(op)
                ));
            }
        };
        let x = name(fresh);
        lets.push((x.clone(), t));
        outs.push(x);
    }
    let body = term_of(&r.results[0], &outs);
    Ok(lets
        .into_iter()
        .rev()
        .fold(body, |b, (x, e)| Term::Let(x, Arc::new(e), Arc::new(b))))
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
