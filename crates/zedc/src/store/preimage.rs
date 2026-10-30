//! The tonicity of the scalar primitives and the scalar entries of the preimage catalog
//! (DESIGN.md sec:domains, "Backward transfer, and `@ensure`", and sec:constraints, "Both
//! directions, one rule"; step L1.25).
//!
//! A preimage is computed over a kernel term whose free names are the inputs, each with an
//! interval domain, from a demand on the term's value: an interval for an integer term, `true`
//! or `false` for a test. The result is a box, one interval per input, that contains every
//! point of the inputs' domains at which the term meets the demand: a necessary condition,
//! which narrowing needs. When the box contains no other point it is marked exact, and it is
//! then also sufficient, which a precondition needs.
//!
//! The catalog, applied from the term's root down:
//!
//! - an input meets the demand exactly where its value lies in it;
//! - a term with no input is evaluated, and keeps the whole box or none of it;
//! - `+`, `-` and `*` with one constant operand, and Euclidean `div` and `mod` by a constant,
//!   invert exactly, `mod` as up to [`PIECE_LIMIT`] pieces within the operand's forward
//!   interval;
//! - `-x`, `abs` and `**` by a constant invert exactly at their endpoints, by the tonicity of
//!   each sign part (the M0.5 revision table); a product of one value `k` times is read as its
//!   `k`th power first (sec:constraints);
//! - `min` and `max` invert exactly with a constant operand, and with two operands when the
//!   demand is a ray in the direction both must meet, or the other direction, where either may;
//! - a comparison with a constant operand is a demand on the other operand, and between two
//!   terms a demand on their difference;
//! - `&&`, `||` and `!` meet, join and swap the preimages of their operands;
//! - a branch's preimage is the union of each arm's preimage met with its guard's;
//! - a `let` and a call to a lambda are read through, as the evaluator reads them;
//! - other integer operations take the HC4 projection of the M0.5 table, which is necessary and
//!   not exact;
//! - string operations other than `len`, and calls to names that are not lambdas (foreign
//!   calls), stop the transfer, and the stop is reported, as is any other term the scalar
//!   catalog does not cover.
//!
//! A union of two boxes is a box, and so exact, only when one contains the other or they differ
//! in one input. After the catalog, a result not marked exact is checked by forward transfer
//! over it: when every point it holds must meet the demand, it is exact. A result still not
//! exact whose term the linear-relation domain states (step L1.38: sums, constant multiples,
//! Euclidean `div` and `mod` by a constant, `min`, `max`, `abs`, branches and the tests over
//! them) is narrowed to the relation's projection on each input, within the box, and is exact
//! when the box entails the relation; when it is not, the relation is kept with the box. And a
//! result that is still not exact, finite and within the enumeration budget of step M0.10 is
//! enumerated: the term is run at each point, and the result is the projection of the points
//! that meet the demand, exact when they form a box. An enumeration that meets a term the
//! evaluator cannot run removes nothing.

use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::budgets::ENUMERATION_BUDGET;
use zed_kernel::{Prim, Term, Value, eval};

use super::interval::{End, IntervalSet, PIECE_LIMIT};
use super::presburger::{self, Con, Formula, Lin, Over, Relation};
use super::revision::{self, Op, Tonicity};
use End::{Fin, NegInf, PosInf};

/// An interval per input name.
pub type Domains = BTreeMap<Arc<str>, IntervalSet>;

/// What the term's value must be.
#[derive(Clone, PartialEq, Debug)]
pub enum Demand {
    /// An integer in the set.
    Ints(IntervalSet),
    /// The boolean.
    Bool(bool),
}

impl Demand {
    /// Whether `v` meets the demand. An integer outside `i64` lies in the set when the set is
    /// unbounded on its side.
    pub fn holds(&self, v: &Value) -> bool {
        match (self, v) {
            (Demand::Ints(z), Value::Int(n)) => z.contains(*n),
            (Demand::Ints(z), Value::Big(_)) => {
                let positive = v > &Value::Int(0);
                match z.bounds() {
                    Some((lo, hi)) => (positive && hi == PosInf) || (!positive && lo == NegInf),
                    None => false,
                }
            }
            (Demand::Bool(w), Value::Bool(b)) => w == b,
            _ => false,
        }
    }
}

/// Why the transfer stopped.
#[derive(Clone, PartialEq, Debug)]
pub enum StopKind {
    /// A string operation other than `len`.
    String(Prim),
    /// A call to a name that is not a lambda, or a free name that is not an input.
    Foreign(Arc<str>),
    /// A term the scalar catalog does not cover: families, folds, `fix`, patterns, ports, or
    /// calls nested past the inlining depth.
    Outside,
}

/// A reported stop: its kind and the term it stopped at.
#[derive(Clone, PartialEq, Debug)]
pub struct Stop {
    /// Why.
    pub kind: StopKind,
    /// The term, as the kernel prints it.
    pub term: String,
}

impl fmt::Display for Stop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StopKind::String(p) => write!(f, "string operation {p:?} stops the transfer at ")?,
            StopKind::Foreign(n) => write!(f, "foreign name `{n}` stops the transfer at ")?,
            StopKind::Outside => write!(f, "no scalar catalog entry for ")?,
        }
        write!(f, "{}", self.term)
    }
}

/// A preimage.
#[derive(Clone, PartialEq, Debug)]
pub struct Preimage {
    /// The box: every point at which the term meets the demand lies in it.
    pub domains: Domains,
    /// Whether every point of the box meets the demand.
    pub exact: bool,
    /// Whether the box came from enumeration.
    pub enumerated: bool,
    /// Where the transfer stopped.
    pub stops: Vec<Stop>,
    /// The relation the inputs must meet, when the box is not exact and the linear-relation
    /// domain states the demand: every point meeting the demand meets it, and every point of
    /// the box meeting it meets the demand.
    pub relation: Option<Relation>,
}

/// The deepest nesting of calls read through before the transfer stops.
pub const CALL_DEPTH: u32 = 64;

/// The preimage of `demand` under `term`, whose free names in `inputs` range over their
/// domains.
pub fn preimage(term: &Term, inputs: &Domains, demand: &Demand) -> Preimage {
    let root = Rc::new(Scope::Empty);
    let mut cx = Cx::new(inputs);
    let mut r = cx.back(term, &root, demand);
    let mut stops = std::mem::take(&mut cx.stops);
    let mut enumerated = false;
    // The piece limit of step M0.5 holds for every element.
    for d in r.dom.values_mut() {
        if d.pieces().len() > PIECE_LIMIT {
            *d = d.cap(PIECE_LIMIT);
            r.exact = false;
        }
    }
    if !r.exact && !is_empty(&r.dom) {
        let mut over = Cx::new(&r.dom);
        if over.fwd(term, &root, 0).meets(demand) {
            r.exact = true;
        }
    }
    let mut relation = None;
    if !r.exact
        && !is_empty(&r.dom)
        && let Some((dom, exact, rel)) = linear(term, &r.dom, demand)
    {
        r = Res { dom, exact };
        relation = (!exact).then_some(rel);
    }
    if !r.exact
        && let Some(e) = enumerate(term, &r.dom, demand)
    {
        r = e;
        enumerated = true;
        if r.exact {
            relation = None;
        }
    }
    stops.dedup();
    Preimage {
        domains: r.dom,
        exact: r.exact,
        enumerated,
        stops,
        relation,
    }
}

/// The relations the linear-relation domain states for `terms`, tests over the free names
/// `inputs`, with one numbering of auxiliary variables; products of two symbols are atoms
/// when `products` holds. `None` when a term is outside the domain.
pub fn relations(terms: &[&Term], inputs: &[Arc<str>], products: bool) -> Option<Vec<Relation>> {
    let doms: Domains = inputs
        .iter()
        .map(|n| (n.clone(), IntervalSet::top()))
        .collect();
    let cx = Cx::new(&doms);
    let mut tr = Tr {
        defs: Vec::new(),
        products,
    };
    let root = Rc::new(Scope::Empty);
    let mut out = Vec::new();
    for t in terms {
        let first = tr.defs.len();
        let body = cx.formula(&mut tr, t, &root, 0)?;
        out.push(Relation {
            body,
            defs: tr.defs[first..].to_vec(),
        });
    }
    Some(out)
}

/// The linear stage: the relation of the demand over the box `dom`, the box narrowed to its
/// projections, whether the box entails the relation, and the relation. `None` when the term
/// is outside the domain or a budget is passed.
fn linear(term: &Term, dom: &Domains, demand: &Demand) -> Option<(Domains, bool, Relation)> {
    let cx = Cx::new(dom);
    let mut tr = Tr {
        defs: Vec::new(),
        products: false,
    };
    let root = Rc::new(Scope::Empty);
    let body = match demand {
        Demand::Bool(w) => {
            let f = cx.formula(&mut tr, term, &root, 0)?;
            if *w { f } else { Formula::negate(f) }
        }
        Demand::Ints(z) => {
            let l = cx.lin(&mut tr, term, &root, 0)?;
            presburger::within(&l, z).ok()?
        }
    };
    let rel = Relation {
        body,
        defs: tr.defs,
    };
    let go = || -> Result<(Domains, bool), Over> {
        let within = |d: &Domains| -> Result<Formula, Over> {
            let parts = d
                .iter()
                .map(|(k, v)| presburger::member(&presburger::Atom::Sym(k.clone()), v))
                .collect::<Result<_, _>>()?;
            Ok(Formula::and(parts))
        };
        let whole = Formula::and(vec![rel.defined(), within(dom)?, rel.body.clone()]);
        let mentioned = rel.body.atoms();
        let mut out = Domains::new();
        for (k, v) in dom {
            let a = presburger::Atom::Sym(k.clone());
            let p = if mentioned.contains(&a)
                || rel.defs.iter().any(|(_, _, f)| f.atoms().contains(&a))
            {
                presburger::project(&whole, &a)?.meet(v)
            } else {
                v.clone()
            };
            out.insert(k.clone(), p);
        }
        if is_empty(&out) {
            let none = out
                .keys()
                .map(|k| (k.clone(), IntervalSet::empty()))
                .collect();
            return Ok((none, true));
        }
        let mut capped = false;
        for v in out.values_mut() {
            if v.pieces().len() > PIECE_LIMIT {
                *v = v.cap(PIECE_LIMIT);
                capped = true;
            }
        }
        let outside = Formula::and(vec![
            rel.defined(),
            within(&out)?,
            Formula::negate(rel.body.clone()),
        ]);
        let exact = !capped && presburger::satisfiable(&outside)?.is_none();
        Ok((out, exact))
    };
    let (out, exact) = go().ok()?;
    Some((out, exact, rel))
}

/// The translation of terms into the linear-relation domain: the definitions of the auxiliary
/// variables made so far.
struct Tr {
    defs: Vec<(u32, String, Formula)>,
    products: bool,
}

impl Tr {
    fn aux(&mut self, what: String, def: Formula) -> presburger::Atom {
        let n = self.defs.len() as u32;
        self.defs.push((n, what, def));
        presburger::Atom::Aux(n)
    }
}

/// The tonicity of a scalar primitive in argument `arg`, the others fixed, with `false` below
/// `true` for the tests (sec:domains, rule (1)); `None` where the primitive is not of one
/// tonicity on each part of one sign, or not a scalar operator.
pub fn tonicity(p: Prim, arg: usize) -> Option<Tonicity> {
    use Prim::*;
    let t = match (p, arg) {
        (Add | Sub | Mul | Min | Max, _) | (IntDiv, _) | (Mod, _) | (Neg | Abs, 0) => {
            revision::tonicity(op(p, None)?, arg)
        }
        (Lt | Le, 0) | (Gt | Ge, 1) | (Not, 0) => Tonicity::Down,
        (Lt | Le, 1) | (Gt | Ge, 0) | (And | Or, _) => Tonicity::Up,
        _ => return None,
    };
    (t != Tonicity::None).then_some(t)
}

/// The revision table's operator for a primitive, with the constant exponent of `**`.
fn op(p: Prim, exponent: Option<u32>) -> Option<Op> {
    Some(match p {
        Prim::Add => Op::Add,
        Prim::Sub => Op::Sub,
        Prim::Mul => Op::Mul,
        Prim::IntDiv => Op::Div,
        Prim::Mod => Op::Mod,
        Prim::Neg => Op::Neg,
        Prim::Abs => Op::Abs,
        Prim::Min => Op::Min,
        Prim::Max => Op::Max,
        Prim::Pow => Op::Pow(exponent?),
        _ => return None,
    })
}

fn is_empty(d: &Domains) -> bool {
    d.values().any(IntervalSet::is_empty)
}

/// A scope: the names bound by `let` and by calls, each to a term and the scope it is read
/// in.
enum Scope {
    Empty,
    Bind(Arc<str>, Term, Env, Env),
}

type Env = Rc<Scope>;

/// What a call reaches.
enum Callee<'e> {
    /// A lambda's parameters and body, with the scope the body is read in.
    Lam(&'e [Arc<str>], &'e Term, &'e Env),
    /// A primitive, as a prelude word binds it (the interpreter's prelude, step L1.18).
    Prim(Prim),
}

fn bind(parent: &Env, name: &Arc<str>, term: &Term, at: &Env) -> Env {
    Rc::new(Scope::Bind(
        name.clone(),
        term.clone(),
        at.clone(),
        parent.clone(),
    ))
}

fn lookup<'a>(env: &'a Env, name: &str) -> Option<(&'a Term, &'a Env)> {
    let mut s = env;
    while let Scope::Bind(n, t, at, parent) = &**s {
        if &**n == name {
            return Some((t, at));
        }
        s = parent;
    }
    None
}

/// A result before the final checks: the box and whether it is exact.
#[derive(Clone)]
struct Res {
    dom: Domains,
    exact: bool,
}

/// What forward transfer knows of a term's value.
struct Fwd {
    /// The integers it may be.
    ints: IntervalSet,
    /// Whether it may be `true`, and `false`.
    bools: (bool, bool),
    /// Whether it may be a failure: an atom such as `#divByZero`, which every primitive but
    /// `==` and `!=` passes through.
    fails: bool,
    /// Whether it may be a value of another kind: a string, a float, a function.
    other: bool,
}

impl Fwd {
    fn int(ints: IntervalSet) -> Fwd {
        Fwd {
            ints,
            ..Fwd::none()
        }
    }

    fn bools(t: bool, f: bool) -> Fwd {
        Fwd {
            bools: (t, f),
            ..Fwd::none()
        }
    }

    fn none() -> Fwd {
        Fwd {
            ints: IntervalSet::empty(),
            bools: (false, false),
            fails: false,
            other: false,
        }
    }

    fn top() -> Fwd {
        Fwd {
            ints: IntervalSet::top(),
            bools: (true, true),
            fails: true,
            other: true,
        }
    }

    fn has_bools(&self) -> bool {
        self.bools.0 || self.bools.1
    }

    /// Whether it is certainly an integer.
    fn is_int(&self) -> bool {
        !self.fails && !self.other && !self.has_bools()
    }

    /// Whether it is certainly a boolean.
    fn is_bool(&self) -> bool {
        !self.fails && !self.other && self.ints.is_empty()
    }

    /// Whether every value it may be meets `d`.
    fn meets(&self, d: &Demand) -> bool {
        match d {
            Demand::Ints(z) => self.is_int() && self.ints.is_subset(z),
            Demand::Bool(w) => self.is_bool() && !(if *w { self.bools.1 } else { self.bools.0 }),
        }
    }
}

struct Cx<'a> {
    inputs: &'a Domains,
    stops: Vec<Stop>,
}

impl<'a> Cx<'a> {
    fn new(inputs: &'a Domains) -> Self {
        Cx {
            inputs,
            stops: Vec::new(),
        }
    }

    fn all(&self) -> Res {
        Res {
            dom: self.inputs.clone(),
            exact: true,
        }
    }

    fn none(&self) -> Res {
        Res {
            dom: self
                .inputs
                .keys()
                .map(|k| (k.clone(), IntervalSet::empty()))
                .collect(),
            exact: true,
        }
    }

    fn stop(&mut self, kind: StopKind, t: &Term) -> Res {
        let s = Stop {
            kind,
            term: t.to_string(),
        };
        if !self.stops.contains(&s) {
            self.stops.push(s);
        }
        Res {
            dom: self.inputs.clone(),
            exact: false,
        }
    }

    fn meet(&self, a: Res, b: Res) -> Res {
        let dom: Domains = a
            .dom
            .iter()
            .map(|(k, v)| (k.clone(), v.meet(&b.dom[k])))
            .collect();
        if is_empty(&dom) {
            return self.none();
        }
        Res {
            dom,
            exact: a.exact && b.exact,
        }
    }

    /// The union, as the per-input join of the two boxes: exact when both are and the union
    /// is itself a box.
    fn union(&self, a: Res, b: Res) -> Res {
        if is_empty(&a.dom) {
            return b;
        }
        if is_empty(&b.dom) {
            return a;
        }
        let differ = a.dom.iter().filter(|(k, v)| **v != b.dom[*k]).count();
        let within = |x: &Domains, y: &Domains| x.iter().all(|(k, v)| v.is_subset(&y[k]));
        let boxed = differ <= 1 || within(&a.dom, &b.dom) || within(&b.dom, &a.dom);
        Res {
            dom: a
                .dom
                .iter()
                .map(|(k, v)| (k.clone(), v.join(&b.dom[k])))
                .collect(),
            exact: a.exact && b.exact && boxed,
        }
    }

    /// The input names the term reads, or `None` when it reads a term the catalog does not
    /// follow.
    fn mentions(&self, t: &Term, env: &Env, depth: u32) -> Option<bool> {
        if depth > CALL_DEPTH {
            return None;
        }
        let any = |cx: &Self, ts: &mut dyn Iterator<Item = (&Term, Env)>| -> Option<bool> {
            let mut m = false;
            for (t, e) in ts {
                m |= cx.mentions(t, &e, depth + 1)?;
            }
            Some(m)
        };
        match t {
            Term::Lit(_) | Term::PrimFn(_) => Some(false),
            Term::Var(x) => match lookup(env, x) {
                Some((bt, benv)) => self.mentions(bt, benv, depth + 1),
                None => Some(self.inputs.contains_key(x)),
            },
            Term::Let(n, e, b) => {
                let inner = bind(env, n, e, env);
                any(self, &mut [(&**e, env.clone()), (&**b, inner)].into_iter())
            }
            Term::Lam(ps, b) => {
                // A parameter is not an input, even where it shadows one.
                let mut inner = env.clone();
                for p in ps {
                    inner = bind(&inner, p, &Term::Lit(Value::Bool(false)), &inner);
                }
                self.mentions(b, &inner, depth + 1)
            }
            Term::App(f, args) => any(
                self,
                &mut std::iter::once((&**f, env.clone()))
                    .chain(args.iter().map(|a| (a, env.clone()))),
            ),
            Term::Prim(_, args) => any(self, &mut args.iter().map(|a| (a, env.clone()))),
            Term::If(g, a, b) => any(
                self,
                &mut [
                    (&**g, env.clone()),
                    (&**a, env.clone()),
                    (&**b, env.clone()),
                ]
                .into_iter(),
            ),
            _ => None,
        }
    }

    /// The term with every bound name replaced by the closed term it is bound to, for a term
    /// that reads no input.
    fn close(t: &Term, env: &Env, depth: u32) -> Option<Term> {
        if depth > CALL_DEPTH {
            return None;
        }
        let c = |t: &Term, e: &Env| Cx::close(t, e, depth + 1);
        Some(match t {
            Term::Var(x) => match lookup(env, x) {
                Some((bt, benv)) => c(bt, benv)?,
                None => t.clone(),
            },
            Term::Lit(_) | Term::PrimFn(_) => t.clone(),
            Term::Let(n, e, b) => {
                // The body reads `n` as the closed bound term.
                let e = c(e, env)?;
                let inner = bind(env, n, &e, &Rc::new(Scope::Empty));
                c(b, &inner)?
            }
            Term::Lam(ps, b) => {
                let mut inner = env.clone();
                for p in ps {
                    inner = bind(&inner, p, &Term::Var(p.clone()), &Rc::new(Scope::Empty));
                }
                Term::Lam(ps.clone(), Arc::new(c(b, &inner)?))
            }
            Term::App(f, args) => Term::App(
                Arc::new(c(f, env)?),
                args.iter().map(|a| c(a, env)).collect::<Option<_>>()?,
            ),
            Term::Prim(p, args) => {
                Term::Prim(*p, args.iter().map(|a| c(a, env)).collect::<Option<_>>()?)
            }
            Term::If(g, a, b) => Term::If(
                Arc::new(c(g, env)?),
                Arc::new(c(a, env)?),
                Arc::new(c(b, env)?),
            ),
            _ => return None,
        })
    }

    /// The value of a term that reads no input, when the evaluator can compute it.
    fn constant(&self, t: &Term, env: &Env) -> Option<Value> {
        if self.mentions(t, env, 0)? {
            return None;
        }
        eval(&Cx::close(t, env, 0)?).ok()
    }

    fn constant_int(&self, t: &Term, env: &Env) -> Option<i64> {
        match self.constant(t, env)? {
            Value::Int(n) => Some(n),
            _ => None,
        }
    }

    /// The function a call reaches, with the scope its body is read in.
    fn callee<'e>(&self, f: &'e Term, env: &'e Env) -> Result<Callee<'e>, Option<Arc<str>>> {
        let (mut f, mut env) = (f, env);
        loop {
            match f {
                Term::Lam(ps, b) => return Ok(Callee::Lam(ps, b, env)),
                Term::PrimFn(p) => return Ok(Callee::Prim(*p)),
                Term::Var(x) => match lookup(env, x) {
                    Some((bt, benv)) => (f, env) = (bt, benv),
                    None => return Err(Some(x.clone())),
                },
                _ => return Err(None),
            }
        }
    }

    /// The scope of a call's body: the lambda's scope with each parameter bound to its
    /// argument, read in the caller's scope.
    fn call_env(ps: &[Arc<str>], args: &[Term], lam: &Env, caller: &Env) -> Env {
        let mut e = lam.clone();
        for (p, a) in ps.iter().zip(args) {
            e = bind(&e, p, a, caller);
        }
        e
    }

    /// The factors of a product of one value read `k` times, as that value and `k`.
    fn power<'e>(&self, t: &'e Term, env: &'e Env) -> Option<(&'e Term, &'e Env, u32)> {
        fn factors<'e>(t: &'e Term, env: &'e Env, out: &mut Vec<(&'e Term, &'e Env)>) {
            let (mut t, mut env) = (t, env);
            while let Term::Var(x) = t
                && let Some((bt, benv)) = lookup(env, x)
            {
                (t, env) = (bt, benv);
            }
            match t {
                Term::Prim(Prim::Mul, args) if args.len() == 2 => {
                    factors(&args[0], env, out);
                    factors(&args[1], env, out);
                }
                _ => out.push((t, env)),
            }
        }
        let mut fs = Vec::new();
        factors(t, env, &mut fs);
        let (first, fenv) = fs[0];
        let one = |&(t, e): &(&Term, &Env)| match (t, first) {
            (Term::Var(x), Term::Var(y)) if x == y => true,
            _ => t == first && Rc::ptr_eq(e, fenv),
        };
        (fs.len() >= 2 && fs.iter().all(one)).then_some((first, fenv, fs.len() as u32))
    }

    // ---- Into the linear-relation domain ------------------------------------------------

    /// The linear term an integer term states over the inputs.
    fn lin(&self, tr: &mut Tr, t: &Term, env: &Env, depth: u32) -> Option<Lin> {
        use Prim::*;
        if depth > CALL_DEPTH {
            return None;
        }
        let d = depth + 1;
        if let Some(v) = self.constant(t, env) {
            return match v {
                Value::Int(n) => Some(Lin::constant(n.into())),
                _ => None,
            };
        }
        match t {
            Term::Var(x) => match lookup(env, x) {
                Some((bt, benv)) => self.lin(tr, bt, &benv.clone(), d),
                None => self
                    .inputs
                    .contains_key(x)
                    .then(|| Lin::atom(presburger::Atom::Sym(x.clone()))),
            },
            Term::Let(n, e, b) => self.lin(tr, b, &bind(env, n, e, env), d),
            Term::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    let inner = Cx::call_env(ps, args, lam, env);
                    self.lin(tr, body, &inner, d)
                }
                Callee::Prim(p) => self.lin(tr, &Term::Prim(p, args.clone()), env, d),
                Callee::Lam(..) => None,
            },
            Term::If(g, a, b) => {
                let g = self.formula(tr, g, env, d)?;
                let (la, lb) = (self.lin(tr, a, env, d)?, self.lin(tr, b, env, d)?);
                let v = presburger::Atom::Aux(tr.defs.len() as u32);
                let x = Lin::atom(v.clone());
                let def = Formula::or(vec![
                    Formula::and(vec![g.clone(), Formula::Con(Con::eq(&x, &la).ok()?)]),
                    Formula::and(vec![
                        Formula::negate(g),
                        Formula::Con(Con::eq(&x, &lb).ok()?),
                    ]),
                ]);
                tr.aux(t.to_string(), def);
                Some(x)
            }
            Term::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => {
                let arg = |tr: &mut Tr, i: usize| self.lin(tr, &args[i], env, d);
                match p {
                    Add => arg(tr, 0)?.plus(&arg(tr, 1)?).ok(),
                    Sub => arg(tr, 0)?.minus(&arg(tr, 1)?).ok(),
                    Neg => arg(tr, 0)?.times(-1).ok(),
                    Mul => {
                        let (a, b) = (arg(tr, 0)?, arg(tr, 1)?);
                        if !tr.products && !a.terms.is_empty() && !b.terms.is_empty() {
                            return None;
                        }
                        a.product(&b)?.ok()
                    }
                    Pow => match self.constant_int(&args[1], env)? {
                        0 => Some(Lin::constant(1)),
                        1 => arg(tr, 0),
                        2 if tr.products => {
                            let a = arg(tr, 0)?;
                            a.product(&a)?.ok()
                        }
                        _ => None,
                    },
                    IntDiv | Mod => {
                        let c = self.constant_int(&args[1], env).filter(|c| *c != 0)?;
                        let a = arg(tr, 0)?;
                        // `a == c·q + r` and `0 <= r < |c|`: Euclidean.
                        let n = tr.defs.len() as u32;
                        let (q, r) = (
                            Lin::atom(presburger::Atom::Aux(n)),
                            Lin::atom(presburger::Atom::Aux(n + 1)),
                        );
                        let c = i128::from(c);
                        let def = Formula::and(vec![
                            Formula::Con(Con::eq(&a, &q.times(c).ok()?.plus(&r).ok()?).ok()?),
                            Formula::Con(Con::ge(&r, &Lin::constant(0)).ok()?),
                            Formula::Con(Con::ge(&Lin::constant(c.abs() - 1), &r).ok()?),
                        ]);
                        let shown = |op: &str| format!("{} {op} {c}", args[0]);
                        tr.defs.push((n, shown("div"), def));
                        tr.defs.push((n + 1, shown("mod"), Formula::top()));
                        Some(if *p == IntDiv { q } else { r })
                    }
                    Min | Max | Abs => {
                        let a = arg(tr, 0)?;
                        let b = if *p == Abs {
                            a.times(-1).ok()?
                        } else {
                            arg(tr, 1)?
                        };
                        let x = Lin::atom(presburger::Atom::Aux(tr.defs.len() as u32));
                        // `min` takes `a` where `a <= b`, `max` and `abs` where `a >= b`.
                        let (lo, hi) = if *p == Min { (&a, &b) } else { (&b, &a) };
                        let first = Con::ge(hi, lo).ok()?;
                        let def = Formula::or(vec![
                            Formula::and(vec![
                                Formula::Con(first.clone()),
                                Formula::Con(Con::eq(&x, &a).ok()?),
                            ]),
                            Formula::and(vec![
                                Formula::negate(Formula::Con(first)),
                                Formula::Con(Con::eq(&x, &b).ok()?),
                            ]),
                        ]);
                        tr.aux(t.to_string(), def);
                        Some(x)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The formula a test states over the inputs.
    fn formula(&self, tr: &mut Tr, t: &Term, env: &Env, depth: u32) -> Option<Formula> {
        use Prim::*;
        if depth > CALL_DEPTH {
            return None;
        }
        let d = depth + 1;
        if let Some(v) = self.constant(t, env) {
            return match v {
                Value::Bool(true) => Some(Formula::top()),
                Value::Bool(false) => Some(Formula::bottom()),
                _ => None,
            };
        }
        match t {
            Term::Var(x) => {
                let (bt, benv) = lookup(env, x)?;
                self.formula(tr, bt, &benv.clone(), d)
            }
            Term::Let(n, e, b) => self.formula(tr, b, &bind(env, n, e, env), d),
            Term::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    let inner = Cx::call_env(ps, args, lam, env);
                    self.formula(tr, body, &inner, d)
                }
                Callee::Prim(p) => self.formula(tr, &Term::Prim(p, args.clone()), env, d),
                Callee::Lam(..) => None,
            },
            Term::If(g, a, b) => {
                let g = self.formula(tr, g, env, d)?;
                let (fa, fb) = (self.formula(tr, a, env, d)?, self.formula(tr, b, env, d)?);
                Some(Formula::or(vec![
                    Formula::and(vec![g.clone(), fa]),
                    Formula::and(vec![Formula::negate(g), fb]),
                ]))
            }
            Term::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => match p {
                Not => Some(Formula::negate(self.formula(tr, &args[0], env, d)?)),
                And | Or => {
                    let (a, b) = (
                        self.formula(tr, &args[0], env, d)?,
                        self.formula(tr, &args[1], env, d)?,
                    );
                    Some(if *p == And {
                        Formula::and(vec![a, b])
                    } else {
                        Formula::or(vec![a, b])
                    })
                }
                Lt | Le | Gt | Ge | Eq | Ne => {
                    let mark = tr.defs.len();
                    if let (Some(a), Some(b)) = (
                        self.lin(tr, &args[0], env, d),
                        self.lin(tr, &args[1], env, d),
                    ) {
                        let one = Lin::constant(1);
                        let c = match p {
                            Lt => Con::ge(&b, &a.plus(&one).ok()?),
                            Le => Con::ge(&b, &a),
                            Gt => Con::ge(&a, &b.plus(&one).ok()?),
                            Ge => Con::ge(&a, &b),
                            _ => Con::eq(&a, &b),
                        }
                        .ok()?;
                        let f = Formula::Con(c);
                        return Some(if *p == Ne { Formula::negate(f) } else { f });
                    }
                    tr.defs.truncate(mark);
                    if !matches!(p, Eq | Ne) {
                        return None;
                    }
                    // Two tests are equal where both hold or neither does.
                    let (a, b) = (
                        self.formula(tr, &args[0], env, d)?,
                        self.formula(tr, &args[1], env, d)?,
                    );
                    let same = Formula::or(vec![
                        Formula::and(vec![a.clone(), b.clone()]),
                        Formula::and(vec![Formula::negate(a), Formula::negate(b)]),
                    ]);
                    Some(if *p == Ne {
                        Formula::negate(same)
                    } else {
                        same
                    })
                }
                _ => None,
            },
            _ => None,
        }
    }

    // ---- Forward transfer -------------------------------------------------------------

    fn fwd(&mut self, t: &Term, env: &Env, depth: u32) -> Fwd {
        if depth > CALL_DEPTH {
            return Fwd::top();
        }
        let d = depth + 1;
        match t {
            Term::Lit(Value::Int(n)) => Fwd::int(IntervalSet::single(*n)),
            Term::Lit(Value::Bool(b)) => Fwd::bools(*b, !*b),
            Term::Lit(Value::Atom(_)) => Fwd {
                fails: true,
                ..Fwd::none()
            },
            Term::Lit(_) => Fwd {
                other: true,
                ..Fwd::none()
            },
            Term::Var(x) => match lookup(env, x) {
                Some((bt, benv)) => self.fwd(bt, &benv.clone(), d),
                None => match self.inputs.get(x) {
                    Some(dom) => Fwd::int(dom.clone()),
                    None => Fwd::top(),
                },
            },
            Term::Let(n, e, b) => self.fwd(b, &bind(env, n, e, env), d),
            Term::If(g, a, b) => {
                let g = self.fwd(g, env, d);
                // A guard that is not a test is a failure.
                let mut out = Fwd {
                    fails: !g.is_bool(),
                    ..Fwd::none()
                };
                for (arm, live) in [(a, g.bools.0), (b, g.bools.1)] {
                    if live {
                        let f = self.fwd(arm, env, d);
                        out.ints = out.ints.join(&f.ints);
                        out.bools = (out.bools.0 || f.bools.0, out.bools.1 || f.bools.1);
                        out.fails |= f.fails;
                        out.other |= f.other;
                    }
                }
                out
            }
            Term::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    let inner = Cx::call_env(ps, args, lam, env);
                    self.fwd(body, &inner, d)
                }
                Ok(Callee::Prim(p)) => self.fwd(&Term::Prim(p, args.clone()), env, d),
                _ => Fwd::top(),
            },
            Term::Prim(p, args) => self.fwd_prim(t, *p, args, env, d),
            _ => Fwd::top(),
        }
    }

    fn fwd_prim(&mut self, t: &Term, p: Prim, args: &[Term], env: &Env, d: u32) -> Fwd {
        use Prim::*;
        if p.arity().is_some_and(|n| n != args.len()) {
            return Fwd::top();
        }
        if p == Mul
            && let Some((base, benv, k)) = self.power(t, env)
        {
            let b = self.fwd(base, &benv.clone(), d);
            return self.arith(Op::Pow(k), &b, &b, false);
        }
        match p {
            Neg | Abs => {
                let a = self.fwd(&args[0], env, d);
                self.arith(op(p, None).expect("scalar"), &a, &a, false)
            }
            Pow => match self.constant_int(&args[1], env).map(u32::try_from) {
                Some(Ok(k)) => {
                    let a = self.fwd(&args[0], env, d);
                    self.arith(Op::Pow(k), &a, &a, false)
                }
                _ => Fwd::top(),
            },
            Add | Sub | Mul | IntDiv | Mod | Min | Max => {
                let a = self.fwd(&args[0], env, d);
                let b = self.fwd(&args[1], env, d);
                let by_zero = matches!(p, IntDiv | Mod) && b.ints.contains(0);
                self.arith(op(p, None).expect("scalar"), &a, &b, by_zero)
            }
            Lt | Le | Gt | Ge | Eq | Ne => {
                let a = self.fwd(&args[0], env, d);
                let b = self.fwd(&args[1], env, d);
                if a.is_int() && b.is_int() {
                    return compare(p, &a.ints, &b.ints);
                }
                // Values of other kinds compare as data under `==` and `!=`, and otherwise
                // fail or compare in an order this transfer does not follow.
                Fwd {
                    bools: (true, true),
                    fails: !matches!(p, Eq | Ne),
                    ..Fwd::none()
                }
            }
            Not => {
                let a = self.fwd(&args[0], env, d);
                Fwd {
                    bools: (a.bools.1, a.bools.0),
                    fails: !a.is_bool(),
                    ..Fwd::none()
                }
            }
            And | Or => {
                let a = self.fwd(&args[0], env, d);
                let b = self.fwd(&args[1], env, d);
                let (t, f) = if p == And {
                    (a.bools.0 && b.bools.0, a.bools.1 || b.bools.1)
                } else {
                    (a.bools.0 || b.bools.0, a.bools.1 && b.bools.1)
                };
                Fwd {
                    bools: (t, f),
                    fails: !a.is_bool() || !b.is_bool(),
                    ..Fwd::none()
                }
            }
            _ => Fwd::top(),
        }
    }

    /// An integer operator over its operands' forward values.
    fn arith(&self, o: Op, a: &Fwd, b: &Fwd, by_zero: bool) -> Fwd {
        Fwd {
            ints: revision::forward(o, &a.ints, &b.ints),
            fails: !a.is_int() || !b.is_int() || by_zero,
            ..Fwd::none()
        }
    }

    // ---- Backward transfer ------------------------------------------------------------

    fn back(&mut self, t: &Term, env: &Env, d: &Demand) -> Res {
        self.back_at(t, env, d, 0)
    }

    fn back_at(&mut self, t: &Term, env: &Env, d: &Demand, depth: u32) -> Res {
        if depth > CALL_DEPTH {
            return self.stop(StopKind::Outside, t);
        }
        if let Demand::Ints(z) = d
            && z.is_empty()
        {
            return self.none();
        }
        // A term that reads no input is decided by running it.
        if !matches!(t, Term::Var(_))
            && let Some(v) = self.constant(t, env)
        {
            return if d.holds(&v) { self.all() } else { self.none() };
        }
        let next = depth + 1;
        match t {
            Term::Var(x) => match lookup(env, x) {
                Some((bt, benv)) => self.back_at(bt, &benv.clone(), d, next),
                None => match (self.inputs.get(x), d) {
                    (Some(dom), Demand::Ints(z)) => {
                        let mut r = self.all();
                        r.dom.insert(x.clone(), dom.meet(z));
                        if is_empty(&r.dom) { self.none() } else { r }
                    }
                    (Some(_), Demand::Bool(_)) => self.none(),
                    (None, _) => self.stop(StopKind::Foreign(x.clone()), t),
                },
            },
            Term::Lit(v) => {
                if d.holds(v) {
                    self.all()
                } else {
                    self.none()
                }
            }
            Term::Let(n, e, b) => self.back_at(b, &bind(env, n, e, env), d, next),
            Term::If(g, a, b) => {
                let gt = self.back_at(g, env, &Demand::Bool(true), next);
                let at = self.back_at(a, env, d, next);
                let gf = self.back_at(g, env, &Demand::Bool(false), next);
                let bf = self.back_at(b, env, d, next);
                let yes = self.meet(gt, at);
                let no = self.meet(gf, bf);
                self.union(yes, no)
            }
            Term::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    let inner = Cx::call_env(ps, args, lam, env);
                    self.back_at(body, &inner, d, next)
                }
                Ok(Callee::Prim(p)) => self.back_at(&Term::Prim(p, args.clone()), env, d, next),
                Err(Some(name)) => self.stop(StopKind::Foreign(name), t),
                _ => self.stop(StopKind::Outside, t),
            },
            Term::Prim(p, args) => {
                if p.arity().is_some_and(|n| n != args.len()) {
                    return self.stop(StopKind::Outside, t);
                }
                self.back_prim(t, *p, args, env, d, next)
            }
            _ => self.stop(StopKind::Outside, t),
        }
    }

    fn back_prim(
        &mut self,
        t: &Term,
        p: Prim,
        args: &[Term],
        env: &Env,
        d: &Demand,
        depth: u32,
    ) -> Res {
        use Prim::*;
        let ints_of = |d: &Demand| match d {
            Demand::Ints(z) => Some(z.clone()),
            Demand::Bool(_) => None,
        };
        match p {
            Show | Lower | Upper | Trim | Concat => self.stop(StopKind::String(p), t),
            // `len` moves the demand to the length facet, which is not an input here; the
            // terms below it may still stop.
            Len => {
                self.scan(&args[0], env, depth);
                Res {
                    dom: self.inputs.clone(),
                    exact: false,
                }
            }
            Not | And | Or => match *d {
                Demand::Ints(_) => self.none(),
                Demand::Bool(w) if p == Not => {
                    self.back_at(&args[0], env, &Demand::Bool(!w), depth)
                }
                Demand::Bool(w) => {
                    let a = self.back_at(&args[0], env, d, depth);
                    let b = self.back_at(&args[1], env, d, depth);
                    if (p == And) == w {
                        return self.meet(a, b);
                    }
                    // `&&` and `||` here are strict: one side meeting the demand is enough
                    // only when the other cannot fail.
                    let strict = self.fwd(&args[0], env, depth).is_bool()
                        && self.fwd(&args[1], env, depth).is_bool();
                    let mut r = self.union(a, b);
                    r.exact &= strict;
                    r
                }
            },
            Lt | Le | Gt | Ge | Eq | Ne => match *d {
                Demand::Ints(_) => self.none(),
                Demand::Bool(w) => {
                    let p = if w { p } else { negate(p) };
                    self.back_compare(p, &args[0], &args[1], env, depth)
                }
            },
            Add | Sub | Mul | IntDiv | Mod | Neg | Abs | Pow => match ints_of(d) {
                Some(z) => self.back_arith(t, p, args, env, &z, depth),
                None => self.none(),
            },
            Min | Max => match ints_of(d) {
                Some(z) => self.back_arith(t, p, args, env, &z, depth),
                // `min` and `max` of two tests are tests.
                None => self.stop(StopKind::Outside, t),
            },
            _ => self.stop(StopKind::Outside, t),
        }
    }

    fn back_compare(&mut self, p: Prim, a: &Term, b: &Term, env: &Env, depth: u32) -> Res {
        let (fa, fb) = (self.fwd(a, env, depth), self.fwd(b, env, depth));
        // Two tests are equal where both are true or both false.
        if matches!(p, Prim::Eq | Prim::Ne) && fa.is_bool() && fb.is_bool() {
            let mut arms = Vec::new();
            for w in [true, false] {
                let ra = self.back_at(a, env, &Demand::Bool(w), depth);
                let rb = self.back_at(b, env, &Demand::Bool(w == (p == Prim::Eq)), depth);
                arms.push(self.meet(ra, rb));
            }
            let no = arms.pop().expect("two arms");
            let yes = arms.pop().expect("two arms");
            return self.union(yes, no);
        }
        // An operand that may fail meets an ordered comparison nowhere, since the comparison
        // fails too, and `==` with an integer nowhere; it meets `!=` everywhere.
        let ints = fa.is_int() && fb.is_int();
        let ordered_or_eq = |f: &Fwd| !f.other && !f.has_bools() && p != Prim::Ne;
        if let Some(c) = self.constant_int(b, env)
            && (ints || ordered_or_eq(&fa))
        {
            return self.back_at(a, env, &Demand::Ints(ray(p, c)), depth);
        }
        if let Some(c) = self.constant_int(a, env)
            && (ints || ordered_or_eq(&fb))
        {
            return self.back_at(b, env, &Demand::Ints(ray(mirror(p), c)), depth);
        }
        let one_int = fa.is_int() || fb.is_int();
        if ints || (ordered_or_eq(&fa) && ordered_or_eq(&fb) && (p != Prim::Eq || one_int)) {
            // Between two integers, `a op b` is `a - b op 0`.
            let diff = Term::Prim(Prim::Sub, vec![a.clone(), b.clone()]);
            return self.back_at(&diff, env, &Demand::Ints(ray(p, 0)), depth);
        }
        // Operands of other kinds, or two that may both fail, which `==` finds equal.
        self.scan(a, env, depth);
        self.scan(b, env, depth);
        let mut r = self.all();
        r.exact = false;
        r
    }

    /// Reports the stops in a term whose value the transfer does not follow.
    fn scan(&mut self, t: &Term, env: &Env, depth: u32) {
        if depth > CALL_DEPTH {
            self.stop(StopKind::Outside, t);
            return;
        }
        if self.mentions(t, env, 0) == Some(false) {
            return;
        }
        let d = depth + 1;
        match t {
            Term::Var(x) => {
                if let Some((bt, benv)) = lookup(env, x) {
                    self.scan(bt, &benv.clone(), d);
                }
            }
            Term::Let(n, e, b) => self.scan(b, &bind(env, n, e, env), d),
            Term::If(g, a, b) => {
                for u in [g, a, b] {
                    self.scan(u, env, d);
                }
            }
            Term::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    let inner = Cx::call_env(ps, args, lam, env);
                    self.scan(body, &inner, d);
                }
                Ok(Callee::Prim(p)) => self.scan(&Term::Prim(p, args.clone()), env, d),
                Err(Some(name)) => {
                    self.stop(StopKind::Foreign(name), t);
                }
                _ => {
                    self.stop(StopKind::Outside, t);
                }
            },
            Term::Prim(
                p @ (Prim::Show | Prim::Lower | Prim::Upper | Prim::Trim | Prim::Concat),
                _,
            ) => {
                self.stop(StopKind::String(*p), t);
            }
            Term::Prim(p, args) if scalar(*p) => {
                for a in args {
                    self.scan(a, env, d);
                }
            }
            _ => {
                self.stop(StopKind::Outside, t);
            }
        }
    }

    fn back_arith(
        &mut self,
        t: &Term,
        p: Prim,
        args: &[Term],
        env: &Env,
        z: &IntervalSet,
        depth: u32,
    ) -> Res {
        use Prim::*;
        let ints = |s: IntervalSet| Demand::Ints(s);
        if p == Mul
            && let Some((base, benv, k)) = self.power(t, env)
        {
            let benv = benv.clone();
            return self.back_unary(Op::Pow(k), base, &benv, z, depth);
        }
        match p {
            Neg | Abs => {
                return self.back_unary(op(p, None).expect("scalar"), &args[0], env, z, depth);
            }
            Pow => {
                return match self.constant_int(&args[1], env).map(u32::try_from) {
                    Some(Ok(k)) => self.back_unary(Op::Pow(k), &args[0], env, z, depth),
                    // A variable exponent: only the points where both operands are integers.
                    _ => self.both_ints(&args[0], &args[1], env, depth),
                };
            }
            _ => {}
        }
        let (a, b) = (&args[0], &args[1]);
        let ca = self.constant_int(a, env);
        let cb = self.constant_int(b, env);
        match (p, ca, cb) {
            (Add, Some(c), _) => self.back_at(b, env, &ints(shift(z, -(c as i128))), depth),
            (Add, _, Some(c)) | (Sub, _, Some(c)) => {
                let c = if p == Add { -(c as i128) } else { c as i128 };
                self.back_at(a, env, &ints(shift(z, c)), depth)
            }
            (Sub, Some(c), _) => {
                let r = revision::forward(Op::Sub, &IntervalSet::single(c), z);
                self.back_at(b, env, &ints(r), depth)
            }
            (Mul, Some(c), _) => self.back_at(b, env, &ints(times_pre(z, c)), depth),
            (Mul, _, Some(c)) => self.back_at(a, env, &ints(times_pre(z, c)), depth),
            (IntDiv, _, Some(c)) => self.back_at(a, env, &ints(div_pre(z, c)), depth),
            (Mod, _, Some(c)) => {
                let fa = self.fwd(a, env, depth).ints;
                match mod_pre(z, c, &fa) {
                    Some(s) => self.back_at(a, env, &ints(s), depth),
                    None => {
                        let mut r = self.back_at(a, env, &ints(fa), depth);
                        r.exact = false;
                        r
                    }
                }
            }
            (Min | Max, Some(c), _) => self.back_at(b, env, &ints(minmax_pre(p, z, c)), depth),
            (Min | Max, _, Some(c)) => self.back_at(a, env, &ints(minmax_pre(p, z, c)), depth),
            (Min | Max, None, None) => {
                let f = self.fwd(t, env, depth).ints;
                let zf = z.meet(&f);
                let (Some((flo, fhi)), Some((lo, hi))) = (f.bounds(), zf.bounds()) else {
                    return self.none();
                };
                let up = IntervalSet::range(lo, fhi).is_subset(z);
                let down = IntervalSet::range(flo, hi).is_subset(z);
                // min ≥ lo: both are; max ≤ hi: both are. The other rays: either is. When
                // the demand holds the whole forward range, both rays apply; the upward one is
                // taken.
                let both = (p == Min && up) || (p == Max && down && !up);
                let either = (p == Min && down && !up) || (p == Max && up);
                if both || either {
                    let r = if up {
                        IntervalSet::range(lo, PosInf)
                    } else {
                        IntervalSet::range(NegInf, hi)
                    };
                    let ra = self.back_at(a, env, &ints(r.clone()), depth);
                    let rb = self.back_at(b, env, &ints(r), depth);
                    return if both {
                        self.meet(ra, rb)
                    } else {
                        self.union(ra, rb)
                    };
                }
                self.project(p, a, b, env, z, depth)
            }
            _ => self.project(p, a, b, env, z, depth),
        }
    }

    /// `op(c)` in `z`, for an operator the revision table inverts exactly within the forward
    /// interval of `c`.
    fn back_unary(&mut self, o: Op, c: &Term, env: &Env, z: &IntervalSet, depth: u32) -> Res {
        if o == Op::Pow(0) {
            // `c ** 0` is 1 wherever `c` is an integer.
            return if z.contains(1) {
                self.back_at(c, env, &Demand::Ints(IntervalSet::top()), depth)
            } else {
                self.none()
            };
        }
        let fc = self.fwd(c, env, depth).ints;
        let zc = revision::backward(o, 0, &fc, &fc, z);
        self.back_at(c, env, &Demand::Ints(zc), depth)
    }

    /// The HC4 projection onto each operand: necessary, not exact.
    fn project(
        &mut self,
        p: Prim,
        a: &Term,
        b: &Term,
        env: &Env,
        z: &IntervalSet,
        depth: u32,
    ) -> Res {
        let o = op(p, None).expect("binary scalar operator");
        let fa = self.fwd(a, env, depth).ints;
        let fb = self.fwd(b, env, depth).ints;
        let za = revision::backward(o, 0, &fa, &fb, z);
        let zb = revision::backward(o, 1, &fa, &fb, z);
        let ra = self.back_at(a, env, &Demand::Ints(za), depth);
        let rb = self.back_at(b, env, &Demand::Ints(zb), depth);
        let mut r = self.meet(ra, rb);
        r.exact = is_empty(&r.dom);
        r
    }

    fn both_ints(&mut self, a: &Term, b: &Term, env: &Env, depth: u32) -> Res {
        let top = Demand::Ints(IntervalSet::top());
        let ra = self.back_at(a, env, &top, depth);
        let rb = self.back_at(b, env, &top, depth);
        let mut r = self.meet(ra, rb);
        r.exact = is_empty(&r.dom);
        r
    }
}

/// Whether the scalar catalog has an entry for the primitive, or reads through it (`len`).
fn scalar(p: Prim) -> bool {
    use Prim::*;
    matches!(
        p,
        Add | Sub
            | Mul
            | IntDiv
            | Mod
            | Neg
            | Abs
            | Pow
            | Min
            | Max
            | Lt
            | Le
            | Gt
            | Ge
            | Eq
            | Ne
            | Not
            | And
            | Or
            | Len
    )
}

/// Forward transfer of a comparison over two integer sets.
fn compare(p: Prim, a: &IntervalSet, b: &IntervalSet) -> Fwd {
    let (Some((alo, ahi)), Some((blo, bhi))) = (a.bounds(), b.bounds()) else {
        return Fwd::bools(false, false);
    };
    let one = |x: &IntervalSet| x.bounds().filter(|(l, h)| l == h);
    let (t, f) = match p {
        Prim::Lt => (alo < bhi, ahi >= blo),
        Prim::Le => (alo <= bhi, ahi > blo),
        Prim::Gt => (ahi > blo, alo <= bhi),
        Prim::Ge => (ahi >= blo, alo < bhi),
        _ => {
            let eq = !a.meet(b).is_empty();
            let ne = !(one(a).is_some() && one(a) == one(b));
            if p == Prim::Eq { (eq, ne) } else { (ne, eq) }
        }
    };
    Fwd::bools(t, f)
}

/// The comparison that holds exactly when `p` is false, between two integers.
fn negate(p: Prim) -> Prim {
    match p {
        Prim::Lt => Prim::Ge,
        Prim::Le => Prim::Gt,
        Prim::Gt => Prim::Le,
        Prim::Ge => Prim::Lt,
        Prim::Eq => Prim::Ne,
        _ => Prim::Eq,
    }
}

/// The comparison `p` with its operands swapped.
fn mirror(p: Prim) -> Prim {
    match p {
        Prim::Lt => Prim::Gt,
        Prim::Le => Prim::Ge,
        Prim::Gt => Prim::Lt,
        Prim::Ge => Prim::Le,
        p => p,
    }
}

/// The integers `x` with `x p c`.
fn ray(p: Prim, c: i64) -> IntervalSet {
    let c = c as i128;
    let e = End::from_i128;
    match p {
        Prim::Lt => IntervalSet::range(NegInf, e(c - 1)),
        Prim::Le => IntervalSet::range(NegInf, e(c)),
        Prim::Gt => IntervalSet::range(e(c + 1), PosInf),
        Prim::Ge => IntervalSet::range(e(c), PosInf),
        Prim::Eq => IntervalSet::range(e(c), e(c)),
        _ => IntervalSet::single(c as i64).complement_in(&IntervalSet::top()),
    }
}

/// Each piece of `z` moved up by `c`.
fn shift(z: &IntervalSet, c: i128) -> IntervalSet {
    let m = |e: End| match e {
        Fin(v) => End::from_i128(v as i128 + c),
        e => e,
    };
    IntervalSet::from_pieces(z.pieces().iter().map(|&(lo, hi)| (m(lo), m(hi))).collect())
}

/// The integers `x` with `x * c` in `z`.
fn times_pre(z: &IntervalSet, c: i64) -> IntervalSet {
    if c == 0 {
        return if z.contains(0) {
            IntervalSet::top()
        } else {
            IntervalSet::empty()
        };
    }
    let c = c as i128;
    // ceil and floor of v / c, at an endpoint.
    let q = |e: End, up: bool| match e {
        Fin(v) => {
            let (v, d) = if c < 0 {
                (-(v as i128), -c)
            } else {
                (v as i128, c)
            };
            let f = v.div_euclid(d);
            End::from_i128(if up && f * d != v { f + 1 } else { f })
        }
        e if c < 0 => -e,
        e => e,
    };
    IntervalSet::from_pieces(
        z.pieces()
            .iter()
            .map(|&(lo, hi)| {
                if c > 0 {
                    (q(lo, true), q(hi, false))
                } else {
                    (q(hi, true), q(lo, false))
                }
            })
            .collect(),
    )
}

/// The integers `x` with `x div c` in `z`, Euclidean: `x = q * c + r` with `r` in
/// `0..abs(c)`.
fn div_pre(z: &IntervalSet, c: i64) -> IntervalSet {
    if c == 0 {
        return IntervalSet::empty();
    }
    let (c, m) = (c as i128, (c as i128).abs());
    let at = |e: End, add: i128| match e {
        Fin(q) => End::from_i128(q as i128 * c + add),
        e if c < 0 => -e,
        e => e,
    };
    IntervalSet::from_pieces(
        z.pieces()
            .iter()
            .map(|&(lo, hi)| {
                if c > 0 {
                    (at(lo, 0), at(hi, m - 1))
                } else {
                    (at(hi, 0), at(lo, m - 1))
                }
            })
            .collect(),
    )
}

/// The members of `within` with `x mod c` in `z`, Euclidean, or `None` when that set has more
/// than [`PIECE_LIMIT`] pieces or `within` is unbounded and the remainders demanded are not
/// all of them.
fn mod_pre(z: &IntervalSet, c: i64, within: &IntervalSet) -> Option<IntervalSet> {
    if c == 0 {
        return Some(IntervalSet::empty());
    }
    let m = c.unsigned_abs() as i128;
    let rem = z.meet(&IntervalSet::range(Fin(0), End::from_i128(m - 1)));
    if rem.is_empty() {
        return Some(IntervalSet::empty());
    }
    if rem == IntervalSet::range(Fin(0), End::from_i128(m - 1)) {
        return Some(within.clone());
    }
    let (Fin(lo), Fin(hi)) = within.bounds()? else {
        return None;
    };
    let (k0, k1) = ((lo as i128).div_euclid(m), (hi as i128).div_euclid(m));
    if (k1 - k0 + 1) * rem.pieces().len() as i128 > 2 * PIECE_LIMIT as i128 + 2 {
        return None;
    }
    let mut pieces = Vec::new();
    for k in k0..=k1 {
        for &(a, b) in rem.pieces() {
            if let (Fin(a), Fin(b)) = (a, b) {
                pieces.push((
                    End::from_i128(k * m + a as i128),
                    End::from_i128(k * m + b as i128),
                ));
            }
        }
    }
    let s = IntervalSet::from_pieces(pieces).meet(within);
    (s.pieces().len() <= PIECE_LIMIT).then_some(s)
}

/// The integers `x` with `min(x, c)` (or `max`) in `z`.
fn minmax_pre(p: Prim, z: &IntervalSet, c: i64) -> IntervalSet {
    let at_c = if p == Prim::Min {
        IntervalSet::range(Fin(c), PosInf)
    } else {
        IntervalSet::range(NegInf, Fin(c))
    };
    let below = if p == Prim::Min {
        IntervalSet::range(NegInf, Fin(c))
    } else {
        IntervalSet::range(Fin(c), PosInf)
    };
    let own = z.meet(&below);
    if z.contains(c) { own.join(&at_c) } else { own }
}

/// The projection of the points of a finite box, within the enumeration budget, at which the
/// term meets the demand.
fn enumerate(term: &Term, dom: &Domains, demand: &Demand) -> Option<Res> {
    let mut axes: Vec<(Arc<str>, Vec<i64>)> = Vec::new();
    let mut size: u64 = 1;
    for (k, s) in dom {
        let mut n: u128 = 0;
        for &(lo, hi) in s.pieces() {
            let (Fin(lo), Fin(hi)) = (lo, hi) else {
                return None;
            };
            n += (hi as i128 - lo as i128 + 1) as u128;
        }
        size = (size as u128 * n)
            .try_into()
            .ok()
            .filter(|&n| n <= ENUMERATION_BUDGET)?;
        let vs = s.pieces().iter().flat_map(|&(lo, hi)| match (lo, hi) {
            (Fin(lo), Fin(hi)) => lo..=hi,
            _ => unreachable!("every piece is finite"),
        });
        axes.push((k.clone(), vs.collect()));
    }
    let mut met: Vec<Vec<i64>> = vec![Vec::new(); axes.len()];
    let mut count: u64 = 0;
    let mut point = vec![0usize; axes.len()];
    if axes.iter().any(|(_, vs)| vs.is_empty()) {
        return Some(Res {
            dom: dom.clone(),
            exact: true,
        });
    }
    loop {
        let mut t = term.clone();
        for ((k, vs), &i) in axes.iter().zip(&point).rev() {
            t = Term::Let(
                k.clone(),
                Arc::new(Term::Lit(Value::Int(vs[i]))),
                Arc::new(t),
            );
        }
        if demand.holds(&eval(&t).ok()?) {
            count += 1;
            for (j, &i) in point.iter().enumerate() {
                met[j].push(axes[j].1[i]);
            }
        }
        // The next point, the last axis fastest.
        let mut j = axes.len();
        loop {
            if j == 0 {
                let dom: Domains = axes
                    .iter()
                    .zip(&met)
                    .map(|((k, _), vs)| {
                        (
                            k.clone(),
                            IntervalSet::from_pieces(
                                vs.iter().map(|&v| (Fin(v), Fin(v))).collect(),
                            ),
                        )
                    })
                    .collect();
                let product: u64 = met
                    .iter()
                    .map(|vs| {
                        let mut vs = vs.clone();
                        vs.sort();
                        vs.dedup();
                        vs.len() as u64
                    })
                    .product();
                return Some(Res {
                    exact: product == count,
                    dom,
                });
            }
            j -= 1;
            point[j] += 1;
            if point[j] < axes[j].1.len() {
                break;
            }
            point[j] = 0;
        }
    }
}
