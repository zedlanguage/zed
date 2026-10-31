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
//!   invert exactly, `mod` within the operand's forward interval, its first and last periods
//!   exactly and the periods between them as one piece;
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

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::budgets::{ENUMERATION_BUDGET, ENUMERATION_FUEL};
use zed_kernel::{Evaluator, Prim, Stack, Term, Value, World, eval, on_stack};

use super::interval::{End, IntervalSet};
use super::presburger::{self, Con, Formula, Lin, Over, Relation};
use super::revision::{self, Op, Tonicity};
use End::{Fin, NegInf, PosInf};

/// An interval per input name.
pub type Domains = BTreeMap<Arc<str>, IntervalSet>;

/// What the term's value must be.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
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
    /// The transfer visited [`TRANSFER_FUEL`] terms of one preimage.
    Budget,
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
            StopKind::Budget => write!(
                f,
                "the transfer's budget of {TRANSFER_FUEL} visited terms stops it at "
            )?,
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

/// The most terms the transfer computes for one preimage, each pair of a term and a scope
/// once; past it the transfer stops, as at [`CALL_DEPTH`].
pub const TRANSFER_FUEL: u32 = 100_000;

/// The most factors read as one power: an integer power past 64 of anything but -1, 0 and 1
/// leaves `i64`.
const POWER_FACTORS: usize = 64;

/// The preimage of `demand` under `term`, whose free names in `inputs` range over their
/// domains.
pub fn preimage(term: &Term, inputs: &Domains, demand: &Demand) -> Preimage {
    // One evaluation thread serves every evaluation of the transfer.
    on_stack(|_| preimage_in(term, inputs, demand))
}

fn preimage_in(term: &Term, inputs: &Domains, demand: &Demand) -> Preimage {
    let root = Rc::new(Scope::Empty);
    let cx = Cx::new(inputs);
    let mut r = cx.back(term, &root, demand);
    let mut stops = cx.stops.take();
    let mut enumerated = false;
    if !r.exact && !is_empty(&r.dom) {
        let over = Cx::new(&r.dom);
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
        // An auxiliary variable belongs to the relation of the term that made it.
        cx.memo.lin.borrow_mut().clear();
        cx.memo.formula.borrow_mut().clear();
        cx.memo.log.borrow_mut().clear();
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
        let mut mentioned = rel.body.atoms();
        for (_, _, f) in &rel.defs {
            mentioned.extend(f.atoms());
        }
        let syms: Vec<presburger::Atom> = dom
            .keys()
            .map(|k| presburger::Atom::Sym(k.clone()))
            .filter(|a| mentioned.contains(a))
            .collect();
        let mut each = presburger::project_each(&whole, &syms)?.into_iter();
        let mut out = Domains::new();
        for (k, v) in dom {
            let p = if mentioned.contains(&presburger::Atom::Sym(k.clone())) {
                each.next()
                    .expect("one projection for each mentioned input")?
                    .meet(v)
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
        let outside = Formula::and(vec![
            rel.defined(),
            within(&out)?,
            Formula::negate(rel.body.clone()),
        ]);
        let exact = presburger::satisfiable(&outside)?.is_none();
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

    /// Whether `k` more auxiliary variables stay within the atoms a relation takes; past
    /// them every relation is over the budget of step M0.5.
    fn room(&self, k: usize) -> bool {
        self.defs.len() + k <= presburger::VARIABLES
    }
}

/// A formula within the constraints a relation takes; past them it is over the budget of
/// step M0.5.
fn small(f: Formula) -> Option<Formula> {
    (f.cons().len() <= presburger::ATOMS).then_some(f)
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
#[derive(Clone)]
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

/// A pair of a term and the scope it is read in, by address.
type Key = (usize, usize);

fn key(t: &Term, env: &Env) -> Key {
    (t as *const Term as usize, Rc::as_ptr(env) as usize)
}

/// What the transfer has computed, for each pair of a term and a scope, so that a name bound
/// once is followed once however often it is read (the rule of low complexity, Part G). Every
/// scope and term the transfer makes is kept here for the life of the context, so that no
/// address in a key is used again.
#[derive(Default)]
struct Memo {
    /// The scopes of `let` bodies, call bodies and lambda bodies, by the term that makes them.
    envs: RefCell<HashMap<Key, Env>>,
    /// The primitive applications that calls of prelude words stand for.
    calls: RefCell<HashMap<Key, Rc<Term>>>,
    /// The differences that comparisons of two terms stand for, by the two terms.
    diffs: RefCell<HashMap<Key, Rc<Term>>>,
    mentions: RefCell<HashMap<Key, Option<bool>>>,
    constant: RefCell<HashMap<Key, Option<Value>>>,
    fwd: RefCell<HashMap<Key, Fwd>>,
    back: RefCell<HashMap<(Key, Demand), Res>>,
    scan: RefCell<HashSet<Key>>,
    lin: RefCell<HashMap<Key, Option<Lin>>>,
    formula: RefCell<HashMap<Key, Option<Formula>>>,
    /// The `lin` (false) and `formula` (true) entries in the order they were made, which a
    /// translation that is undone removes.
    log: RefCell<Vec<(bool, Key)>>,
}

struct Cx<'a> {
    inputs: &'a Domains,
    stops: RefCell<Vec<Stop>>,
    seen: RefCell<HashSet<String>>,
    /// Terms left to compute before [`TRANSFER_FUEL`] stops the transfer.
    fuel: Cell<u32>,
    /// Whether the result being computed was cut short by the depth limit or the budget; such
    /// a result is not remembered, since it depends on where it was reached.
    cut: Cell<bool>,
    memo: Memo,
}

impl<'a> Cx<'a> {
    fn new(inputs: &'a Domains) -> Self {
        Cx {
            inputs,
            stops: RefCell::new(Vec::new()),
            seen: RefCell::new(HashSet::new()),
            fuel: Cell::new(TRANSFER_FUEL),
            cut: Cell::new(false),
            memo: Memo::default(),
        }
    }

    /// Why the transfer stops at this depth, if it does; otherwise one term is counted.
    fn spent(&self, depth: u32) -> Option<StopKind> {
        let why = if depth > CALL_DEPTH {
            StopKind::Outside
        } else if self.fuel.get() == 0 {
            StopKind::Budget
        } else {
            self.fuel.set(self.fuel.get() - 1);
            return None;
        };
        self.cut.set(true);
        Some(why)
    }

    /// `f()`, remembered under `k` in `map` unless the depth limit or the budget cut it short.
    fn cached<K: Hash + Eq, V: Clone>(
        &self,
        map: &RefCell<HashMap<K, V>>,
        k: K,
        f: impl FnOnce() -> V,
    ) -> V {
        if let Some(v) = map.borrow().get(&k) {
            return v.clone();
        }
        let outer = self.cut.replace(false);
        let v = f();
        let cut = self.cut.get();
        if !cut {
            map.borrow_mut().insert(k, v.clone());
        }
        self.cut.set(outer || cut);
        v
    }

    /// [`Cx::cached`] for the translation into the linear-relation domain, whose entries a
    /// translation that is undone removes.
    fn translated<V: Clone>(
        &self,
        formula: bool,
        map: &RefCell<HashMap<Key, V>>,
        k: Key,
        f: impl FnOnce() -> V,
    ) -> V {
        let known = map.borrow().contains_key(&k);
        let v = self.cached(map, k, f);
        if !known && map.borrow().contains_key(&k) {
            self.memo.log.borrow_mut().push((formula, k));
        }
        v
    }

    /// Removes the translation's entries made after the first `mark`.
    fn forget(&self, mark: usize) {
        let undone: Vec<(bool, Key)> = self.memo.log.borrow_mut().drain(mark..).collect();
        for (formula, k) in undone {
            if formula {
                self.memo.formula.borrow_mut().remove(&k);
            } else {
                self.memo.lin.borrow_mut().remove(&k);
            }
        }
    }

    /// The scope of a `let` body, made once for each `let` and scope.
    fn let_env(&self, t: &Term, n: &Arc<str>, e: &Term, env: &Env) -> Env {
        self.memo
            .envs
            .borrow_mut()
            .entry(key(t, env))
            .or_insert_with(|| bind(env, n, e, env))
            .clone()
    }

    /// The primitive application a call `t` of a prelude word stands for.
    fn call_prim(&self, t: &Term, env: &Env, p: Prim, args: &[Term]) -> Rc<Term> {
        self.memo
            .calls
            .borrow_mut()
            .entry(key(t, env))
            .or_insert_with(|| Rc::new(Term::Prim(p, args.to_vec())))
            .clone()
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

    fn stop(&self, kind: StopKind, t: &Term) -> Res {
        let s = Stop {
            kind,
            term: t.to_string(),
        };
        if self.seen.borrow_mut().insert(s.to_string()) {
            self.stops.borrow_mut().push(s);
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
        self.cached(&self.memo.mentions, key(t, env), || {
            self.mentions_at(t, env, depth)
        })
    }

    fn mentions_at(&self, t: &Term, env: &Env, depth: u32) -> Option<bool> {
        if self.spent(depth).is_some() {
            return None;
        }
        let any = |cx: &Self, ts: &mut dyn Iterator<Item = (&Term, Env)>| -> Option<bool> {
            let mut m = false;
            for (t, e) in ts {
                m |= cx.mentions(t, &e, depth)?;
            }
            Some(m)
        };
        match t {
            Term::Lit(_) | Term::PrimFn(_) => Some(false),
            Term::Var(x) => match lookup(env, x) {
                Some((bt, benv)) => self.mentions(bt, benv, depth),
                None => Some(self.inputs.contains_key(x)),
            },
            Term::Let(n, e, b) => {
                let inner = self.let_env(t, n, e, env);
                any(self, &mut [(&**e, env.clone()), (&**b, inner)].into_iter())
            }
            Term::Lam(ps, b) => {
                // A parameter is not an input, even where it shadows one.
                let inner = self
                    .memo
                    .envs
                    .borrow_mut()
                    .entry(key(t, env))
                    .or_insert_with(|| {
                        let mut inner = env.clone();
                        for p in ps {
                            inner = bind(&inner, p, &Term::Lit(Value::Bool(false)), &inner);
                        }
                        inner
                    })
                    .clone();
                self.mentions(b, &inner, depth)
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
    fn close(&self, t: &Term, env: &Env, depth: u32) -> Option<Term> {
        if self.spent(depth).is_some() {
            return None;
        }
        let c = |t: &Term, e: &Env| self.close(t, e, depth);
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
        self.cached(&self.memo.constant, key(t, env), || {
            if self.mentions(t, env, 0)? || self.spent(0).is_some() {
                return None;
            }
            // From the values of the parts where the catalog reads them, so that a part is
            // run once; otherwise the closed term.
            match t {
                Term::Lit(v) => Some(v.clone()),
                Term::Var(x) if let Some((bt, benv)) = lookup(env, x) => {
                    self.constant(bt, &benv.clone())
                }
                Term::Let(n, e, b) => self.constant(b, &self.let_env(t, n, e, env)),
                Term::Prim(p, args) => {
                    let vs = args
                        .iter()
                        .map(|a| self.constant(a, env).map(Term::Lit))
                        .collect::<Option<_>>()?;
                    eval(&Term::Prim(*p, vs)).ok()
                }
                Term::If(g, a, b) => match self.constant(g, env)? {
                    Value::Bool(true) => self.constant(a, env),
                    Value::Bool(false) => self.constant(b, env),
                    _ => eval(&self.close(t, env, 0)?).ok(),
                },
                _ => eval(&self.close(t, env, 0)?).ok(),
            }
        })
    }

    fn constant_int(&self, t: &Term, env: &Env) -> Option<i64> {
        match self.constant(t, env)? {
            Value::Int(n) => Some(n),
            _ => None,
        }
    }

    /// The function a call reaches, with the scope its body is read in. Each name is looked
    /// up in the scope its binding was made in, which was built before that binding, so the
    /// walk ends.
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
    fn call_env(&self, t: &Term, ps: &[Arc<str>], args: &[Term], lam: &Env, caller: &Env) -> Env {
        self.memo
            .envs
            .borrow_mut()
            .entry(key(t, caller))
            .or_insert_with(|| {
                let mut e = lam.clone();
                for (p, a) in ps.iter().zip(args) {
                    e = bind(&e, p, a, caller);
                }
                e
            })
            .clone()
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
                _ if out.len() > POWER_FACTORS => {}
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
        (fs.len() >= 2 && fs.len() <= POWER_FACTORS && fs.iter().all(one)).then_some((
            first,
            fenv,
            fs.len() as u32,
        ))
    }

    // ---- Into the linear-relation domain ------------------------------------------------

    /// The linear term an integer term states over the inputs.
    fn lin(&self, tr: &mut Tr, t: &Term, env: &Env, depth: u32) -> Option<Lin> {
        self.translated(false, &self.memo.lin, key(t, env), || {
            self.lin_at(tr, t, env, depth)
        })
    }

    fn lin_at(&self, tr: &mut Tr, t: &Term, env: &Env, depth: u32) -> Option<Lin> {
        use Prim::*;
        if self.spent(depth).is_some() {
            return None;
        }
        let d = depth;
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
            Term::Let(n, e, b) => self.lin(tr, b, &self.let_env(t, n, e, env), d),
            Term::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    let inner = self.call_env(t, ps, args, lam, env);
                    self.lin(tr, body, &inner, d + 1)
                }
                Callee::Prim(p) => self.lin(tr, &self.call_prim(t, env, p, args), env, d),
                Callee::Lam(..) => None,
            },
            Term::If(g, a, b) => {
                let g = self.formula(tr, g, env, d)?;
                let (la, lb) = (self.lin(tr, a, env, d)?, self.lin(tr, b, env, d)?);
                if !tr.room(1) {
                    return None;
                }
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
                        if !tr.room(2) {
                            return None;
                        }
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
                        if !tr.room(1) {
                            return None;
                        }
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
        self.translated(true, &self.memo.formula, key(t, env), || {
            self.formula_at(tr, t, env, depth).and_then(small)
        })
    }

    fn formula_at(&self, tr: &mut Tr, t: &Term, env: &Env, depth: u32) -> Option<Formula> {
        use Prim::*;
        if self.spent(depth).is_some() {
            return None;
        }
        let d = depth;
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
            Term::Let(n, e, b) => self.formula(tr, b, &self.let_env(t, n, e, env), d),
            Term::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    let inner = self.call_env(t, ps, args, lam, env);
                    self.formula(tr, body, &inner, d + 1)
                }
                Callee::Prim(p) => self.formula(tr, &self.call_prim(t, env, p, args), env, d),
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
                    let (mark, logged) = (tr.defs.len(), self.memo.log.borrow().len());
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
                    self.forget(logged);
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

    fn fwd(&self, t: &Term, env: &Env, depth: u32) -> Fwd {
        self.cached(&self.memo.fwd, key(t, env), || self.fwd_at(t, env, depth))
    }

    fn fwd_at(&self, t: &Term, env: &Env, depth: u32) -> Fwd {
        if let Some(why) = self.spent(depth) {
            self.stop(why, t);
            return Fwd::top();
        }
        let d = depth;
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
            Term::Let(n, e, b) => self.fwd(b, &self.let_env(t, n, e, env), d),
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
                    let inner = self.call_env(t, ps, args, lam, env);
                    self.fwd(body, &inner, d + 1)
                }
                Ok(Callee::Prim(p)) => self.fwd(&self.call_prim(t, env, p, args), env, d),
                _ => Fwd::top(),
            },
            Term::Prim(p, args) => self.fwd_prim(t, *p, args, env, d),
            _ => Fwd::top(),
        }
    }

    fn fwd_prim(&self, t: &Term, p: Prim, args: &[Term], env: &Env, d: u32) -> Fwd {
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

    fn back(&self, t: &Term, env: &Env, d: &Demand) -> Res {
        self.back_at(t, env, d, 0)
    }

    fn back_at(&self, t: &Term, env: &Env, d: &Demand, depth: u32) -> Res {
        self.cached(&self.memo.back, (key(t, env), d.clone()), || {
            self.back_in(t, env, d, depth)
        })
    }

    fn back_in(&self, t: &Term, env: &Env, d: &Demand, depth: u32) -> Res {
        if let Some(why) = self.spent(depth) {
            return self.stop(why, t);
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
        let next = depth;
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
            Term::Let(n, e, b) => self.back_at(b, &self.let_env(t, n, e, env), d, next),
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
                    let inner = self.call_env(t, ps, args, lam, env);
                    self.back_at(body, &inner, d, next + 1)
                }
                Ok(Callee::Prim(p)) => self.back_at(&self.call_prim(t, env, p, args), env, d, next),
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
        &self,
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

    fn back_compare(&self, p: Prim, a: &Term, b: &Term, env: &Env, depth: u32) -> Res {
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
            let diff = self
                .memo
                .diffs
                .borrow_mut()
                .entry((a as *const Term as usize, b as *const Term as usize))
                .or_insert_with(|| Rc::new(Term::Prim(Prim::Sub, vec![a.clone(), b.clone()])))
                .clone();
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
    fn scan(&self, t: &Term, env: &Env, depth: u32) {
        // A term is scanned once in each scope: its stops are reported the first time.
        if !self.memo.scan.borrow_mut().insert(key(t, env)) {
            return;
        }
        if let Some(why) = self.spent(depth) {
            self.stop(why, t);
            return;
        }
        if self.mentions(t, env, 0) == Some(false) {
            return;
        }
        let d = depth;
        match t {
            Term::Var(x) => {
                if let Some((bt, benv)) = lookup(env, x) {
                    self.scan(bt, &benv.clone(), d);
                }
            }
            Term::Let(n, e, b) => self.scan(b, &self.let_env(t, n, e, env), d),
            Term::If(g, a, b) => {
                for u in [g, a, b] {
                    self.scan(u, env, d);
                }
            }
            Term::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    let inner = self.call_env(t, ps, args, lam, env);
                    self.scan(body, &inner, d + 1);
                }
                Ok(Callee::Prim(p)) => self.scan(&self.call_prim(t, env, p, args), env, d),
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
        &self,
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
                let (s, exact) = mod_pre(z, c, &fa);
                let mut r = self.back_at(a, env, &ints(s), depth);
                r.exact &= exact;
                r
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
    fn back_unary(&self, o: Op, c: &Term, env: &Env, z: &IntervalSet, depth: u32) -> Res {
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
    fn project(&self, p: Prim, a: &Term, b: &Term, env: &Env, z: &IntervalSet, depth: u32) -> Res {
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

    fn both_ints(&self, a: &Term, b: &Term, env: &Env, depth: u32) -> Res {
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

/// The members of `within` with `x mod c` in `z`, Euclidean, and whether that is all of them
/// and no more. The first and last periods `within` meets are listed exactly and the periods
/// between them are one piece, so the set has at most `2 * p + 1` pieces for `p` pieces of
/// remainders, and it is exact when there is no period between them. An unbounded `within`
/// is kept whole unless every remainder is demanded.
fn mod_pre(z: &IntervalSet, c: i64, within: &IntervalSet) -> (IntervalSet, bool) {
    if c == 0 {
        return (IntervalSet::empty(), true);
    }
    let m = c.unsigned_abs() as i128;
    let rem = z.meet(&IntervalSet::range(Fin(0), End::from_i128(m - 1)));
    if rem.is_empty() {
        return (IntervalSet::empty(), true);
    }
    if rem == IntervalSet::range(Fin(0), End::from_i128(m - 1)) {
        return (within.clone(), true);
    }
    let Some((Fin(lo), Fin(hi))) = within.bounds() else {
        return (within.clone(), false);
    };
    let (k0, k1) = ((lo as i128).div_euclid(m), (hi as i128).div_euclid(m));
    let period = |k: i128| {
        rem.pieces()
            .iter()
            .filter_map(|&(a, b)| match (a, b) {
                (Fin(a), Fin(b)) => Some((
                    End::from_i128(k * m + a as i128),
                    End::from_i128(k * m + b as i128),
                )),
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    let mut pieces = period(k0);
    if k1 > k0 + 1 {
        let Some((Fin(a), Fin(b))) = rem.bounds() else {
            unreachable!("the remainders lie in 0..m")
        };
        pieces.push((
            End::from_i128((k0 + 1) * m + a as i128),
            End::from_i128((k1 - 1) * m + b as i128),
        ));
    }
    if k1 > k0 {
        pieces.extend(period(k1));
    }
    let s = IntervalSet::from_pieces(pieces).meet(within);
    (s, k1 <= k0 + 1)
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
    if axes.iter().any(|(_, vs)| vs.is_empty()) {
        return Some(Res {
            dom: dom.clone(),
            exact: true,
        });
    }
    on_stack(|stack| enumerate_on(stack, term, &axes, demand))
}

/// The enumeration of [`enumerate`] over `axes`, each point evaluated on `stack` within
/// [`ENUMERATION_FUEL`].
fn enumerate_on(
    stack: &Stack,
    term: &Term,
    axes: &[(Arc<str>, Vec<i64>)],
    demand: &Demand,
) -> Option<Res> {
    let mut met: Vec<Vec<i64>> = vec![Vec::new(); axes.len()];
    let mut count: u64 = 0;
    let mut point = vec![0usize; axes.len()];
    loop {
        let mut t = term.clone();
        for ((k, vs), &i) in axes.iter().zip(&point).rev() {
            t = Term::Let(
                k.clone(),
                Arc::new(Term::Lit(Value::Int(vs[i]))),
                Arc::new(t),
            );
        }
        let v = Evaluator::new(World::new())
            .with_fuel(ENUMERATION_FUEL)
            .run_on(stack, &t)
            .ok()?;
        if demand.holds(&v) {
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
