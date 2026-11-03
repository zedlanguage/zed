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
//! - a `let` is read through, as the evaluator reads it; a call to a lambda is read through
//!   once for each argument abstraction: each argument that reads an input and is an integer
//!   is a parameter over its forward interval with its ends moved out to the landmarks (the
//!   term's literals and the domains' ends, each with its neighbors), and the call's preimage
//!   is the summary's box over the inputs met with each argument's preimage of the box over its
//!   parameter; a call whose arguments are not of that kind is read through in place; and a
//!   call of a lambda already being read stops the transfer, so the calls followed nest no
//!   deeper than the number of lambdas;
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
//! result that is still not exact over a listed box (every piece of every input's set holding
//! no more members than its endpoints, at most one input with more than one member), of a term whose form shows that it ends, is
//! enumerated: the term is run at each point, and the result is the projection of the points
//! that meet the demand, exact when they form a box. An enumeration that meets a term the
//! evaluator cannot run removes nothing.
//!
//! Under `@exact` ([`exact_preimage`]) a result still not exact over a bounded box is found by
//! branch and prune (docs/thresholds.md, "`@exact`"): each sub-box is narrowed by the steps
//! above, and dropped when nothing in it meets the demand, kept whole when every point does,
//! and otherwise halved on its widest input; a single point is evaluated. A sub-box whose
//! values on every input are already known to meet the demand at some point is skipped, since
//! only each input's projection is sought. A scope under `@exact` does not list the projection,
//! which can have as many pieces as the box has points; it asks [`witness`] for one point
//! that meets the demand, and the same search stops at the first.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::{Evaluator, Prim, Term, Value, World, eval, on_stack};

use super::int::Int;
use super::interval::{self, End, IntervalSet};
use super::lattice::{Congruence, Landmarks, Lattice};
use super::presburger::{self, Con, Formula, Lin, Refusal, Relation};
use super::revision::{self, Op, Tonicity, reduce_congruence};
use crate::stage;
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
    /// A term the scalar catalog does not cover: families, folds, `fix`, patterns or ports.
    ///
    /// Complexity tradeoff: for `fix`, `gen` and `fold` (the other terms here are catalog
    /// entries not yet written, with no cost reason), the transfer stops at the loop, which
    /// it raises at the `_` arms of `back_in`, `back_prim` and `scan`; the term's answer is
    /// the whole box (`Res::unknown`, necessary only), and the stop is reported. Why: reading
    /// through a loop unfolds it once per iteration it may take, which need not end, as for
    /// `StopKind::Recursion`; a fixpoint over the loop is the full analysis this transfer
    /// avoids. Trigger: a `fix`, `gen` or `fold` term between the demand and an input. Test:
    /// `l01_25_preimage_catalog::stops::a_term_outside_the_scalar_catalog_is_reported`
    /// covers the stop through `sum` of a tuple; in the same module,
    /// `a_fold_between_the_demand_and_an_input_stops_the_transfer` stops at a `fold` and
    /// `a_fix_between_the_demand_and_an_input_stops_the_transfer` at a `fix`, both at the `_`
    /// arm of `back_in`, and `a_gen_between_the_demand_and_an_input_stops_the_transfer` at a
    /// `gen`, at the `_` arm of `scan`.
    /// COMPLEXITY.md row C15. A complete solution would compute a fixpoint of the loop's
    /// backward transfer with widening, as the forward iteration does for loops.
    Outside,
    /// A call of a lambda whose call is already being read.
    Recursion,
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
            StopKind::Recursion => write!(f, "a call of a function already being read at ")?,
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
    /// Why the linear-relation domain left the demand undecided, when it did and the box is
    /// not exact.
    pub refusal: Option<Refusal>,
}

/// The value of the closed term `t`, if its form shows that it ends ([`stage::ends`]) and it
/// evaluates. A term not shown to end stays unevaluated, since a program may loop forever.
fn run_closed(t: &Term) -> Option<Value> {
    if !stage::ends(t) {
        return None;
    }
    eval(t).ok()
}

/// The most factors read as one power: an integer power past 64 of anything but -1, 0 and 1
/// leaves `i64`.
///
/// Complexity tradeoff: a product of more than 64 equal factors is not read as a power, so it
/// is read as nested products (the HC4 entry for `*`), wider than the power's exact inverse. Why
/// given: the power would leave `i64`; that reason does not hold, since `Int` is unbounded
/// and `x ** k` inverts by a k-th root at a cost in the bits of its bounds. Trigger: more than
/// 64 equal factors. Test:
/// `l01_25_preimage_catalog::scopes::equal_factors_written_twice_are_read_as_a_square`
/// (below the constant only). COMPLEXITY.md row C19. This switches behavior at a constant
/// size, so it violates the no-thresholds rule; to be replaced (ledger item CAP-power). A
/// complete solution would read any count of equal factors as a power, with ends held as
/// unbounded integers.
const POWER_FACTORS: usize = 64;

/// The preimage of `demand` under `term`, whose free names in `inputs` range over their
/// domains.
pub fn preimage(term: &Term, inputs: &Domains, demand: &Demand) -> Preimage {
    on_stack(|| preimage_of(term, inputs, demand))
}

/// [`preimage`] on the caller's stack.
fn preimage_of(term: &Term, inputs: &Domains, demand: &Demand) -> Preimage {
    let mut tx = Tx::new();
    let root = tx.terms.add(term);
    preimage_in(&mut tx, root, term, inputs, demand)
}

/// [`preimage`] of `term`, which is `root` in `tx`'s terms.
fn preimage_in(
    tx: &mut Tx<'_>,
    root: Tid,
    term: &Term,
    inputs: &Domains,
    demand: &Demand,
) -> Preimage {
    let marks = tx.landmarks(inputs, demand);
    tx.start(inputs, marks.clone());
    interval::rounded();
    let r = tx.back(root, ROOT, demand);
    let mut r = Whole {
        dom: tx.whole(&r),
        // An exact backward transfer through a rounded end may keep points that fail.
        exact: r.exact && !interval::rounded(),
    };
    let mut stops = std::mem::take(&mut tx.run.stops);
    let mut enumerated = false;
    if !r.exact && !is_empty(&r.dom) {
        tx.start(&r.dom, marks);
        if tx.fwd(root, ROOT).meets(demand) {
            r.exact = true;
        }
    }
    let (mut relation, mut refusal) = (None, None);
    interval::rounded();
    if !r.exact
        && !is_empty(&r.dom)
        && let Some((rel, found)) = linear(tx, root, &r.dom, demand)
    {
        match found {
            Ok((dom, exact, why)) => {
                let exact = exact && !interval::rounded();
                r = Whole { dom, exact };
                relation = (!exact).then_some(rel);
                refusal = why;
            }
            Err(why) => refusal = Some(why),
        }
    }
    if !r.exact
        && let Some(e) = enumerate(term, &r.dom, demand)
    {
        r = e;
        enumerated = true;
        if r.exact {
            relation = None;
            refusal = None;
        }
    }
    stops.dedup();
    Preimage {
        domains: r.dom,
        exact: r.exact,
        enumerated,
        stops,
        relation,
        refusal,
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
    let mut tx = Tx::new();
    tx.start(&doms, Landmarks::none());
    let mut tr = Tr {
        defs: Vec::new(),
        products,
    };
    let mut out = Vec::new();
    for t in terms {
        let root = tx.terms.add(t);
        // An auxiliary variable belongs to the relation of the term that made it.
        let m = &mut tx.run.memo;
        m.lin.clear();
        m.formula.clear();
        m.lin_calls.clear();
        m.formula_calls.clear();
        m.log.clear();
        let first = tr.defs.len();
        let body = tx.formula(&mut tr, root, ROOT)?;
        out.push(Relation {
            body,
            defs: tr.defs[first..].to_vec(),
        });
    }
    Some(out)
}

/// The linear stage: the relation of the demand over the box `dom`, the box narrowed to its
/// projections and whether the box entails the relation, with the refusal that left the latter
/// undecided, or the refusal that left the projections undecided. `None` when the term
/// is outside the domain or the relation is refused.
#[allow(clippy::type_complexity)]
fn linear(
    tx: &mut Tx<'_>,
    root: Tid,
    dom: &Domains,
    demand: &Demand,
) -> Option<(Relation, Result<(Domains, bool, Option<Refusal>), Refusal>)> {
    tx.start(dom, Landmarks::none());
    let mut tr = Tr {
        defs: Vec::new(),
        products: false,
    };
    let body = match demand {
        Demand::Bool(w) => {
            let f = tx.formula(&mut tr, root, ROOT)?;
            if *w { f } else { Formula::negate(f) }
        }
        Demand::Ints(z) => {
            let l = tx.lin(&mut tr, root, ROOT)?;
            presburger::within(&l, z)
        }
    };
    let rel = Relation {
        body,
        defs: tr.defs,
    };
    let go = || -> Result<(Domains, bool, Option<Refusal>), Refusal> {
        let within = |d: &Domains| -> Formula {
            let parts = d
                .iter()
                .map(|(k, v)| presburger::member(&presburger::Atom::Sym(k.clone()), v))
                .collect();
            Formula::and(parts)
        };
        let whole = Formula::and(vec![rel.defined(), within(dom), rel.body.clone()]);
        let mut mentioned = rel.body.atoms();
        for (_, _, f) in &rel.defs {
            mentioned.extend(f.atoms());
        }
        let syms: Vec<presburger::Atom> = dom
            .keys()
            .map(|k| presburger::Atom::Sym(k.clone()))
            .filter(|a| mentioned.contains(a))
            .collect();
        let (each, skipped) = presburger::project_each(&whole, &syms)?;
        let mut each = each.into_iter();
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
            return Ok((none, true, None));
        }
        let outside = Formula::and(vec![
            rel.defined(),
            within(&out),
            Formula::negate(rel.body.clone()),
        ]);
        Ok(match presburger::decide(&outside) {
            Ok(meets) => (out, !meets, skipped.first().copied()),
            Err(why) => (out, false, Some(why)),
        })
    };
    let found = go();
    Some((rel, found))
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

/// `l` as the operand of an infix operator: in parentheses unless it is one name or a natural
/// number.
fn operand(l: &Lin) -> String {
    let bare = match l.terms.iter().next() {
        None => !l.constant.is_negative(),
        Some((_, c)) => l.terms.len() == 1 && *c == Int::ONE && l.constant.is_zero(),
    };
    if bare {
        l.to_string()
    } else {
        format!("({l})")
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

/// A term's number among the terms of one transfer ([`Terms`]).
type Tid = u32;

/// A scope's number among the scopes of one transfer.
type Eid = u32;

/// A name's number among the names of one transfer.
type Name = u32;

/// The scope that binds no name.
const ROOT: Eid = 0;

/// A term and the scope it is read in, by their numbers: what the transfer remembers results
/// by.
type At = (Tid, Eid);

/// A run of consecutive numbers in [`Terms::kids`] or [`Terms::params`].
#[derive(Clone, Copy)]
struct Span {
    at: u32,
    len: u32,
}

impl Span {
    fn new(at: usize, len: usize) -> Span {
        Span {
            at: at as u32,
            len: len as u32,
        }
    }

    fn len(self) -> usize {
        self.len as usize
    }

    fn get(self, all: &[u32], i: usize) -> u32 {
        all[self.at as usize + i]
    }
}

/// A term of the transfer, its parts by number. A literal integer or boolean, a name and a
/// primitive application are the kinds the transfer makes itself.
#[derive(Clone, Copy)]
enum Node<'t> {
    Int(i64),
    Bool(bool),
    Lit(&'t Value),
    Var(Name),
    /// Parameters, in [`Terms::params`], and body.
    Lam(Span, Tid),
    /// Function and arguments, in [`Terms::kids`].
    App(Tid, Span),
    Prim(Prim, Span),
    PrimFn(Prim),
    Let(Name, Tid, Tid),
    If(Tid, Tid, Tid),
    /// A term the scalar catalog does not cover.
    Other,
}

/// A term the transfer makes, by what fixes it: a literal, a parameter's name, the primitive
/// application a call of a prelude word stands for (the call, and the primitive the word is
/// bound to), and the difference a comparison of two terms stands for (the comparison).
#[derive(PartialEq, Eq, Hash)]
enum Made {
    Int(i64),
    Bool(bool),
    Var(Name),
    Call(Tid, std::mem::Discriminant<Prim>),
    Diff(Tid),
}

/// The terms of one transfer, each numbered once: the given terms and their parts, and the
/// terms the transfer makes, each made once. Numbers, not addresses, are what results are
/// remembered by, so a number is never reused while a result keyed by it is kept.
#[derive(Default)]
struct Terms<'t> {
    nodes: Vec<Node<'t>>,
    /// The given term each number stands for; `None` for a made term.
    src: Vec<Option<&'t Term>>,
    kids: Vec<Tid>,
    params: Vec<Name>,
    names: Vec<Arc<str>>,
    name_ids: HashMap<Arc<str>, Name>,
    made: HashMap<Made, Tid>,
    /// The integer literals of the given terms, each term counted once.
    ints: Vec<i64>,
}

impl<'t> Terms<'t> {
    fn name(&mut self, x: &Arc<str>) -> Name {
        if let Some(&n) = self.name_ids.get(x) {
            return n;
        }
        let n = self.names.len() as Name;
        self.names.push(x.clone());
        self.name_ids.insert(x.clone(), n);
        n
    }

    /// Numbers `root` and its parts. A part the given term shares (one `Arc` reached twice)
    /// is numbered once: the walk keeps the parts it has met, by address, while it holds the
    /// term borrowed, so the walk takes time of the term's distinct parts and no address
    /// outlives it.
    fn add(&mut self, root: &'t Term) -> Tid {
        let mut seen = HashMap::new();
        let mut todo = Vec::new();
        let r = self.id(root, &mut seen, &mut todo);
        while let Some((t, id)) = todo.pop() {
            let node = match t {
                Term::Lit(Value::Int(n)) => {
                    self.ints.push(*n);
                    Node::Int(*n)
                }
                Term::Lit(Value::Bool(b)) => Node::Bool(*b),
                Term::Lit(v) => Node::Lit(v),
                Term::Var(x) => Node::Var(self.name(x)),
                Term::PrimFn(p) => Node::PrimFn(*p),
                Term::Lam(ps, b) => {
                    let at = self.params.len();
                    for p in ps {
                        let n = self.name(p);
                        self.params.push(n);
                    }
                    Node::Lam(Span::new(at, ps.len()), self.id(b, &mut seen, &mut todo))
                }
                Term::App(f, args) => {
                    let f = self.id(f, &mut seen, &mut todo);
                    Node::App(f, self.ids(args, &mut seen, &mut todo))
                }
                Term::Prim(p, args) => Node::Prim(*p, self.ids(args, &mut seen, &mut todo)),
                Term::Let(x, e, b) => Node::Let(
                    self.name(x),
                    self.id(e, &mut seen, &mut todo),
                    self.id(b, &mut seen, &mut todo),
                ),
                Term::If(g, a, b) => Node::If(
                    self.id(g, &mut seen, &mut todo),
                    self.id(a, &mut seen, &mut todo),
                    self.id(b, &mut seen, &mut todo),
                ),
                _ => Node::Other,
            };
            self.nodes[id as usize] = node;
        }
        r
    }

    /// The number of `t`, numbered now and its parts left to `todo` when it is new.
    fn id(
        &mut self,
        t: &'t Term,
        seen: &mut HashMap<*const Term, Tid>,
        todo: &mut Vec<(&'t Term, Tid)>,
    ) -> Tid {
        *seen.entry(t as *const Term).or_insert_with(|| {
            let id = self.nodes.len() as Tid;
            self.nodes.push(Node::Other);
            self.src.push(Some(t));
            todo.push((t, id));
            id
        })
    }

    fn ids(
        &mut self,
        ts: &'t [Term],
        seen: &mut HashMap<*const Term, Tid>,
        todo: &mut Vec<(&'t Term, Tid)>,
    ) -> Span {
        let at = self.kids.len();
        for t in ts {
            let id = self.id(t, seen, todo);
            self.kids.push(id);
        }
        Span::new(at, ts.len())
    }

    fn made(&mut self, m: Made, node: Node<'t>) -> Tid {
        if let Some(&t) = self.made.get(&m) {
            return t;
        }
        let t = self.nodes.len() as Tid;
        self.nodes.push(node);
        self.src.push(None);
        self.made.insert(m, t);
        t
    }

    fn int(&mut self, n: i64) -> Tid {
        self.made(Made::Int(n), Node::Int(n))
    }

    fn bool(&mut self, b: bool) -> Tid {
        self.made(Made::Bool(b), Node::Bool(b))
    }

    fn var(&mut self, x: Name) -> Tid {
        self.made(Made::Var(x), Node::Var(x))
    }

    /// The primitive application the call `app` of a word bound to `p` stands for.
    fn call(&mut self, app: Tid, p: Prim, args: Span) -> Tid {
        let key = Made::Call(app, std::mem::discriminant(&p));
        self.made(key, Node::Prim(p, args))
    }

    /// `a - b` for the comparison `cmp` of `a` and `b`.
    fn diff(&mut self, cmp: Tid, args: Span) -> Tid {
        self.made(Made::Diff(cmp), Node::Prim(Prim::Sub, args))
    }
}

/// An argument of a summarized call: a parameter over an interval, a constant, or a term that
/// reads no input, by the term and scope it resolves to.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Arg {
    Ints(IntervalSet),
    Int(i64),
    Bool(bool),
    At(At),
}

/// A summarized call: the lambda, by its body and scope, and its arguments.
type Summary = (At, Vec<Arg>);

/// A call to summarize: its summary's number, each parameter's binding (a name and the term and
/// scope it is bound to), and the parameters over intervals (the argument's place, the input
/// that stands for it, the interval).
struct Call {
    sid: u32,
    binds: Vec<(Name, At)>,
    params: Vec<(usize, Arc<str>, IntervalSet)>,
}

/// What one transfer over one box computes.
#[derive(Default)]
struct Run {
    stops: Vec<Stop>,
    seen: HashSet<String>,
    /// The bodies of the lambdas whose calls are being read, each with its place on the stack.
    active: HashMap<Tid, usize>,
    marks: Landmarks,
    /// The summaries met, each numbered once.
    sums: HashMap<Summary, u32>,
    fwds: HashMap<u32, Fwd>,
    backs: HashMap<(u32, Demand), Res>,
    scanned: HashSet<u32>,
    /// Whether an input's domain is empty, so that no point exists.
    void: bool,
    memo: Memo,
}

fn is_empty(d: &Domains) -> bool {
    d.values().any(IntervalSet::is_empty)
}

/// A scope: the names bound by `let` and by calls, each to a term and the scope it is read
/// in. It is persistent, so a name is found in `O(log n)` however many names are bound.
type Scope = imbl::HashMap<Name, At>;

/// What a call reaches.
#[derive(Clone, Copy)]
enum Callee {
    /// A lambda's parameters and body, with the scope the body is read in.
    Lam(Span, Tid, Eid),
    /// A primitive, as a prelude word binds it (the interpreter's prelude, step L1.18).
    Prim(Prim),
}

/// An interval per name, persistent: a copy takes `O(1)` and a change `O(log n)`.
type Sets = imbl::OrdMap<Arc<str>, Rc<IntervalSet>>;

/// A result of the transfer: the box, by the inputs it narrows, so that a result takes the
/// space of what the term reads and not of every enclosing parameter. A name not in `dom` has
/// the whole of its domain.
#[derive(Clone)]
struct Res {
    dom: Sets,
    /// Whether the box holds no point.
    none: bool,
    exact: bool,
}

impl Res {
    fn all() -> Res {
        Res {
            dom: Sets::new(),
            none: false,
            exact: true,
        }
    }

    fn none() -> Res {
        Res {
            none: true,
            ..Res::all()
        }
    }

    /// The whole box, which is not known to be exact.
    fn unknown() -> Res {
        Res {
            exact: false,
            ..Res::all()
        }
    }
}

/// A box over every input, after the transfer.
struct Whole {
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

/// What the transfer has computed, for each term and scope, so that a name bound once is
/// followed once however often it is read (the rule of low complexity, Part G), from
/// whichever summary it is read. The pair fixes the value: the inputs of the transfer are the
/// same in every context, and a parameter is read through the scope that binds it, which
/// differs for each summary, since the parameter's name holds the summary's number.
#[derive(Default)]
struct Memo {
    mentions: HashMap<At, Option<bool>>,
    constant: HashMap<At, Option<Value>>,
    fwd: HashMap<At, Fwd>,
    back: HashMap<(At, Demand), Res>,
    scan: HashSet<At>,
    lin: HashMap<At, Option<Lin>>,
    formula: HashMap<At, Option<Formula>>,
    /// The translations of calls, by the lambda and the translations of the arguments: a
    /// body's value depends on its parameters only through their values, so calls whose
    /// arguments translate alike translate alike, however they are reached.
    lin_calls: HashMap<CallKey, Option<Lin>>,
    formula_calls: HashMap<CallKey, Option<Formula>>,
    /// The translation entries in the order they were made, which a translation that is
    /// undone removes.
    log: Vec<Logged>,
}

/// A call to translate: the lambda, by its body and scope, and its arguments' linear terms.
type CallKey = (At, Vec<Lin>);

/// An entry of a translation memo.
enum Logged {
    Lin(At),
    Formula(At),
    LinCall(CallKey),
    FormulaCall(CallKey),
}

/// One of the memo's tables.
type Table<K, V> = fn(&mut Memo) -> &mut HashMap<K, V>;

/// A context: the inputs it reads, those of the transfer and the parameters of the summaries
/// it is within.
struct Cx {
    inputs: Sets,
    /// The lowest place on the stack of lambdas being read whose lambda a call stopped at,
    /// since the result being computed began. A result is remembered only when that place is
    /// not below the stack's height when it began: otherwise it depends on where it was
    /// reached.
    cut: usize,
}

/// The transfer: the terms and scopes, numbered, which outlive one box; what one run over a
/// box computes; and the context being read.
struct Tx<'t> {
    terms: Terms<'t>,
    scopes: Vec<Scope>,
    /// Each scope by the scope it extends and the binding it adds, so that a binding made
    /// twice gives one scope.
    scope_ids: HashMap<(Eid, Name, At), Eid>,
    run: Run,
    cx: Cx,
}

impl<'t> Tx<'t> {
    fn new() -> Self {
        Tx {
            terms: Terms::default(),
            scopes: vec![Scope::new()],
            scope_ids: HashMap::new(),
            run: Run::default(),
            cx: Cx {
                inputs: Sets::new(),
                cut: usize::MAX,
            },
        }
    }

    /// Begins a run over the box `inputs`.
    fn start(&mut self, inputs: &Domains, marks: Landmarks) {
        self.run = Run {
            marks,
            void: is_empty(inputs),
            ..Run::default()
        };
        self.cx = Cx {
            inputs: inputs
                .iter()
                .map(|(k, v)| (k.clone(), Rc::new(v.clone())))
                .collect(),
            cut: usize::MAX,
        };
    }

    /// The landmarks a summary's parameters and demands move out to: the terms' integer
    /// literals, the ends of the input domains and of the demand, each with its neighbors. A
    /// finite set, so a lambda has finitely many summaries.
    fn landmarks(&self, inputs: &Domains, demand: &Demand) -> Landmarks {
        let ends = |s: &IntervalSet| -> Vec<i64> {
            s.pieces()
                .iter()
                .flat_map(|&(a, b)| [a, b])
                .filter_map(|e| match e {
                    Fin(v) => Some(v),
                    _ => None,
                })
                .collect()
        };
        let demanded = match demand {
            Demand::Ints(z) => ends(z),
            Demand::Bool(_) => Vec::new(),
        };
        let ints = (self.terms.ints.iter().copied())
            .chain(inputs.values().flat_map(ends))
            .chain(demanded);
        Landmarks::of(ints, [])
    }

    fn node(&self, t: Tid) -> Node<'t> {
        self.terms.nodes[t as usize]
    }

    fn arg(&self, args: Span, i: usize) -> Tid {
        args.get(&self.terms.kids, i)
    }

    fn param(&self, ps: Span, i: usize) -> Name {
        ps.get(&self.terms.params, i)
    }

    fn name(&self, x: Name) -> &Arc<str> {
        &self.terms.names[x as usize]
    }

    fn lookup(&self, env: Eid, x: Name) -> Option<At> {
        self.scopes[env as usize].get(&x).copied()
    }

    /// The scope `env` with `x` bound to `to`, made once for each scope and binding.
    fn bind(&mut self, env: Eid, x: Name, to: At) -> Eid {
        let k = (env, x, to);
        if let Some(&e) = self.scope_ids.get(&k) {
            return e;
        }
        let e = self.scopes.len() as Eid;
        let s = self.scopes[env as usize].update(x, to);
        self.scopes.push(s);
        self.scope_ids.insert(k, e);
        e
    }

    /// The kernel term `t` stands for.
    fn term(&self, t: Tid) -> Term {
        if let Some(s) = self.terms.src[t as usize] {
            return s.clone();
        }
        match self.node(t) {
            Node::Int(n) => Term::Lit(Value::Int(n)),
            Node::Bool(b) => Term::Lit(Value::Bool(b)),
            Node::Var(x) => Term::Var(self.name(x).clone()),
            Node::Prim(p, args) => Term::Prim(
                p,
                (0..args.len())
                    .map(|i| self.term(self.arg(args, i)))
                    .collect(),
            ),
            _ => unreachable!("the transfer makes literals, names and primitive applications"),
        }
    }

    /// `t` as the kernel prints it.
    fn print(&self, t: Tid) -> String {
        match self.terms.src[t as usize] {
            Some(s) => s.to_string(),
            None => self.term(t).to_string(),
        }
    }

    /// Whether `a` and `b` are the same term, part by part. Each pair of parts is compared
    /// once, and a part that both share is not looked into.
    fn same(&self, a: Tid, b: Tid) -> bool {
        let (mut todo, mut seen) = (vec![(a, b)], HashSet::new());
        let pairs = |todo: &mut Vec<(Tid, Tid)>, s: Span, r: Span, all: &[u32]| {
            todo.extend((0..s.len()).map(|i| (s.get(all, i), r.get(all, i))));
        };
        while let Some((a, b)) = todo.pop() {
            if a == b || !seen.insert((a, b)) {
                continue;
            }
            match (self.node(a), self.node(b)) {
                (Node::Int(x), Node::Int(y)) if x == y => {}
                (Node::Bool(x), Node::Bool(y)) if x == y => {}
                (Node::Lit(x), Node::Lit(y)) if x == y => {}
                (Node::Var(x), Node::Var(y)) if x == y => {}
                (Node::PrimFn(p), Node::PrimFn(q)) if p == q => {}
                (Node::Lam(ps, x), Node::Lam(qs, y))
                    if ps.len() == qs.len()
                        && (0..ps.len()).all(|i| self.param(ps, i) == self.param(qs, i)) =>
                {
                    todo.push((x, y))
                }
                (Node::App(f, s), Node::App(g, r)) if s.len() == r.len() => {
                    todo.push((f, g));
                    pairs(&mut todo, s, r, &self.terms.kids);
                }
                (Node::Prim(p, s), Node::Prim(q, r)) if p == q && s.len() == r.len() => {
                    pairs(&mut todo, s, r, &self.terms.kids)
                }
                (Node::Let(x, e, c), Node::Let(y, f, d)) if x == y => todo.extend([(e, f), (c, d)]),
                (Node::If(g, x, c), Node::If(h, y, d)) => todo.extend([(g, h), (x, y), (c, d)]),
                (Node::Other, Node::Other)
                    if self.terms.src[a as usize] == self.terms.src[b as usize] => {}
                _ => return false,
            }
        }
        true
    }

    /// `f` with the lambda whose body is `body` on the stack of lambdas being read, given its
    /// place; or `stopped`, with the stop reported, when it is already there, since that call
    /// would make the same call again. The stack holds distinct lambdas, so it is no higher
    /// than the number of lambdas in the term.
    fn through<V>(
        &mut self,
        t: Tid,
        body: Tid,
        stopped: V,
        f: impl FnOnce(&mut Self, usize) -> V,
    ) -> V {
        if let Some(&at) = self.run.active.get(&body) {
            // Complexity tradeoff: a call of a lambda already being read (recursion) is not
            // read again; the transfer stops there with `StopKind::Recursion`, and the inputs
            // above it keep their forward intervals (necessary only). Why: reading through
            // recursion unfolds the call for every depth it may reach, which need not end,
            // and a fixpoint over the recursive summary is the full interprocedural analysis
            // this transfer avoids. Trigger: a call cycle through the term. Test:
            // `l01_25_preimage_catalog::stops::a_call_that_never_returns_stops_where_it_calls_itself`.
            // COMPLEXITY.md rows S12 and S15. A complete solution would compute a fixpoint of
            // the function's summary with widening, as the forward iteration does for loops.
            self.cx.cut = self.cx.cut.min(at);
            self.stop(StopKind::Recursion, t);
            return stopped;
        }
        let place = self.run.active.len();
        self.run.active.insert(body, place);
        let v = f(self, place);
        self.run.active.remove(&body);
        v
    }

    /// The summary of a call of the lambda with parameters `ps` and body `body` in scope
    /// `lam`, with `args` read in `env`, or `None` when an argument that reads an input may be
    /// other than an integer, or reads a term the catalog does not follow.
    fn summon(&mut self, ps: Span, body: Tid, lam: Eid, args: Span, env: Eid) -> Option<Call> {
        // Each parameter's binding, or `None` for a parameter over an interval.
        let (mut sig, mut binds, mut doms) = (Vec::new(), Vec::new(), Vec::new());
        for i in 0..ps.len() {
            let (p, a) = (self.param(ps, i), self.arg(args, i));
            if self.mentions(a, env)? {
                let f = self.fwd(a, env);
                // An argument with no value has no parameter: a context's points are those
                // of the transfer.
                if !f.is_int() || f.ints.is_empty() {
                    return None;
                }
                // Complexity tradeoff: the argument's interval is moved out to the landmarks
                // before it keys the summary, so the summary is taken over a wider parameter
                // and its preimage may be wider than the call's (not exact). Why: keyed by the
                // exact interval, a chain of k functions each calling the one before twice
                // makes a summary per distinct interval, up to 2^k; with landmarks the keys
                // per lambda are bounded by the landmark pairs. Trigger: an input-reading
                // integer argument whose ends are not landmarks. Tests:
                // `l01_25_preimage_catalog::scopes::one_function_called_twice_is_summarized_for_each_argument`,
                // `l01_25_preimage_catalog::scaling::nested_calls_are_summarized`. COMPLEXITY.md
                // rows S13 and S15. A complete solution would read each call in place (exact,
                // exponential in the nesting) or key summaries by relational summaries that
                // hold for every argument (a polyhedral or Presburger summary per function).
                let dom = f.ints.snap(&self.run.marks);
                sig.push(Arg::Ints(dom.clone()));
                doms.push((i, dom));
                binds.push((p, None));
                continue;
            }
            match self.constant(a, env) {
                Some(Value::Int(n)) => {
                    binds.push((p, Some((self.terms.int(n), ROOT))));
                    sig.push(Arg::Int(n));
                }
                Some(Value::Bool(b)) => {
                    binds.push((p, Some((self.terms.bool(b), ROOT))));
                    sig.push(Arg::Bool(b));
                }
                _ => {
                    let (mut t, mut e) = (a, env);
                    while let Node::Var(x) = self.node(t)
                        && let Some(to) = self.lookup(e, x)
                    {
                        (t, e) = to;
                    }
                    sig.push(Arg::At((t, e)));
                    binds.push((p, Some((t, e))));
                }
            }
        }
        let next = self.run.sums.len() as u32;
        let sid = *self.run.sums.entry(((body, lam), sig)).or_insert(next);
        let (mut doms, mut params) = (doms.into_iter(), Vec::new());
        let mut bound = Vec::with_capacity(binds.len());
        for (p, to) in binds {
            let to = match to {
                Some(to) => to,
                None => {
                    let (i, dom) = doms.next().expect("an interval for each parameter");
                    // A name no source name can be, one for each summary.
                    let name: Arc<str> = format!("\u{1}{i}.{sid}").into();
                    let x = self.terms.name(&name);
                    params.push((i, name, dom));
                    (self.terms.var(x), ROOT)
                }
            };
            bound.push((p, to));
        }
        Some(Call {
            sid,
            binds: bound,
            params,
        })
    }

    /// The context a summary is computed in: the inputs and the call's parameters, and the
    /// lambda's scope with its parameters bound.
    fn open(&mut self, call: &Call, lam: Eid) -> (Cx, Eid) {
        let mut inputs = self.cx.inputs.clone();
        for (_, n, d) in &call.params {
            inputs.insert(n.clone(), Rc::new(d.clone()));
        }
        let mut e = lam;
        for &(p, to) in &call.binds {
            e = self.bind(e, p, to);
        }
        let cx = Cx {
            inputs,
            cut: usize::MAX,
        };
        (cx, e)
    }

    /// `f` read in the context `sub`, and the lowest place a call in it stopped at.
    fn within<V>(&mut self, sub: Cx, f: impl FnOnce(&mut Self) -> V) -> (V, usize) {
        let outer = std::mem::replace(&mut self.cx, sub);
        let v = f(self);
        let sub = std::mem::replace(&mut self.cx, outer);
        (v, sub.cut)
    }

    /// Whether a summary computed in a context whose calls stopped no lower than `cut`, for
    /// the lambda at `place`, holds wherever it is reached; the stops below it are passed on.
    fn closes(&mut self, cut: usize, place: usize) -> bool {
        self.cx.cut = self.cx.cut.min(cut);
        cut >= place
    }

    /// The forward value of a summarized call.
    fn call_fwd(&mut self, call: Call, body: Tid, lam: Eid, place: usize) -> Fwd {
        if let Some(f) = self.run.fwds.get(&call.sid) {
            return f.clone();
        }
        let (sub, e) = self.open(&call, lam);
        let (f, cut) = self.within(sub, |s| s.fwd(body, e));
        if self.closes(cut, place) {
            self.run.fwds.insert(call.sid, f.clone());
        }
        f
    }

    /// The preimage of a summarized call: the summary's box over the inputs, met with each
    /// argument's preimage of the summary's interval for its parameter. Exact when the summary
    /// is, the demand's ends are landmarks, and each argument's preimage is exact.
    ///
    /// A summary keeps only the inputs it narrows. Its context holds every input of the
    /// context that first reached it, the parameters of enclosing summaries among them, and
    /// another context reaching the same summary may give those other intervals. An input
    /// the body reads has the same interval wherever the summary is reached: an input of the
    /// transfer is the same in every context, and an enclosing parameter is read through the
    /// lambda's scope, which the summary's key holds.
    #[allow(clippy::too_many_arguments)]
    fn call_back(
        &mut self,
        call: Call,
        body: Tid,
        lam: Eid,
        args: Span,
        env: Eid,
        d: &Demand,
        place: usize,
    ) -> Res {
        let (d, same) = match d {
            Demand::Ints(z) => {
                let s = z.snap(&self.run.marks);
                let same = s == *z;
                (Demand::Ints(s), same)
            }
            _ => (d.clone(), true),
        };
        let k = (call.sid, d);
        let r = match self.run.backs.get(&k) {
            Some(r) => r.clone(),
            None => {
                let (sub, e) = self.open(&call, lam);
                let (r, cut) = self.within(sub, |s| s.back_at(body, e, &k.1));
                if self.closes(cut, place) {
                    self.run.backs.insert(k, r.clone());
                }
                r
            }
        };
        if r.none {
            return Res::none();
        }
        let mut out = Res::all();
        out.exact = r.exact && same;
        for (k, z) in &r.dom {
            if self.cx.inputs.get(k).is_some_and(|w| w != z) {
                out.dom.insert(k.clone(), z.clone());
            }
        }
        for (i, n, dom) in &call.params {
            if let Some(z) = r.dom.get(n)
                && !dom.is_subset(z)
            {
                let ra = self.back_at(self.arg(args, *i), env, &Demand::Ints((**z).clone()));
                out = self.meet(out, ra);
            }
        }
        out
    }

    /// `f()`, remembered under `k` in `table` unless a call it reads stopped at a lambda that
    /// was being read before it began.
    fn cached<K: Hash + Eq, V: Clone>(
        &mut self,
        table: Table<K, V>,
        k: K,
        f: impl FnOnce(&mut Self) -> V,
    ) -> V {
        if let Some(v) = table(&mut self.run.memo).get(&k) {
            return v.clone();
        }
        let base = self.run.active.len();
        let outer = std::mem::replace(&mut self.cx.cut, usize::MAX);
        let v = f(self);
        let cut = self.cx.cut;
        if cut >= base {
            table(&mut self.run.memo).insert(k, v.clone());
        }
        self.cx.cut = outer.min(cut);
        v
    }

    /// [`Tx::cached`] for the translation into the linear-relation domain, whose entries a
    /// translation that is undone removes; `logged` names an entry for the log.
    fn translated<K: Hash + Eq + Clone, V: Clone>(
        &mut self,
        table: Table<K, V>,
        k: K,
        logged: impl FnOnce(K) -> Logged,
        f: impl FnOnce(&mut Self) -> V,
    ) -> V {
        let known = table(&mut self.run.memo).contains_key(&k);
        let v = self.cached(table, k.clone(), f);
        if !known && table(&mut self.run.memo).contains_key(&k) {
            self.run.memo.log.push(logged(k));
        }
        v
    }

    /// Removes the translation's entries made after the first `mark`.
    fn forget(&mut self, mark: usize) {
        let m = &mut self.run.memo;
        for e in m.log.drain(mark..) {
            match e {
                Logged::Lin(k) => _ = m.lin.remove(&k),
                Logged::Formula(k) => _ = m.formula.remove(&k),
                Logged::LinCall(k) => _ = m.lin_calls.remove(&k),
                Logged::FormulaCall(k) => _ = m.formula_calls.remove(&k),
            }
        }
    }

    /// The key a call of the lambda `body` in scope `lam` is translated under: `None`, with
    /// what the attempt made undone, when an argument has no linear term.
    fn call_key(
        &mut self,
        tr: &mut Tr,
        body: Tid,
        lam: Eid,
        args: Span,
        env: Eid,
    ) -> Option<CallKey> {
        let (mark, logged) = (tr.defs.len(), self.run.memo.log.len());
        let mut lins = Vec::with_capacity(args.len());
        for i in 0..args.len() {
            match self.lin(tr, self.arg(args, i), env) {
                Some(l) => lins.push(l),
                None => {
                    tr.defs.truncate(mark);
                    self.forget(logged);
                    return None;
                }
            }
        }
        Some(((body, lam), lins))
    }

    /// The scope of a `let` body.
    fn let_env(&mut self, n: Name, e: Tid, env: Eid) -> Eid {
        self.bind(env, n, (e, env))
    }

    /// The scope of a call's body: the lambda's scope with each parameter bound to its
    /// argument, read in the caller's scope.
    fn call_env(&mut self, ps: Span, args: Span, lam: Eid, caller: Eid) -> Eid {
        let mut e = lam;
        for i in 0..ps.len() {
            let (p, a) = (self.param(ps, i), self.arg(args, i));
            e = self.bind(e, p, (a, caller));
        }
        e
    }

    /// Whether the box holds no point.
    fn empty(&self, r: &Res) -> bool {
        r.none || self.run.void
    }

    /// The box over every input. A box that narrows a name of an empty domain is empty in
    /// every name, as a box found empty is; one that narrows nothing keeps the domains.
    fn whole(&self, r: &Res) -> Domains {
        let none = r.none || (self.run.void && !r.dom.is_empty());
        let of = |k: &Arc<str>, z: &Rc<IntervalSet>| {
            let z = match r.dom.get(k) {
                _ if none => IntervalSet::empty(),
                Some(n) => (**n).clone(),
                None => (**z).clone(),
            };
            (k.clone(), z)
        };
        self.cx.inputs.iter().map(|(k, z)| of(k, z)).collect()
    }

    fn stop(&mut self, kind: StopKind, t: Tid) -> Res {
        let s = Stop {
            kind,
            term: self.print(t),
        };
        if self.run.seen.insert(s.to_string()) {
            self.run.stops.push(s);
        }
        Res::unknown()
    }

    /// The meet, in time of the smaller box's names.
    fn meet(&self, a: Res, b: Res) -> Res {
        if self.empty(&a) || self.empty(&b) {
            return Res::none();
        }
        let exact = a.exact && b.exact;
        let (mut dom, small) = if a.dom.len() < b.dom.len() {
            (b.dom, a.dom)
        } else {
            (a.dom, b.dom)
        };
        for (k, v) in &small {
            let met = match dom.get(k) {
                Some(w) => Rc::new(v.meet(w)),
                None => v.clone(),
            };
            if met.is_empty() {
                return Res::none();
            }
            dom.insert(k.clone(), met);
        }
        Res {
            dom,
            none: false,
            exact,
        }
    }

    /// The union, as the per-input join of the two boxes: exact when both are and the union
    /// is itself a box. A name in only one box joins to its whole domain, so the time is that
    /// of the smaller box's names.
    ///
    /// Complexity tradeoff: a union of boxes that is not a box is answered by its box hull,
    /// which holds points neither side has (necessary, not exact). Why: a union of boxes kept
    /// exactly grows with each `||` and branch, up to 2^k boxes for k of them, and every
    /// later operation would pay for each box. Trigger: two boxes that differ in two or more
    /// inputs (a name held by one box only counts as a difference), with neither box within
    /// the other. Test:
    /// `l01_25_preimage_catalog::scopes::a_union_of_boxes_is_exact_when_it_is_a_box`.
    /// COMPLEXITY.md row C14. A complete solution would keep a list (or a decision diagram) of
    /// boxes, exponential in the disjunctions in the worst case.
    fn union(&self, a: Res, b: Res) -> Res {
        if self.empty(&a) {
            return b;
        }
        if self.empty(&b) {
            return a;
        }
        let (small, large) = if a.dom.len() < b.dom.len() {
            (&a.dom, &b.dom)
        } else {
            (&b.dom, &a.dom)
        };
        let mut dom = Sets::new();
        let (mut common, mut changed) = (0, 0);
        let (mut small_within, mut large_within) = (true, true);
        for (k, v) in small {
            let Some(w) = large.get(k) else { continue };
            common += 1;
            changed += usize::from(v != w);
            small_within &= v.is_subset(w);
            large_within &= w.is_subset(v);
            let joined = v.join(w);
            if self.cx.inputs.get(k).is_none_or(|z| **z != joined) {
                dom.insert(k.clone(), Rc::new(joined));
            }
        }
        // A box within another narrows every name that one narrows.
        small_within &= common == large.len();
        large_within &= common == small.len();
        let differ = small.len() + large.len() - 2 * common + changed;
        let boxed = differ <= 1 || small_within || large_within;
        Res {
            dom,
            none: false,
            exact: a.exact && b.exact && boxed,
        }
    }

    /// Whether the term reads an input, or `None` when it reads a term the catalog does not
    /// follow.
    fn mentions(&mut self, t: Tid, env: Eid) -> Option<bool> {
        self.cached(|m| &mut m.mentions, (t, env), |s| s.mentions_at(t, env))
    }

    fn mentions_at(&mut self, t: Tid, env: Eid) -> Option<bool> {
        let any = |s: &mut Self, ts: &mut dyn Iterator<Item = At>| -> Option<bool> {
            let mut m = false;
            for (t, e) in ts {
                m |= s.mentions(t, e)?;
            }
            Some(m)
        };
        match self.node(t) {
            Node::Int(_) | Node::Bool(_) | Node::Lit(_) | Node::PrimFn(_) => Some(false),
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.mentions(bt, be),
                None => Some(self.cx.inputs.contains_key(self.name(x))),
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                any(self, &mut [(e, env), (b, inner)].into_iter())
            }
            Node::Lam(ps, b) => {
                // A parameter is not an input, even where it shadows one.
                let no = (self.terms.bool(false), ROOT);
                let mut inner = env;
                for i in 0..ps.len() {
                    inner = self.bind(inner, self.param(ps, i), no);
                }
                self.mentions(b, inner)
            }
            Node::App(f, args) => {
                let kids = (0..args.len()).map(|i| (self.arg(args, i), env));
                let all: Vec<At> = std::iter::once((f, env)).chain(kids).collect();
                any(self, &mut all.into_iter())
            }
            Node::Prim(_, args) => {
                let all: Vec<At> = (0..args.len()).map(|i| (self.arg(args, i), env)).collect();
                any(self, &mut all.into_iter())
            }
            Node::If(g, a, b) => any(self, &mut [(g, env), (a, env), (b, env)].into_iter()),
            Node::Other => None,
        }
    }

    /// The term with every bound name replaced by the closed term it is bound to, for a term
    /// that reads no input. `local` holds the names bound within the term being closed: to
    /// the closed term a `let` binds, or to `None` for a lambda's parameter, which stays.
    fn close(&self, t: Tid, env: Eid, local: &Local) -> Option<Term> {
        let c = |t: Tid| self.close(t, env, local);
        let all = |args: Span| {
            (0..args.len())
                .map(|i| c(self.arg(args, i)))
                .collect::<Option<Vec<Term>>>()
        };
        Some(match self.node(t) {
            Node::Var(x) => match (local.get(&x), self.lookup(env, x)) {
                (Some(Some(bound)), _) => (**bound).clone(),
                (Some(None), _) | (None, None) => Term::Var(self.name(x).clone()),
                (None, Some((bt, be))) => self.close(bt, be, &Local::new())?,
            },
            Node::Int(n) => Term::Lit(Value::Int(n)),
            Node::Bool(b) => Term::Lit(Value::Bool(b)),
            Node::Lit(v) => Term::Lit(v.clone()),
            Node::PrimFn(p) => Term::PrimFn(p),
            Node::Let(n, e, b) => {
                // The body reads `n` as the closed bound term.
                let e = c(e)?;
                self.close(b, env, &local.update(n, Some(Rc::new(e))))?
            }
            Node::Lam(ps, b) => {
                let mut inner = local.clone();
                let mut names = Vec::with_capacity(ps.len());
                for i in 0..ps.len() {
                    let p = self.param(ps, i);
                    inner.insert(p, None);
                    names.push(self.name(p).clone());
                }
                Term::Lam(names, Arc::new(self.close(b, env, &inner)?))
            }
            Node::App(f, args) => Term::App(Arc::new(c(f)?), all(args)?),
            Node::Prim(p, args) => Term::Prim(p, all(args)?),
            Node::If(g, a, b) => Term::If(Arc::new(c(g)?), Arc::new(c(a)?), Arc::new(c(b)?)),
            Node::Other => return None,
        })
    }

    /// The value of a term that reads no input, when the evaluator can compute it.
    fn constant(&mut self, t: Tid, env: Eid) -> Option<Value> {
        self.cached(
            |m| &mut m.constant,
            (t, env),
            |s| {
                if s.mentions(t, env)? {
                    return None;
                }
                // From the values of the parts where the catalog reads them, so that a part is
                // run once; otherwise the closed term.
                match s.node(t) {
                    Node::Int(n) => Some(Value::Int(n)),
                    Node::Bool(b) => Some(Value::Bool(b)),
                    Node::Lit(v) => Some(v.clone()),
                    Node::Var(x) if let Some((bt, be)) = s.lookup(env, x) => s.constant(bt, be),
                    Node::Let(n, e, b) => {
                        let inner = s.let_env(n, e, env);
                        s.constant(b, inner)
                    }
                    Node::Prim(p, args) => {
                        let mut vs = Vec::with_capacity(args.len());
                        for i in 0..args.len() {
                            vs.push(Term::Lit(s.constant(s.arg(args, i), env)?));
                        }
                        eval(&Term::Prim(p, vs)).ok()
                    }
                    Node::If(g, a, b) => match s.constant(g, env)? {
                        Value::Bool(true) => s.constant(a, env),
                        Value::Bool(false) => s.constant(b, env),
                        _ => run_closed(&s.close(t, env, &Local::new())?),
                    },
                    _ => run_closed(&s.close(t, env, &Local::new())?),
                }
            },
        )
    }

    fn constant_int(&mut self, t: Tid, env: Eid) -> Option<i64> {
        match self.constant(t, env)? {
            Value::Int(n) => Some(n),
            _ => None,
        }
    }

    /// The function a call reaches, with the scope its body is read in. Each name is looked
    /// up in the scope its binding was made in, which was built before that binding, so the
    /// walk ends.
    fn callee(&self, f: Tid, env: Eid) -> Result<Callee, Option<Arc<str>>> {
        let (mut f, mut env) = (f, env);
        loop {
            match self.node(f) {
                Node::Lam(ps, b) => return Ok(Callee::Lam(ps, b, env)),
                Node::PrimFn(p) => return Ok(Callee::Prim(p)),
                Node::Var(x) => match self.lookup(env, x) {
                    Some(to) => (f, env) = to,
                    None => return Err(Some(self.name(x).clone())),
                },
                _ => return Err(None),
            }
        }
    }

    /// The factors of a product of one value read `k` times, as that value and `k`.
    fn power(&self, t: Tid, env: Eid) -> Option<(Tid, Eid, u32)> {
        let mut fs = Vec::new();
        self.factors(t, env, &mut fs);
        let (first, fenv) = fs[0];
        let one = |&(t, e): &At| match (self.node(t), self.node(first)) {
            (Node::Var(x), Node::Var(y)) if x == y => true,
            _ => e == fenv && self.same(t, first),
        };
        (fs.len() >= 2 && fs.len() <= POWER_FACTORS && fs.iter().all(one)).then_some((
            first,
            fenv,
            fs.len() as u32,
        ))
    }

    fn factors(&self, t: Tid, env: Eid, out: &mut Vec<At>) {
        let (mut t, mut env) = (t, env);
        while let Node::Var(x) = self.node(t)
            && let Some(to) = self.lookup(env, x)
        {
            (t, env) = to;
        }
        match self.node(t) {
            _ if out.len() > POWER_FACTORS => {}
            Node::Prim(Prim::Mul, args) if args.len() == 2 => {
                self.factors(self.arg(args, 0), env, out);
                self.factors(self.arg(args, 1), env, out);
            }
            _ => out.push((t, env)),
        }
    }

    // ---- Into the linear-relation domain ------------------------------------------------

    /// The linear term an integer term states over the inputs.
    fn lin(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Lin> {
        self.translated(
            |m| &mut m.lin,
            (t, env),
            Logged::Lin,
            |s| s.lin_at(tr, t, env),
        )
    }

    fn lin_at(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Lin> {
        use Prim::*;
        if let Some(v) = self.constant(t, env) {
            return match v {
                Value::Int(n) => Some(Lin::constant(n)),
                _ => None,
            };
        }
        match self.node(t) {
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.lin(tr, bt, be),
                None => {
                    let x = self.name(x);
                    (self.cx.inputs.contains_key(x))
                        .then(|| Lin::atom(presburger::Atom::Sym(x.clone())))
                }
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.lin(tr, b, inner)
            }
            Node::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    let read = |s: &mut Self, tr: &mut Tr| {
                        s.through(t, body, None, |s, _| {
                            let inner = s.call_env(ps, args, lam, env);
                            s.lin(tr, body, inner)
                        })
                    };
                    match self.call_key(tr, body, lam, args, env) {
                        Some(k) => self.translated(
                            |m| &mut m.lin_calls,
                            k,
                            Logged::LinCall,
                            |s| read(s, tr),
                        ),
                        None => read(self, tr),
                    }
                }
                Callee::Prim(p) => {
                    let c = self.terms.call(t, p, args);
                    self.lin(tr, c, env)
                }
                Callee::Lam(..) => None,
            },
            Node::If(g, a, b) => {
                let g = self.formula(tr, g, env)?;
                let (la, lb) = (self.lin(tr, a, env)?, self.lin(tr, b, env)?);
                // One level: the parts are shown by their linear forms, in which an auxiliary
                // variable is its name, so the name costs the size of what it is made of.
                let what = format!("if {g} then {la} else {lb}");
                let x = Lin::atom(presburger::Atom::Aux(tr.defs.len() as u32));
                let def = Formula::or(vec![
                    Formula::and(vec![g.clone(), Formula::Con(Con::eq(&x, &la))]),
                    Formula::and(vec![Formula::negate(g), Formula::Con(Con::eq(&x, &lb))]),
                ]);
                tr.aux(what, def);
                Some(x)
            }
            Node::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => {
                let arg = |s: &mut Self, tr: &mut Tr, i: usize| s.lin(tr, s.arg(args, i), env);
                match p {
                    Add => Some(arg(self, tr, 0)?.plus(&arg(self, tr, 1)?)),
                    Sub => Some(arg(self, tr, 0)?.minus(&arg(self, tr, 1)?)),
                    Neg => Some(arg(self, tr, 0)?.times(-1)),
                    Mul => {
                        let (a, b) = (arg(self, tr, 0)?, arg(self, tr, 1)?);
                        if !tr.products && !a.terms.is_empty() && !b.terms.is_empty() {
                            return None;
                        }
                        a.product(&b)
                    }
                    Pow => match self.constant_int(self.arg(args, 1), env)? {
                        0 => Some(Lin::constant(1)),
                        1 => arg(self, tr, 0),
                        2 if tr.products => {
                            let a = arg(self, tr, 0)?;
                            a.product(&a)
                        }
                        _ => None,
                    },
                    IntDiv | Mod => {
                        let c = (self.constant_int(self.arg(args, 1), env)).filter(|c| *c != 0)?;
                        let a = arg(self, tr, 0)?;
                        // `a == c·q + r` and `0 <= r < |c|`: Euclidean.
                        let n = tr.defs.len() as u32;
                        let (q, r) = (
                            Lin::atom(presburger::Atom::Aux(n)),
                            Lin::atom(presburger::Atom::Aux(n + 1)),
                        );
                        let c = i128::from(c);
                        let def = Formula::and(vec![
                            Formula::Con(Con::eq(&a, &q.times(c).plus(&r))),
                            Formula::Con(Con::ge(&r, &Lin::constant(0))),
                            Formula::Con(Con::ge(&Lin::constant(c.abs() - 1), &r)),
                        ]);
                        let first = operand(&a);
                        let shown = |op: &str| format!("{first} {op} {c}");
                        tr.defs.push((n, shown("div"), def));
                        tr.defs.push((n + 1, shown("mod"), Formula::top()));
                        Some(if p == IntDiv { q } else { r })
                    }
                    Min | Max | Abs => {
                        let a = arg(self, tr, 0)?;
                        let b = if p == Abs {
                            a.times(-1)
                        } else {
                            arg(self, tr, 1)?
                        };
                        let x = Lin::atom(presburger::Atom::Aux(tr.defs.len() as u32));
                        // `min` takes `a` where `a <= b`, `max` and `abs` where `a >= b`.
                        let (lo, hi) = if p == Min { (&a, &b) } else { (&b, &a) };
                        let first = Con::ge(hi, lo);
                        let def = Formula::or(vec![
                            Formula::and(vec![
                                Formula::Con(first.clone()),
                                Formula::Con(Con::eq(&x, &a)),
                            ]),
                            Formula::and(vec![
                                Formula::negate(Formula::Con(first)),
                                Formula::Con(Con::eq(&x, &b)),
                            ]),
                        ]);
                        let what = match p {
                            Abs => format!("abs({a})"),
                            Min => format!("min({a}, {b})"),
                            _ => format!("max({a}, {b})"),
                        };
                        tr.aux(what, def);
                        Some(x)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The formula a test states over the inputs.
    fn formula(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Formula> {
        self.translated(
            |m| &mut m.formula,
            (t, env),
            Logged::Formula,
            |s| s.formula_at(tr, t, env),
        )
    }

    fn formula_at(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Formula> {
        use Prim::*;
        if let Some(v) = self.constant(t, env) {
            return match v {
                Value::Bool(true) => Some(Formula::top()),
                Value::Bool(false) => Some(Formula::bottom()),
                _ => None,
            };
        }
        match self.node(t) {
            Node::Var(x) => {
                let (bt, be) = self.lookup(env, x)?;
                self.formula(tr, bt, be)
            }
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.formula(tr, b, inner)
            }
            Node::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    let read = |s: &mut Self, tr: &mut Tr| {
                        s.through(t, body, None, |s, _| {
                            let inner = s.call_env(ps, args, lam, env);
                            s.formula(tr, body, inner)
                        })
                    };
                    match self.call_key(tr, body, lam, args, env) {
                        Some(k) => self.translated(
                            |m| &mut m.formula_calls,
                            k,
                            Logged::FormulaCall,
                            |s| read(s, tr),
                        ),
                        None => read(self, tr),
                    }
                }
                Callee::Prim(p) => {
                    let c = self.terms.call(t, p, args);
                    self.formula(tr, c, env)
                }
                Callee::Lam(..) => None,
            },
            Node::If(g, a, b) => {
                let g = self.formula(tr, g, env)?;
                let (fa, fb) = (self.formula(tr, a, env)?, self.formula(tr, b, env)?);
                Some(Formula::or(vec![
                    Formula::and(vec![g.clone(), fa]),
                    Formula::and(vec![Formula::negate(g), fb]),
                ]))
            }
            Node::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => {
                let (a, b) = (
                    self.arg(args, 0),
                    (args.len() > 1).then(|| self.arg(args, 1)),
                );
                match p {
                    Not => Some(Formula::negate(self.formula(tr, a, env)?)),
                    And | Or => {
                        let b = b.expect("two operands");
                        let (a, b) = (self.formula(tr, a, env)?, self.formula(tr, b, env)?);
                        Some(if p == And {
                            Formula::and(vec![a, b])
                        } else {
                            Formula::or(vec![a, b])
                        })
                    }
                    Lt | Le | Gt | Ge | Eq | Ne => {
                        let b = b.expect("two operands");
                        let (mark, logged) = (tr.defs.len(), self.run.memo.log.len());
                        if let (Some(la), Some(lb)) = (self.lin(tr, a, env), self.lin(tr, b, env)) {
                            let one = Lin::constant(1);
                            let c = match p {
                                Lt => Con::ge(&lb, &la.plus(&one)),
                                Le => Con::ge(&lb, &la),
                                Gt => Con::ge(&la, &lb.plus(&one)),
                                Ge => Con::ge(&la, &lb),
                                _ => Con::eq(&la, &lb),
                            };
                            let f = Formula::Con(c);
                            return Some(if p == Ne { Formula::negate(f) } else { f });
                        }
                        tr.defs.truncate(mark);
                        self.forget(logged);
                        if !matches!(p, Eq | Ne) {
                            return None;
                        }
                        // Two tests are equal where both hold or neither does.
                        let (fa, fb) = (self.formula(tr, a, env)?, self.formula(tr, b, env)?);
                        let same = Formula::or(vec![
                            Formula::and(vec![fa.clone(), fb.clone()]),
                            Formula::and(vec![Formula::negate(fa), Formula::negate(fb)]),
                        ]);
                        Some(if p == Ne { Formula::negate(same) } else { same })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    // ---- Forward transfer -------------------------------------------------------------

    fn fwd(&mut self, t: Tid, env: Eid) -> Fwd {
        self.cached(|m| &mut m.fwd, (t, env), |s| s.fwd_at(t, env))
    }

    fn fwd_at(&mut self, t: Tid, env: Eid) -> Fwd {
        match self.node(t) {
            Node::Int(n) => Fwd::int(IntervalSet::single(n)),
            Node::Bool(b) => Fwd::bools(b, !b),
            Node::Lit(Value::Atom(_)) => Fwd {
                fails: true,
                ..Fwd::none()
            },
            Node::Lit(_) => Fwd {
                other: true,
                ..Fwd::none()
            },
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.fwd(bt, be),
                None => match self.cx.inputs.get(self.name(x)) {
                    Some(dom) => Fwd::int((**dom).clone()),
                    None => Fwd::top(),
                },
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.fwd(b, inner)
            }
            Node::If(g, a, b) => {
                let g = self.fwd(g, env);
                // A guard that is not a test is a failure.
                let mut out = Fwd {
                    fails: !g.is_bool(),
                    ..Fwd::none()
                };
                for (arm, live) in [(a, g.bools.0), (b, g.bools.1)] {
                    if live {
                        let f = self.fwd(arm, env);
                        out.ints = out.ints.join(&f.ints);
                        out.bools = (out.bools.0 || f.bools.0, out.bools.1 || f.bools.1);
                        out.fails |= f.fails;
                        out.other |= f.other;
                    }
                }
                out
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    self.through(t, body, Fwd::top(), |s, place| {
                        match s.summon(ps, body, lam, args, env) {
                            Some(call) => s.call_fwd(call, body, lam, place),
                            None => {
                                let inner = s.call_env(ps, args, lam, env);
                                s.fwd(body, inner)
                            }
                        }
                    })
                }
                Ok(Callee::Prim(p)) => {
                    let c = self.terms.call(t, p, args);
                    self.fwd(c, env)
                }
                _ => Fwd::top(),
            },
            Node::Prim(p, args) => self.fwd_prim(t, p, args, env),
            _ => Fwd::top(),
        }
    }

    fn fwd_prim(&mut self, t: Tid, p: Prim, args: Span, env: Eid) -> Fwd {
        use Prim::*;
        if p.arity().is_some_and(|n| n != args.len()) {
            return Fwd::top();
        }
        if p == Mul
            && let Some((base, be, k)) = self.power(t, env)
        {
            let b = self.fwd(base, be);
            return self.arith(Op::Pow(k), &b, &b, false);
        }
        let fwd = |s: &mut Self, i: usize| s.fwd(s.arg(args, i), env);
        match p {
            Neg | Abs => {
                let a = fwd(self, 0);
                self.arith(op(p, None).expect("scalar"), &a, &a, false)
            }
            Pow => match self.constant_int(self.arg(args, 1), env).map(u32::try_from) {
                Some(Ok(k)) => {
                    let a = fwd(self, 0);
                    self.arith(Op::Pow(k), &a, &a, false)
                }
                _ => Fwd::top(),
            },
            Add | Sub | Mul | IntDiv | Mod | Min | Max => {
                let a = fwd(self, 0);
                let b = fwd(self, 1);
                let by_zero = matches!(p, IntDiv | Mod) && b.ints.contains(0);
                self.arith(op(p, None).expect("scalar"), &a, &b, by_zero)
            }
            Lt | Le | Gt | Ge | Eq | Ne => {
                let a = fwd(self, 0);
                let b = fwd(self, 1);
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
                let a = fwd(self, 0);
                Fwd {
                    bools: (a.bools.1, a.bools.0),
                    fails: !a.is_bool(),
                    ..Fwd::none()
                }
            }
            And | Or => {
                let a = fwd(self, 0);
                let b = fwd(self, 1);
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

    fn back(&mut self, t: Tid, env: Eid, d: &Demand) -> Res {
        self.back_at(t, env, d)
    }

    fn back_at(&mut self, t: Tid, env: Eid, d: &Demand) -> Res {
        self.cached(
            |m| &mut m.back,
            ((t, env), d.clone()),
            |s| s.back_in(t, env, d),
        )
    }

    fn back_in(&mut self, t: Tid, env: Eid, d: &Demand) -> Res {
        if let Demand::Ints(z) = d
            && z.is_empty()
        {
            return Res::none();
        }
        // A term that reads no input is decided by running it.
        if !matches!(self.node(t), Node::Var(_))
            && let Some(v) = self.constant(t, env)
        {
            return if d.holds(&v) { Res::all() } else { Res::none() };
        }
        let holds = |v: &Value| if d.holds(v) { Res::all() } else { Res::none() };
        match self.node(t) {
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.back_at(bt, be, d),
                None => {
                    let x = self.name(x);
                    match (self.cx.inputs.get(x), d) {
                        (Some(dom), Demand::Ints(z)) => {
                            let met = dom.meet(z);
                            if met.is_empty() {
                                return Res::none();
                            }
                            let mut r = Res::all();
                            if met != **dom {
                                r.dom.insert(x.clone(), Rc::new(met));
                            }
                            r
                        }
                        (Some(_), Demand::Bool(_)) => Res::none(),
                        (None, _) => {
                            let kind = StopKind::Foreign(x.clone());
                            self.stop(kind, t)
                        }
                    }
                }
            },
            Node::Int(n) => holds(&Value::Int(n)),
            Node::Bool(b) => holds(&Value::Bool(b)),
            Node::Lit(v) => holds(v),
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.back_at(b, inner, d)
            }
            Node::If(g, a, b) => {
                let gt = self.back_at(g, env, &Demand::Bool(true));
                let at = self.back_at(a, env, d);
                let gf = self.back_at(g, env, &Demand::Bool(false));
                let bf = self.back_at(b, env, d);
                let yes = self.meet(gt, at);
                let no = self.meet(gf, bf);
                self.union(yes, no)
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    self.through(t, body, Res::unknown(), |s, place| {
                        match s.summon(ps, body, lam, args, env) {
                            Some(call) => s.call_back(call, body, lam, args, env, d, place),
                            None => {
                                let inner = s.call_env(ps, args, lam, env);
                                s.back_at(body, inner, d)
                            }
                        }
                    })
                }
                Ok(Callee::Prim(p)) => {
                    let c = self.terms.call(t, p, args);
                    self.back_at(c, env, d)
                }
                Err(Some(name)) => self.stop(StopKind::Foreign(name), t),
                _ => self.stop(StopKind::Outside, t),
            },
            Node::Prim(p, args) => {
                if p.arity().is_some_and(|n| n != args.len()) {
                    return self.stop(StopKind::Outside, t);
                }
                self.back_prim(t, p, args, env, d)
            }
            _ => self.stop(StopKind::Outside, t),
        }
    }

    fn back_prim(&mut self, t: Tid, p: Prim, args: Span, env: Eid, d: &Demand) -> Res {
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
                self.scan(self.arg(args, 0), env);
                Res::unknown()
            }
            Not | And | Or => match *d {
                Demand::Ints(_) => Res::none(),
                Demand::Bool(w) if p == Not => {
                    self.back_at(self.arg(args, 0), env, &Demand::Bool(!w))
                }
                Demand::Bool(w) => {
                    let (x, y) = (self.arg(args, 0), self.arg(args, 1));
                    let a = self.back_at(x, env, d);
                    let b = self.back_at(y, env, d);
                    if (p == And) == w {
                        return self.meet(a, b);
                    }
                    // `&&` and `||` here are strict: one side meeting the demand is enough
                    // only when the other cannot fail.
                    let strict = self.fwd(x, env).is_bool() && self.fwd(y, env).is_bool();
                    let mut r = self.union(a, b);
                    r.exact &= strict;
                    r
                }
            },
            Lt | Le | Gt | Ge | Eq | Ne => match *d {
                Demand::Ints(_) => Res::none(),
                Demand::Bool(w) => {
                    let p = if w { p } else { negate(p) };
                    self.back_compare(t, p, args, env)
                }
            },
            Add | Sub | Mul | IntDiv | Mod | Neg | Abs | Pow => match ints_of(d) {
                Some(z) => self.back_arith(t, p, args, env, &z),
                None => Res::none(),
            },
            Min | Max => match ints_of(d) {
                Some(z) => self.back_arith(t, p, args, env, &z),
                // `min` and `max` of two tests are tests.
                None => self.stop(StopKind::Outside, t),
            },
            _ => self.stop(StopKind::Outside, t),
        }
    }

    /// The comparison `t` of its operands `args` by `p`, which may be `t`'s own comparison
    /// negated.
    fn back_compare(&mut self, t: Tid, p: Prim, args: Span, env: Eid) -> Res {
        let (a, b) = (self.arg(args, 0), self.arg(args, 1));
        let (fa, fb) = (self.fwd(a, env), self.fwd(b, env));
        // Two tests are equal where both are true or both false.
        if matches!(p, Prim::Eq | Prim::Ne) && fa.is_bool() && fb.is_bool() {
            let mut arms = Vec::new();
            for w in [true, false] {
                let ra = self.back_at(a, env, &Demand::Bool(w));
                let rb = self.back_at(b, env, &Demand::Bool(w == (p == Prim::Eq)));
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
            return self.back_at(a, env, &Demand::Ints(ray(p, c)));
        }
        if let Some(c) = self.constant_int(a, env)
            && (ints || ordered_or_eq(&fb))
        {
            return self.back_at(b, env, &Demand::Ints(ray(mirror(p), c)));
        }
        let one_int = fa.is_int() || fb.is_int();
        if ints || (ordered_or_eq(&fa) && ordered_or_eq(&fb) && (p != Prim::Eq || one_int)) {
            // Between two integers, `a op b` is `a - b op 0`.
            let diff = self.terms.diff(t, args);
            return self.back_at(diff, env, &Demand::Ints(ray(p, 0)));
        }
        // Operands of other kinds, or two that may both fail, which `==` finds equal.
        self.scan(a, env);
        self.scan(b, env);
        Res::unknown()
    }

    /// Reports the stops in a term whose value the transfer does not follow.
    fn scan(&mut self, t: Tid, env: Eid) {
        // A term is scanned once in each scope: its stops are reported the first time.
        if !self.run.memo.scan.insert((t, env)) {
            return;
        }
        if self.mentions(t, env) == Some(false) {
            return;
        }
        match self.node(t) {
            Node::Var(x) => {
                if let Some((bt, be)) = self.lookup(env, x) {
                    self.scan(bt, be);
                }
            }
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.scan(b, inner)
            }
            Node::If(g, a, b) => {
                for u in [g, a, b] {
                    self.scan(u, env);
                }
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    self.through(t, body, (), |s, place| {
                        match s.summon(ps, body, lam, args, env) {
                            Some(call) => {
                                if s.run.scanned.insert(call.sid) {
                                    let (sub, e) = s.open(&call, lam);
                                    let ((), cut) = s.within(sub, |s| s.scan(body, e));
                                    s.closes(cut, place);
                                }
                            }
                            None => {
                                let inner = s.call_env(ps, args, lam, env);
                                s.scan(body, inner)
                            }
                        }
                    })
                }
                Ok(Callee::Prim(p)) => {
                    let c = self.terms.call(t, p, args);
                    self.scan(c, env)
                }
                Err(Some(name)) => {
                    self.stop(StopKind::Foreign(name), t);
                }
                _ => {
                    self.stop(StopKind::Outside, t);
                }
            },
            Node::Prim(
                p @ (Prim::Show | Prim::Lower | Prim::Upper | Prim::Trim | Prim::Concat),
                _,
            ) => {
                self.stop(StopKind::String(p), t);
            }
            Node::Prim(p, args) if scalar(p) => {
                for i in 0..args.len() {
                    self.scan(self.arg(args, i), env);
                }
            }
            _ => {
                self.stop(StopKind::Outside, t);
            }
        }
    }

    fn back_arith(&mut self, t: Tid, p: Prim, args: Span, env: Eid, z: &IntervalSet) -> Res {
        use Prim::*;
        let ints = |s: IntervalSet| Demand::Ints(s);
        if p == Mul
            && let Some((base, be, k)) = self.power(t, env)
        {
            return self.back_unary(Op::Pow(k), base, be, z);
        }
        let a = self.arg(args, 0);
        match p {
            Neg | Abs => {
                return self.back_unary(op(p, None).expect("scalar"), a, env, z);
            }
            Pow => {
                let b = self.arg(args, 1);
                return match self.constant_int(b, env).map(u32::try_from) {
                    Some(Ok(k)) => self.back_unary(Op::Pow(k), a, env, z),
                    // A variable exponent: only the points where both operands are integers.
                    _ => self.both_ints(a, b, env),
                };
            }
            _ => {}
        }
        let b = self.arg(args, 1);
        let ca = self.constant_int(a, env);
        let cb = self.constant_int(b, env);
        match (p, ca, cb) {
            (Add, Some(c), _) => self.back_at(b, env, &ints(shift(z, -(c as i128)))),
            (Add, _, Some(c)) | (Sub, _, Some(c)) => {
                let c = if p == Add { -(c as i128) } else { c as i128 };
                self.back_at(a, env, &ints(shift(z, c)))
            }
            (Sub, Some(c), _) => {
                let r = revision::forward(Op::Sub, &IntervalSet::single(c), z);
                self.back_at(b, env, &ints(r))
            }
            (Mul, Some(c), _) => self.back_at(b, env, &ints(times_pre(z, c))),
            (Mul, _, Some(c)) => self.back_at(a, env, &ints(times_pre(z, c))),
            (IntDiv, _, Some(c)) => self.back_at(a, env, &ints(div_pre(z, c))),
            (Mod, _, Some(c)) => {
                let fa = self.fwd(a, env).ints;
                let (s, exact) = mod_pre(z, c, &fa);
                let mut r = self.back_at(a, env, &ints(s));
                r.exact &= exact;
                r
            }
            (Min | Max, Some(c), _) => self.back_at(b, env, &ints(minmax_pre(p, z, c))),
            (Min | Max, _, Some(c)) => self.back_at(a, env, &ints(minmax_pre(p, z, c))),
            (Min | Max, None, None) => {
                let f = self.fwd(t, env).ints;
                let zf = z.meet(&f);
                let (Some((flo, fhi)), Some((lo, hi))) = (f.bounds(), zf.bounds()) else {
                    return Res::none();
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
                    let ra = self.back_at(a, env, &ints(r.clone()));
                    let rb = self.back_at(b, env, &ints(r));
                    return if both {
                        self.meet(ra, rb)
                    } else {
                        self.union(ra, rb)
                    };
                }
                self.project(p, a, b, env, z)
            }
            _ => self.project(p, a, b, env, z),
        }
    }

    /// `op(c)` in `z`, for an operator the revision table inverts exactly within the forward
    /// interval of `c`.
    fn back_unary(&mut self, o: Op, c: Tid, env: Eid, z: &IntervalSet) -> Res {
        if o == Op::Pow(0) {
            // `c ** 0` is 1 wherever `c` is an integer.
            return if z.contains(1) {
                self.back_at(c, env, &Demand::Ints(IntervalSet::top()))
            } else {
                Res::none()
            };
        }
        let fc = self.fwd(c, env).ints;
        let zc = revision::backward(o, 0, &fc, &fc, z);
        self.back_at(c, env, &Demand::Ints(zc))
    }

    /// The HC4 projection onto each operand: necessary, not exact.
    ///
    /// Complexity tradeoff: each operand is narrowed alone against the other's forward
    /// interval, so the relation between the operands is given up and the box can hold
    /// points that fail the demand. Why: the exact preimage of a nonlinear operator is a
    /// region that is not a box, and finding it costs the points of the box (or is
    /// undecidable for polynomial tests over unbounded integers). Trigger: an operator with
    /// no exact catalog entry (anything but shifts, scalings, `div` and `mod` by a constant,
    /// `**`, and branches), or two operands that both read inputs. Test:
    /// `l01_25_preimage_catalog::entries::a_strict_disjunction_with_a_failing_side_is_necessary_only`.
    /// COMPLEXITY.md row C16. A complete solution is `@exact` ([`exact_preimage`]), which
    /// searches the box at a cost in its points.
    fn project(&mut self, p: Prim, a: Tid, b: Tid, env: Eid, z: &IntervalSet) -> Res {
        let o = op(p, None).expect("binary scalar operator");
        let fa = self.fwd(a, env).ints;
        let fb = self.fwd(b, env).ints;
        let za = revision::backward(o, 0, &fa, &fb, z);
        let zb = revision::backward(o, 1, &fa, &fb, z);
        let ra = self.back_at(a, env, &Demand::Ints(za));
        let rb = self.back_at(b, env, &Demand::Ints(zb));
        let mut r = self.meet(ra, rb);
        r.exact = self.empty(&r);
        r
    }

    fn both_ints(&mut self, a: Tid, b: Tid, env: Eid) -> Res {
        let top = Demand::Ints(IntervalSet::top());
        let ra = self.back_at(a, env, &top);
        let rb = self.back_at(b, env, &top);
        let mut r = self.meet(ra, rb);
        r.exact = self.empty(&r);
        r
    }
}

/// The names bound within a term being closed ([`Tx::close`]).
type Local = imbl::HashMap<Name, Option<Rc<Term>>>;

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
    let (lower, upper) = (End::lower, End::upper);
    match p {
        Prim::Lt => IntervalSet::range(NegInf, upper(c - 1)),
        Prim::Le => IntervalSet::range(NegInf, upper(c)),
        Prim::Gt => IntervalSet::range(lower(c + 1), PosInf),
        Prim::Ge => IntervalSet::range(lower(c), PosInf),
        Prim::Eq => IntervalSet::range(lower(c), upper(c)),
        _ => IntervalSet::single(c as i64).complement_in(&IntervalSet::top()),
    }
}

/// Each piece of `z` moved up by `c`.
fn shift(z: &IntervalSet, c: i128) -> IntervalSet {
    let m = |e: End, end: fn(i128) -> End| match e {
        Fin(v) => end(v as i128 + c),
        e => e,
    };
    IntervalSet::from_pieces(
        z.pieces()
            .iter()
            .map(|&(lo, hi)| (m(lo, End::lower), m(hi, End::upper)))
            .collect(),
    )
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
            let f = if up && f * d != v { f + 1 } else { f };
            if up { End::lower(f) } else { End::upper(f) }
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
    let lower = |e: End| match e {
        Fin(q) => End::lower(q as i128 * c),
        e if c < 0 => -e,
        e => e,
    };
    let upper = |e: End| match e {
        Fin(q) => End::upper(q as i128 * c + m - 1),
        e if c < 0 => -e,
        e => e,
    };
    IntervalSet::from_pieces(
        z.pieces()
            .iter()
            .map(|&(lo, hi)| {
                if c > 0 {
                    (lower(lo), upper(hi))
                } else {
                    (lower(hi), upper(lo))
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
///
/// Complexity tradeoff: the periods between the first and the last are merged into one
/// piece, so the result holds the members with other remainders there and is not exact.
/// Why: listing every period costs pieces in the width of `within` divided by `c`, which is
/// exponential in the bits written. Trigger: `within` spanning more than two periods of `c`.
/// Test: `l01_25_preimage_catalog::random::a_remainder_inverts_to_its_first_and_last_periods_and_one_piece_between`.
/// COMPLEXITY.md row C17. A complete solution would pair the interval with the congruence
/// facet (`x mod c` in `z` as a set of classes), which the reduced product can hold exactly.
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

/// The projection of the points of a listed box at which the term meets the demand: every
/// input's set is listed, each piece holding no more members than its two endpoints (the rule
/// by which a type lists an interval), and at most one input has more than one member, so the
/// points number no more than the endpoints written (docs/thresholds.md, replacement 8). The
/// term's form must show that it ends ([`stage::ends`]). A range is left to the catalog and the
/// linear relation.
///
/// Complexity tradeoff: a box with a range wider than its endpoints, with two or more inputs
/// of several members, or with a term whose ending is not shown is not enumerated; it gets
/// the catalog's and the linear relation's answer, which may be wider. Why: the points of a
/// box are the product of its axes, exponential in the inputs and in the bits of each range,
/// and a term not shown to end may not end. Trigger: those three properties of the box and
/// the term, each relative to what is written, never a constant. Test:
/// `l01_25_preimage_catalog::entries::a_listed_box_is_enumerated_and_a_range_is_not`.
/// COMPLEXITY.md row C18 (thresholds.md replacement 8). A complete solution is `@exact`
/// ([`exact_preimage`]), branch and prune over the box, at a cost in its points.
fn enumerate(term: &Term, dom: &Domains, demand: &Demand) -> Option<Whole> {
    if !stage::ends(term) {
        return None;
    }
    let mut axes: Vec<(Arc<str>, Vec<i64>)> = Vec::new();
    for (k, s) in dom {
        let mut vs = Vec::new();
        for &(lo, hi) in s.pieces() {
            match (lo, hi) {
                (Fin(lo), Fin(hi)) if hi as i128 - lo as i128 <= 1 => vs.extend(lo..=hi),
                _ => return None,
            }
        }
        axes.push((k.clone(), vs));
    }
    if axes.iter().filter(|(_, vs)| vs.len() > 1).count() > 1 {
        return None;
    }
    if axes.iter().any(|(_, vs)| vs.is_empty()) {
        return Some(Whole {
            dom: dom.clone(),
            exact: true,
        });
    }
    on_stack(|| enumerate_on(term, &axes, demand))
}

/// The congruence class of each input that has one, under `@exact`; an input not listed may be
/// any integer.
pub type Classes = BTreeMap<Arc<str>, Congruence>;

/// The preimage of `demand` under `term` when its declaration is annotated `@exact`
/// (DESIGN.md sec:constraints): [`preimage`], and where that is not exact, every input is
/// bounded and the term's form shows that it ends, the projection of the points of the box, in
/// their inputs' `classes`, that meet the demand. Its cost is that of the points the analysis
/// cannot decide in bulk, which the annotation accepts; there is no limit on them. The result
/// is exact when the projections' product holds no point that fails the demand, which a second
/// search, for such a point, decides. A point the evaluator cannot run leaves the result of
/// [`preimage`].
pub fn exact_preimage(
    term: &Term,
    inputs: &Domains,
    classes: &Classes,
    demand: &Demand,
) -> Preimage {
    on_stack(|| {
        let mut p = preimage_of(term, inputs, demand);
        if p.exact {
            // Every point of the box meets the demand, so the classes alone narrow it.
            p.domains = within_classes(&p.domains, classes).unwrap_or_else(|| {
                (p.domains.keys().map(|k| (k.clone(), IntervalSet::empty()))).collect()
            });
            return p;
        }
        if !stage::ends(term) {
            return p;
        }
        let Some((domains, exact)) = exact_search(term, &p.domains, classes, demand) else {
            return p;
        };
        Preimage {
            domains,
            exact,
            enumerated: true,
            stops: p.stops,
            relation: if exact { None } else { p.relation },
            refusal: if exact { None } else { p.refusal },
        }
    })
}

/// A point of the inputs, each input within its class, at which the term meets the demand.
pub type Point = BTreeMap<Arc<str>, i64>;

/// A point of `inputs`, each input within its class, at which `term` meets `demand`:
/// `Some(Some(point))`, or `Some(None)` when there is none. The search of [`exact_preimage`]
/// stops at the first point found, and a box on which the preimage is exact gives its lowest
/// point, so it holds only the boxes on its stack, two for each halving. `None` when an input
/// is unbounded, a point cannot be run, or the term's form does not show that it ends and the
/// preimage alone does not decide.
///
/// Complexity tradeoff: an unbounded input, or a term not shown to end, gives `None` (no
/// answer) even under `@exact`; [`exact_preimage`] likewise keeps the necessary preimage
/// there. Why: a search over an unbounded box need not end, and finding a point of an
/// arbitrary terminating test over unbounded integers is undecidable. Trigger: an input with
/// an infinite end after the preimage, or a recursive or looping term. Tests:
/// `l01_25_preimage_catalog::exact::a_witness_is_the_first_point_found_or_none`,
/// `l01_25_preimage_catalog::exact::exact_preimages_of_ranges`. COMPLEXITY.md row S17. No
/// complete solution exists in general; for linear terms the Presburger solver
/// (`presburger`) decides unbounded inputs.
pub fn witness(
    term: &Term,
    inputs: &Domains,
    classes: &Classes,
    demand: &Demand,
) -> Option<Option<Point>> {
    let lowest = |b: &Domains| -> Point {
        b.iter()
            .map(|(k, s)| match s.bounds() {
                Some((Fin(lo), _)) => (k.clone(), lo),
                _ => unreachable!("a searched box is bounded"),
            })
            .collect()
    };
    if inputs
        .values()
        .any(|s| !s.is_empty() && !matches!(s.bounds(), Some((Fin(_), Fin(_)))))
    {
        return None;
    }
    let Some(dom) = within_classes(inputs, classes) else {
        return Some(None);
    };
    if !stage::ends(term) {
        let r = preimage_of(term, &dom, demand);
        let narrowed: Domains = dom
            .iter()
            .map(|(k, s)| (k.clone(), s.meet(&r.domains[k])))
            .collect();
        return match within_classes(&narrowed, classes) {
            None => Some(None),
            Some(n) if r.exact => Some(Some(lowest(&n))),
            Some(_) => None,
        };
    }
    /// The search for a point: the lowest point of the first box that meets the demand.
    struct First<F>(Option<Point>, F);
    impl<F: Fn(&Domains) -> Point> Search for First<F> {
        fn all(&mut self, b: &Domains) -> bool {
            self.0 = Some((self.1)(b));
            true
        }
    }
    on_stack(|| {
        let mut first = First(None, lowest);
        branch(term, dom, classes, demand, &mut first)?;
        Some(first.0)
    })
}

/// The projection of the points of `dom` in `classes` meeting `demand`, and whether their box
/// holds no point that fails it; `None` when an input is unbounded or a point cannot be run.
fn exact_search(
    term: &Term,
    dom: &Domains,
    classes: &Classes,
    demand: &Demand,
) -> Option<(Domains, bool)> {
    let Some(dom) = within_classes(dom, classes) else {
        let empty = dom
            .keys()
            .map(|k| (k.clone(), IntervalSet::empty()))
            .collect();
        return Some((empty, true));
    };
    if dom
        .values()
        .any(|s| !matches!(s.bounds(), Some((Fin(_), Fin(_)))))
    {
        return None;
    }
    /// The search for every point: the projections of the boxes met so far, each input's
    /// the join of its parts; a box within them adds nothing.
    struct Met(Domains);
    impl Search for Met {
        fn skip(&self, b: &Domains) -> bool {
            b.iter().all(|(k, s)| s.is_subset(&self.0[k]))
        }
        fn all(&mut self, b: &Domains) -> bool {
            for (k, s) in b {
                let joined = self.0[k].join(s);
                self.0.insert(k.clone(), joined);
            }
            false
        }
    }
    let mut met = Met(dom
        .keys()
        .map(|k| (k.clone(), IntervalSet::empty()))
        .collect());
    branch(term, dom, classes, demand, &mut met)?;
    let met = met.0;
    let several = met.values().filter(|s| !is_point(s)).count();
    if met.values().any(IntervalSet::is_empty) || several <= 1 {
        return Some((met, true));
    }
    let fails = match demand {
        Demand::Bool(b) => Demand::Bool(!b),
        Demand::Ints(z) => Demand::Ints(z.complement_in(&IntervalSet::top())),
    };
    /// The search for any point.
    struct Any;
    impl Search for Any {
        fn all(&mut self, _: &Domains) -> bool {
            true
        }
    }
    let found = branch(term, met.clone(), classes, &fails, &mut Any)?;
    Some((met, !found))
}

/// What a search of [`branch`] does with the boxes: which it skips, and what it takes from each
/// box whose every point meets the demand.
trait Search {
    /// Whether `b` adds nothing to what the search has found.
    fn skip(&self, _b: &Domains) -> bool {
        false
    }

    /// Takes `b`, whose every point meets the demand; `true` stops the search.
    fn all(&mut self, b: &Domains) -> bool;
}

/// Branch and prune over `root`: each box not skipped by `search` is narrowed by [`preimage_in`] and
/// its inputs' classes, and dropped when empty, given to `search` when every point meets
/// `demand`, and otherwise halved on its widest input; a single point is evaluated. Every box
/// is smaller than the one it was split from, so the search ends. `Some(true)` when `search`
/// stopped it, `None` when a point cannot be run.
fn branch(
    term: &Term,
    root: Domains,
    classes: &Classes,
    demand: &Demand,
    search: &mut dyn Search,
) -> Option<bool> {
    // The classes hold for the whole search, so their arithmetic is read once: it can decide
    // the term on every point of the box, as `x * x mod 10 == 9` with `x` in `5 mod 10`.
    match classes_decide(term, classes, demand) {
        Some(false) => return Some(false),
        Some(true) => return Some(search.all(&root)),
        None => {}
    }
    // The term is numbered once for the whole search; each box is a run of its own.
    let mut tx = Tx::new();
    let top = tx.terms.add(term);
    let mut boxes = vec![root];
    while let Some(b) = boxes.pop() {
        if search.skip(&b) {
            continue;
        }
        let b = if b.values().all(is_point) {
            b
        } else {
            let r = preimage_in(&mut tx, top, term, &b, demand);
            let narrowed: Domains = b
                .iter()
                .map(|(k, s)| (k.clone(), s.meet(&r.domains[k])))
                .collect();
            let Some(n) = within_classes(&narrowed, classes) else {
                continue;
            };
            if r.exact {
                if search.all(&n) {
                    return Some(true);
                }
                continue;
            }
            n
        };
        if b.values().all(is_point) {
            let mut t = term.clone();
            for (k, s) in b.iter().rev() {
                let Some((Fin(v), _)) = s.bounds() else {
                    unreachable!("a point is finite")
                };
                t = Term::Let(k.clone(), Arc::new(Term::Lit(Value::Int(v))), Arc::new(t));
            }
            let v = Evaluator::new(World::new()).run(&t).ok()?;
            if demand.holds(&v) && search.all(&b) {
                return Some(true);
            }
            continue;
        }
        let (k, lo, hi) = b
            .iter()
            .filter_map(|(k, s)| match s.bounds() {
                Some((Fin(lo), Fin(hi))) if lo < hi => Some((k, lo, hi)),
                _ => None,
            })
            .max_by_key(|(_, lo, hi)| *hi as i128 - *lo as i128)
            .expect("a box of more than one point has an input of more than one value");
        let mid = (lo as i128 + (hi as i128 - lo as i128) / 2) as i64;
        for half in [
            IntervalSet::range(Fin(mid + 1), PosInf),
            IntervalSet::range(NegInf, Fin(mid)),
        ] {
            let mut h = b.clone();
            h.insert(k.clone(), b[k].meet(&half));
            if let Some(h) = within_classes(&h, classes) {
                boxes.push(h);
            }
        }
    }
    Some(false)
}

/// Whether every integer point with each input in its class meets `demand` under `term`
/// (`Some(true)`), none does (`Some(false)`), or the classes do not decide.
fn classes_decide(term: &Term, classes: &Classes, demand: &Demand) -> Option<bool> {
    match demand {
        Demand::Bool(d) => class_test(term, classes).map(|b| b == *d),
        Demand::Ints(z) => match class_of(term, classes)? {
            Congruence::Bottom => Some(false),
            Congruence::Class {
                modulus: 0,
                residue,
            } => Some(z.contains(residue)),
            _ => None,
        },
    }
}

/// The value of the test `term` at every point with each input in its class, if one value.
fn class_test(term: &Term, classes: &Classes) -> Option<bool> {
    let Term::Prim(p, xs) = term else {
        return match term {
            Term::Lit(Value::Bool(b)) => Some(*b),
            Term::Let(x, _, body) => class_test(body, &unbound(classes, x)),
            _ => None,
        };
    };
    match (p, xs.as_slice()) {
        (Prim::Not, [a]) => class_test(a, classes).map(|b| !b),
        (Prim::And, [a, b]) => match (class_test(a, classes), class_test(b, classes)) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        },
        (Prim::Or, [a, b]) => match (class_test(a, classes), class_test(b, classes)) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        },
        (Prim::Eq | Prim::Ne, [a, b]) => {
            let (x, y) = (class_of(a, classes)?, class_of(b, classes)?);
            let eq = match (x, y) {
                (
                    Congruence::Class {
                        modulus: 0,
                        residue: u,
                    },
                    Congruence::Class {
                        modulus: 0,
                        residue: v,
                    },
                ) => u == v,
                _ if x.meet(&y) == Congruence::Bottom => false,
                _ => return None,
            };
            Some(eq == (*p == Prim::Eq))
        }
        _ => None,
    }
}

/// The class of the integer `term` at every point with each input in its class, by Granger's
/// arithmetic of congruences; `None` for a form it does not cover or a class too fine to hold.
fn class_of(term: &Term, classes: &Classes) -> Option<Congruence> {
    // A class as (modulus, residue) in i128, and back, `None` when it leaves u64 and i64.
    let parts = |c: Congruence| match c {
        Congruence::Bottom => None,
        Congruence::Class { modulus, residue } => Some((modulus as i128, residue as i128)),
    };
    let class = |m: i128, r: i128| -> Option<Congruence> {
        let r = if m == 0 { r } else { r.rem_euclid(m) };
        Some(Congruence::new(
            u64::try_from(m).ok()?,
            i64::try_from(r).ok()?,
        ))
    };
    fn gcd(a: i128, b: i128) -> i128 {
        if b == 0 { a.abs() } else { gcd(b, a % b) }
    }
    match term {
        Term::Lit(Value::Int(v)) => Some(Congruence::single(*v)),
        Term::Var(x) => Some(classes.get(x).copied().unwrap_or(Congruence::new(1, 0))),
        Term::Let(x, _, body) => class_of(body, &unbound(classes, x)),
        Term::Prim(p, xs) => match (p, xs.as_slice()) {
            (Prim::Neg, [a]) => {
                let (m, r) = parts(class_of(a, classes)?)?;
                class(m, -r)
            }
            (Prim::Add | Prim::Sub, [a, b]) => {
                let ((m, r), (n, s)) =
                    (parts(class_of(a, classes)?)?, parts(class_of(b, classes)?)?);
                class(gcd(m, n), if *p == Prim::Add { r + s } else { r - s })
            }
            (Prim::Mul, [a, b]) => {
                // (r mod m)(s mod n) is rs mod gcd(mn, rn, sm).
                let ((m, r), (n, s)) =
                    (parts(class_of(a, classes)?)?, parts(class_of(b, classes)?)?);
                let g = gcd(gcd(m.checked_mul(n)?, r.checked_mul(n)?), s.checked_mul(m)?);
                class(g, r.checked_mul(s)?)
            }
            (Prim::Mod, [a, Term::Lit(Value::Int(k))]) if *k > 0 => {
                // `x mod k` is Euclidean, so in 0..k; when k divides the modulus it is one value,
                // and otherwise it is x's residue modulo gcd(m, k).
                let (m, r) = parts(class_of(a, classes)?)?;
                let k = *k as i128;
                if m % k == 0 {
                    class(0, r.rem_euclid(k))
                } else {
                    class(gcd(m, k), r)
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// `classes` without `x`, which a `let` has bound to a value the classes do not hold.
fn unbound(classes: &Classes, x: &str) -> Classes {
    let mut c = classes.clone();
    c.remove(x);
    c
}

/// `dom` with each input's set tightened to its class, or `None` when one is then empty.
fn within_classes(dom: &Domains, classes: &Classes) -> Option<Domains> {
    let d: Domains = dom
        .iter()
        .map(|(k, s)| match classes.get(k) {
            Some(c) => (k.clone(), reduce_congruence(s, c).0),
            None => (k.clone(), s.clone()),
        })
        .collect();
    (!is_empty(&d)).then_some(d)
}

/// Whether `s` is one value.
fn is_point(s: &IntervalSet) -> bool {
    matches!(s.bounds(), Some((Fin(a), Fin(b))) if a == b)
}

/// The enumeration of [`enumerate`] over `axes`, each point evaluated in turn.
fn enumerate_on(term: &Term, axes: &[(Arc<str>, Vec<i64>)], demand: &Demand) -> Option<Whole> {
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
        let v = Evaluator::new(World::new()).run(&t).ok()?;
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
                return Some(Whole {
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
