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
//! - `-x`, `abs` and `^` by a constant invert exactly at their endpoints, by the tonicity of
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
//! result that is still not exact over a listed box (every input's set one whose members the
//! source lists, `x: {0, 1, 2}` and not `x: int[0..=2]` whatever its width, at most one input
//! with more than one member; [`preimage_listed`]), of a term whose form shows that it ends,
//! is enumerated: the term is run at each point, and the result is the projection of the points
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

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Pattern, Prim, Shared, Term, Value, World, eval};

use End::{Fin, NegInf, PosInf};
use zed_kernel::frames::{Deep, Stack};
use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::landmarks::Landmarks;
use zedc_lattice::lattice::{Congruence, Lattice};
use zedc_lattice::revision::{self, Exponent, Op, Tonicity, reduce_congruence};
use zedc_presburger::presburger::{self, Con, Formula, Joining, Lin, Mark, Refusal, Relation};
use zedc_stage::stage;

use crate::divisors::{EMPTY, Set, Sets as DivisorSets};
use crate::shared_ints::Ints;
pub use crate::shared_ints::forward_pieces;

/// The box of a term whose value `v` is known: every point when `v` meets the demand, none
/// otherwise.
fn decided(d: &Demand, v: &Value) -> Res {
    if d.holds(v) { Res::all() } else { Res::none() }
}

/// An interval per input name.
pub type Domains = BTreeMap<Arc<str>, IntervalSet>;

/// The input names whose domains are sets the source lists member by member
/// ([`preimage_listed`]).
pub type Listed = BTreeSet<Arc<str>>;

/// No input listed.
const NONE_LISTED: &Listed = &Listed::new();

/// What the term's value must be.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Demand {
    /// An integer in the set.
    Ints(IntervalSet),
    /// The boolean.
    Bool(bool),
}

impl Demand {
    /// Whether `v` meets the demand, exact at any magnitude.
    pub fn holds(&self, v: &Value) -> bool {
        match (self, v) {
            (Demand::Ints(z), Value::Int(n)) => z.contains(*n),
            (Demand::Ints(z), Value::Big(n)) => z.contains_end(&Fin(Num::from(&**n))),
            (Demand::Bool(w), Value::Bool(b)) => w == b,
            _ => false,
        }
    }
}

/// Why the transfer stopped.
#[derive(Clone, PartialEq, Eq, Debug)]
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
    /// Naive version: the transfer read through the loop, once per iteration, which need not end;
    /// used: the stop, O(1) at the loop, with the whole box as the answer (necessary only).
    Outside,
    /// A call of a lambda whose call is already being read.
    Recursion,
}

/// A reported stop: its kind and the term it stopped at. The term is held, not printed: its
/// text is made only when the stop is shown.
#[derive(Clone, PartialEq, Debug)]
pub struct Stop {
    /// Why.
    pub kind: StopKind,
    /// The term, as the transfer was given it.
    pub term: Shared,
}

/// By the kind and the primitive or name it holds, as [`PartialEq`] compares them: [`Prim`]
/// has no hash of its own, and no primitive carries data, so its discriminant is all of it.
impl std::hash::Hash for StopKind {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        std::mem::discriminant(self).hash(h);
        match self {
            StopKind::String(p) => std::mem::discriminant(p).hash(h),
            StopKind::Foreign(n) => n.hash(h),
            StopKind::Outside | StopKind::Recursion => {}
        }
    }
}

impl fmt::Display for Stop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StopKind::String(p) => write!(
                f,
                "string operation `{}` stops the transfer at ",
                p.written()
            )?,
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

impl Preimage {
    /// The stops as printed, each text once, in the order they were reported. A stop is kept
    /// for each kind and term the transfer stopped at, so two copies of one term (cloned, not
    /// shared) are two stops; their texts are made here, where copies that print alike merge.
    pub fn stop_texts(&self) -> Vec<String> {
        let mut seen = HashSet::new();
        (self.stops.iter())
            .map(Stop::to_string)
            .filter(|s| seen.insert(s.clone()))
            .collect()
    }
}

/// The value of the closed term `t`, if its form shows that it ends ([`stage::ends`]) and it
/// evaluates. A term not shown to end stays unevaluated, since a program may loop forever.
fn run_closed(t: &Term) -> Option<Value> {
    if !stage::ends(t) {
        return None;
    }
    eval(t).ok()
}

/// The preimage of `demand` under `term`, whose free names in `inputs` range over their
/// domains, no domain one whose members the source lists ([`preimage_listed`]).
pub fn preimage(term: &Term, inputs: &Domains, demand: &Demand) -> Preimage {
    preimage_of(term, inputs, NONE_LISTED, demand)
}

/// [`preimage`], the domains of the names in `listed` being sets whose members the source
/// lists (`x: {0, 1, 2}`), each holding no member the source does not list: a box over them
/// may be enumerated (`enumerate`). A domain the source gives as a range (`int[0..=2]`) is
/// not listed, whatever its width.
pub fn preimage_listed(
    term: &Term,
    inputs: &Domains,
    listed: &Listed,
    demand: &Demand,
) -> Preimage {
    preimage_of(term, inputs, listed, demand)
}

/// The work of [`preimage`] and [`preimage_listed`].
fn preimage_of(term: &Term, inputs: &Domains, listed: &Listed, demand: &Demand) -> Preimage {
    if let Some(p) = order_with_literal(term, inputs, demand) {
        p
    } else {
        let mut tx = Tx::new();
        let root = tx.terms.add(term);
        preimage_in(&mut tx, root, term, inputs, listed, demand)
    }
}

/// The preimage of the outcome `demand` under `term` when the term orders its one input
/// against an integer literal (`x < k`, `k >= x`), the input's domain not empty: the domain
/// met with the half-line on which the test has that outcome, exact; the box holds no point,
/// every input empty, when that meet is empty. `None` for any other term or demand.
// Complexity tradeoff: naive version, the term read by the general path ([`preimage_in`]):
// a transfer state made, the split by remainders tried, the backward transfer run, about
// 68,000 instructions a test (COMPLEXITY.md row PA-bind-cost). Used: this form of one input
// is read at once, one meet, O(p) for `p` pieces of the domain; it gives what the general path
// gives, compared in `an_order_with_a_literal_has_the_preimage_of_the_general_path`. Any other
// form takes the general path as before.
fn order_with_literal(term: &Term, inputs: &Domains, demand: &Demand) -> Option<Preimage> {
    let Demand::Bool(outcome) = demand else {
        return None;
    };
    let (x, half) = order_set(term, *outcome)?;
    let (name, dom) = inputs.iter().next()?;
    if inputs.len() != 1 || name != x || dom.is_empty() {
        return None;
    }
    Some(Preimage {
        domains: Domains::from([(x.clone(), dom.meet(&half))]),
        exact: true,
        enumerated: false,
        stops: Vec::new(),
        relation: None,
        refusal: None,
    })
}

/// For a test `x op k` or `k op x` of a name `x` against an integer literal `k` by an order
/// `op`, the name and the integers on which the test has the outcome `outcome`: the half-line
/// the backward transfer finds ([`Walk::back_compare`] after [`Walk::back_prim`]). `None` for
/// any other term.
fn order_set(term: &Term, outcome: bool) -> Option<(&Arc<str>, IntervalSet)> {
    let Term::Prim(p @ (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge), a) = term else {
        return None;
    };
    let p = if outcome { *p } else { negate(*p) };
    match a.as_slice() {
        [Term::Var(x), Term::Lit(Value::Int(k))] => Some((x, ray(p, *k))),
        [Term::Lit(Value::Int(k)), Term::Var(x)] => Some((x, ray(mirror(p), *k))),
        _ => None,
    }
}

/// The summary ([`Pa`]) of `if x op k then a else b` for a test of an input `x` among
/// `inputs` against an integer literal by an order ([`order_set`]) and integer literals `a`
/// and `b`, as the transfer finds it ([`Walk::pa_if`]): the constant of the one arm taken
/// over `x`'s domain, or both sliced to the stretches that take each ([`select`]); the inner
/// `None` where the transfer finds no summary. `None` for any other term. The caller checks
/// that the box holds a point (`Begun::void`), as [`Walk::pa`] does.
fn order_if(t: &Term, inputs: &Domains) -> Option<Option<Pa>> {
    let Term::If(g, a, b) = t else {
        return None;
    };
    let (Term::Lit(Value::Int(a)), Term::Lit(Value::Int(b))) = (&**a, &**b) else {
        return None;
    };
    let (x, yes) = order_set(g, true)?;
    let dom = inputs.get(x)?;
    let (_, no) = order_set(g, false)?;
    let (yes, no) = (dom.meet(&yes), dom.meet(&no));
    let (pa, pb) = (Pa::Const(Int::from(*a)), Pa::Const(Int::from(*b)));
    Some(match (yes.is_empty(), no.is_empty()) {
        (false, true) => Some(pa),
        (true, false) => Some(pb),
        (false, false) => select(x, dom, [Some((&yes, &pa)), Some((&no, &pb))]),
        (true, true) => None,
    })
}

/// The inputs on which the piecewise-affine summary of `term` ([`Pa`]) takes a value in `z`,
/// read without the transfer around it, or `None` when the summary of `term` or its inversion
/// is given up: for the tests that check where the summary exists and what it says.
#[doc(hidden)]
pub fn summary_preimage(term: &Term, inputs: &Domains, z: &IntervalSet) -> Option<Domains> {
    let mut tx = Tx::new();
    let root = tx.terms.add(term);
    let marks = tx.landmarks(inputs, &Demand::Ints(z.clone()));
    tx.start(inputs, marks);
    let pa = tx.pa(root, ROOT)?;
    let r = tx.invert_pa(&pa, z)?;
    Some(tx.whole(&r))
}

/// The box over `inputs` of the points where `term` meets `demand`, read by the backward
/// transfer alone, the names of `lets` read through their summaries ([`LetPa`]): a name of
/// `lets` is no input, and the inputs its summary reads are among `inputs`. A test of a name
/// bound by a `let` (`x == 1` after `y = n + 1; x = y + n`) narrows the input the name is
/// computed from (`n` to 0), and one of a name over several inputs (`x >= 0` after
/// `x = n + k`) narrows each by the bounds of the others (`Tx::invert_sep`). The stages
/// after the transfer (the split by remainders, the linear relation, enumeration) read the
/// term itself, whose names of `lets` they would take for inputs, and are not run: the caller
/// meets this box with the preimage of the term over the names themselves ([`preimage`]).
pub fn let_preimage(term: &Term, inputs: &Domains, lets: Lets, demand: &Demand) -> Domains {
    let mut tx = Tx::new();
    tx.lets = lets;
    let root = tx.terms.add(term);
    let marks = tx.landmarks(inputs, demand);
    tx.start(inputs, marks);
    let r = tx.back(root, ROOT, demand);
    tx.whole(&r)
}

/// [`let_preimage`], giving only the inputs the box narrows, each with its set, or `None` when
/// the box holds no point; the other inputs keep their domains. The inputs of a summary read
/// through a tree of its terms' bounds ([`LetIn::read`]) are not among `inputs`: a test of a
/// name over `k` such inputs then costs those it narrows, each `O(log k)`, and not all `k`
/// (`Tx::invert_read`, item PA-letpre-linear). The reads are made in one scope
/// ([`SummaryRead::scope_ints`]); an input among `inputs` that a read holds is read over the
/// domain `inputs` gives it, each such costing `O(log k)` a read.
pub fn let_narrowing(
    term: &Term,
    inputs: &Domains,
    lets: Lets,
    demand: &Demand,
) -> Option<Domains> {
    #[cfg(feature = "counts")]
    counts::INPUTS.set(counts::INPUTS.get() + inputs.len() as u64);
    let mut tx = Tx::new();
    tx.lets = lets;
    let root = tx.terms.add(term);
    let marks = tx.landmarks(inputs, demand);
    tx.start(inputs, marks);
    let r = tx.back(root, ROOT, demand);
    tx.narrowed(&r)
}

/// The summary of the term `e` a `let` binds ([`LetPa`]), its free names in `inputs` ranging
/// over their domains and those of `lets` read through their summaries; `None` when a term it
/// adds has no summary over one input. The summaries of the terms it adds are summed by input
/// (`Sep`): `n + k` is a summary over `n` and `k`. Its sums of names of `lets` are kept
/// unsummed, so that each binding costs its own term and not the summaries it adds
/// ([`LetPa`]).
pub fn let_summary(e: &Term, inputs: &Domains, lets: Lets) -> Option<LetPa> {
    let mut parts: Vec<(Int, LetPa)> = Vec::new();
    let mut rest: Vec<(Int, &Term)> = Vec::new();
    let mut constant = Int::ZERO;
    let mut todo: Vec<(Int, &Term)> = vec![(Int::ONE, e)];
    while let Some((c, t)) = todo.pop() {
        let lit = |t: &Term| match t {
            Term::Lit(Value::Int(k)) => Some(Int::from(*k)),
            _ => None,
        };
        match t {
            Term::Prim(Prim::Add, a) if a.len() == 2 => {
                todo.extend([(c.clone(), &a[0]), (c, &a[1])]);
            }
            Term::Prim(Prim::Sub, a) if a.len() == 2 => {
                todo.extend([(c.clone(), &a[0]), (-&c, &a[1])]);
            }
            Term::Prim(Prim::Neg, a) if a.len() == 1 => todo.push((-&c, &a[0])),
            Term::Prim(Prim::Mul, a) if a.len() == 2 && lit(&a[0]).is_some() => {
                todo.push((&c * &lit(&a[0])?, &a[1]));
            }
            Term::Prim(Prim::Mul, a) if a.len() == 2 && lit(&a[1]).is_some() => {
                todo.push((&c * &lit(&a[1])?, &a[0]));
            }
            Term::Lit(Value::Int(k)) => constant = &constant + &(&c * &Int::from(*k)),
            Term::Var(x) if let Some(l) = lets.get(x) => parts.push((c, l.summary.clone())),
            _ => rest.push((c, t)),
        }
    }
    let mut sum = Sep::constant(constant);
    if rest.is_empty() {
        return Some(LetPa::new(parts, sum));
    }
    // A box of no point has no summary ([`Walk::pa`]).
    let begun = begin(&lets, inputs);
    if begun.void {
        return None;
    }
    // Complexity tradeoff: naive version, every term read by the transfer: a transfer state
    // made, the landmarks of its integers found, the terms added and walked, about 170,000
    // instructions a binding `t_j = t_(j-1) + if n > j then 2 else 1` (COMPLEXITY.md row
    // PA-bind-cost). Used: an `if` of two integer literals guarded by an order of an input
    // against an integer literal is summarized at once ([`order_if`]), two meets and the
    // slicing of [`Walk::pa_select`], O(p) for `p` pieces of the input's domain; the
    // transfer is made, as before and over every term, only when some term is not of that
    // form. The summary is the transfer's, compared in
    // `an_if_of_literals_on_an_order_has_the_summary_of_the_transfer`.
    let mut lets = Some(lets);
    let mut transfer: Option<(Tx, Vec<Tid>)> = None;
    for (i, (c, t)) in rest.iter().enumerate() {
        let pa = match order_if(t, inputs) {
            Some(pa) => pa?,
            None => {
                let (tx, roots) = transfer.get_or_insert_with(|| {
                    let mut tx = Tx::new();
                    tx.lets = lets.take().expect("the transfer is made once");
                    let roots = rest.iter().map(|(_, t)| tx.terms.add(t)).collect();
                    let marks = tx.landmarks(inputs, &Demand::Bool(true));
                    tx.start_from(&begun, marks);
                    (tx, roots)
                });
                tx.pa(roots[i], ROOT)?
            }
        };
        sum.add_pa(pa.affine(c.clone(), 0), None);
    }
    Some(LetPa::new(parts, sum))
}

/// [`preimage`] of `term`, which is `root` in `tx`'s terms.
fn preimage_in(
    tx: &mut Tx<'_>,
    root: Tid,
    term: &Term,
    inputs: &Domains,
    listed: &Listed,
    demand: &Demand,
) -> Preimage {
    let marks = tx.landmarks(inputs, demand);
    // A split by remainders found exact over the whole box is the preimage. The transfer over
    // the box, run first otherwise, reads a guard on a remainder inexactly when its set spans
    // more than two periods (row C17), and then reads a chain of such guards once for each
    // demand the chain's arms shift, `O(k^2)` for `k` guards; in a class the chain is read
    // once for all classes ([`Walk::by_class`]).
    //
    // Complexity tradeoff: the split before the first transfer is given up, and the transfer
    // runs first as without it, when the box holds the split input within two periods (the
    // transfer reads every guard on the remainder exactly) or when a class's run reads a guard
    // on the remainder by itself rather than from the summary over every class (a `min` arm,
    // an `if` with boolean arms): run first in those cases the split would cost one transfer
    // of the chain per class, `O(G n)` for `G` classes, where the transfer alone may be exact
    // in `O(n)`. Given up: those inputs get the transfer's answer, and the split after it
    // when that is inexact, as before S22e-quad; at most one class's run is spent. Trigger:
    // the input's domain within two periods of the modulus, or a guard on the remainder that
    // [`Walk::by_class`] does not read. Test:
    // `l01_25_preimage_catalog::s22::remainders_read_by_each_class_keep_the_transfer_first_scales`,
    // COMPLEXITY.md row S22e-quad. A complete solution would hold the congruence facet in
    // the backward transfer's sets, so that one transfer carries every class at once.
    //
    // A split that finds a mixed stretch over many periods ([`Split::Wide`]) runs once more over
    // the box it found, which holds every point of the preimage, so an exact answer there is
    // the preimage. Otherwise it is kept, and the transfer and the split over the transfer's
    // box run as without it: over that narrower box the split may be exact where over the
    // whole box it is not (`many_remainders` below `i mod 1024 == 0`, row S22e-wide). When
    // neither is exact the kept answer is the preimage, its box met with the transfer's, and
    // the linear stage is not run. The split over the found box comes first because the
    // transfer reads a guard on the remainder over more than two periods inexactly, so the
    // `if` it guards has no summary ([`Walk::pa_if`]) and the term its arms share is read once
    // for each demand they send it, a number that grows with the depth of a chain (row
    // S22-order-chain); the split reads each level once ([`Walk::by_class`]).
    //
    // Complexity tradeoff: when the split over the found box is not exact, it was one more
    // split, `O(G n log n)` as the first, spent for nothing. Why: whether it is exact is
    // known only by running it. Trigger: a split that is wide over the whole box and not
    // exact over the box it finds. Test:
    // `store::preimage::tests::a_chain_split_by_two_classes_is_read_in_time_near_its_length`,
    // deferred to plan row PRE-class-int in wt/scratch/deferred-tests/PRE-class-int.rs.
    // COMPLEXITY.md row S22-order-chain.
    let mut whole_tried = false;
    let mut early = None;
    if !is_empty(inputs) {
        match split_residues(tx, root, inputs, demand, &marks, true) {
            Split::Exact(dom) => {
                return Preimage {
                    domains: dom,
                    exact: true,
                    enumerated: false,
                    stops: Vec::new(),
                    relation: None,
                    refusal: None,
                };
            }
            Split::Wide(dom, found) => {
                if dom != *inputs
                    && let Split::Exact(exact) =
                        split_residues(tx, root, &dom, demand, &marks, false)
                {
                    return Preimage {
                        domains: exact,
                        exact: true,
                        enumerated: false,
                        stops: Vec::new(),
                        relation: None,
                        refusal: None,
                    };
                }
                early = Some((dom, found));
                whole_tried = true;
            }
            Split::NotExact => whole_tried = true,
            Split::Deferred => {}
        }
    }

    let begun = tx.begin(inputs);
    tx.start_from(&begun, marks.clone());
    let r = tx.back(root, ROOT, demand);
    let mut r = Whole {
        dom: tx.whole(&r),
        exact: r.exact,
    };
    let stops = std::mem::take(&mut tx.run.stops);
    let mut enumerated = false;
    if !r.exact && !is_empty(&r.dom) {
        // Complexity tradeoff: naive version, the forward run over a box the backward run
        // did not narrow begins afresh, so it makes again every set of integers the backward
        // run made: for `i * i * j * i * j * … <= 1` the bounds of each product, `O(n)` bits
        // at depth `n`, `O(n^2)` bits in all, twice. Used: the box is the same, so the run
        // begins from the same shared domains and keeps the backward run's sets
        // ([`SharedInts`]), each a function of its key alone, as the runs of
        // [`split_residues`] keep them; a narrowed box begins afresh as before. The test
        // `r.dom == *inputs` is `O(p)` for the `p` pieces of the box. Test:
        // `l01_25_preimage_catalog::powers::reading_a_product_as_a_power_is_linear_in_its_factors`;
        // COMPLEXITY.md row PA-bind-cost.
        if r.dom == *inputs {
            let ints = std::mem::take(&mut tx.run.ints);
            tx.start_from(&begun, marks.clone());
            tx.run.ints = ints;
        } else {
            tx.start(&r.dom, marks.clone());
        }
        if tx.fwd(root, ROOT).meets(demand) {
            r.exact = true;
        }
    }
    if !r.exact
        && !is_empty(&r.dom)
        // The split over the whole box was tried above.
        && !(whole_tried && r.dom == *inputs)
    {
        match split_residues(tx, root, &r.dom, demand, &marks, false) {
            Split::Exact(dom) => r = Whole { dom, exact: true },
            Split::Wide(dom, found) => return wide(term, dom, found, listed, demand, stops),
            Split::NotExact | Split::Deferred => {}
        }
    }
    if !r.exact
        && let Some((dom, found)) = early
    {
        let dom = dom.into_iter().map(|(k, v)| {
            let v = v.meet(&r.dom[&k]);
            (k, v)
        });
        return wide(term, dom.collect(), found, listed, demand, stops);
    }
    let (mut relation, mut refusal) = (None, None);
    if !r.exact
        && !is_empty(&r.dom)
        && let Some((rel, found)) = linear(tx, root, &r.dom, demand)
    {
        match found {
            Ok((dom, exact, why)) => {
                r = Whole { dom, exact };
                relation = (!exact).then_some(rel);
                refusal = why;
            }
            Err((dom, why)) => {
                r = Whole { dom, exact: false };
                refusal = Some(why);
            }
        }
    }
    if !r.exact
        && let Some(e) = enumerate(term, &r.dom, listed, demand)
    {
        r = e;
        enumerated = true;
        if r.exact {
            relation = None;
            refusal = None;
        }
    }
    Preimage {
        domains: r.dom,
        exact: r.exact,
        enumerated,
        stops,
        relation,
        refusal,
    }
}

/// The preimage of a split by remainders over many periods ([`Split::Wide`]): its box, not
/// exact, with the classes' relation and the refusal that left the box wider, or the box
/// listed when it can be ([`enumerate`]). The linear stage is not run on the term
/// ([`split_residues`] says why).
fn wide(
    term: &Term,
    dom: Domains,
    (rel, why): ClassRelation,
    listed: &Listed,
    demand: &Demand,
    stops: Vec<Stop>,
) -> Preimage {
    let mut r = Whole { dom, exact: false };
    let mut enumerated = false;
    if let Some(e) = enumerate(term, &r.dom, listed, demand) {
        r = e;
        enumerated = true;
    }
    Preimage {
        domains: r.dom,
        exact: r.exact,
        enumerated,
        stops,
        relation: (!r.exact).then_some(rel),
        refusal: if r.exact { None } else { why },
    }
}

/// The box `dom` narrowed to the projection of the classes' relation `rel` onto its inputs,
/// with the refusal for which a set is wider than the projection, as the linear stage projects
/// its own relation ([`linear`]), here with one pair of auxiliary variables for the split
/// input. Where the solver refuses a projection, the input keeps the box stage's bounds
/// ([`boxed_projections`]).
fn project_classes(rel: &Relation, dom: &Domains) -> (Domains, Option<Refusal>) {
    let within = |d: &Domains| -> Formula {
        let parts = d
            .iter()
            .map(|(k, v)| presburger::member(&presburger::Atom::Sym(k.clone()), v))
            .collect();
        Formula::and(parts)
    };
    let mentioned = rel.body.atoms();
    let syms: Vec<presburger::Atom> = dom
        .keys()
        .map(|k| presburger::Atom::Sym(k.clone()))
        .filter(|a| mentioned.contains(a))
        .collect();
    // The box's hull, so that the body is the only disjunction; the projections are met with
    // the box below.
    let hull = dom.iter().map(|(k, v)| (k.clone(), v.hull())).collect();
    let whole = Formula::and(vec![rel.defined(), within(&hull), rel.body.clone()]);
    let (out, why, _) = boxed_projections(&whole, dom, &syms);
    (out, why)
}

/// Each input of `dom` met with its set in the projection of `whole` onto `syms`, the inputs
/// `whole` mentions ([`presburger::project_each_boxed`]), an input not among them keeping its
/// box; the first cause for which a set is wider than the projection; and the cause for which
/// the solver refused a projection, where it did, whose input then keeps the bounds the box
/// stage gives the rows of `whole` (DESIGN step L1.38).
fn boxed_projections(
    whole: &Formula,
    dom: &Domains,
    syms: &[presburger::Atom],
) -> (Domains, Option<Refusal>, Option<Refusal>) {
    let got = presburger::project_each_boxed(whole, syms);
    let why = got.cause();
    let refused = (got.whole.clone()).or_else(|| got.each.iter().find_map(|(_, e)| e.clone()));
    let mut each = got.each.into_iter().zip(syms).peekable();
    let mut out = Domains::new();
    for (k, v) in dom {
        let p = match each.next_if(|(_, s)| **s == presburger::Atom::Sym(k.clone())) {
            Some(((x, _), _)) => x.meet(v),
            None => v.clone(),
        };
        out.insert(k.clone(), p);
    }
    (out, why, refused)
}

/// The relation of the classes of a split by remainders over many periods, exact on its box,
/// and the refusal that left the box wider ([`Split::Wide`]).
type ClassRelation = (Relation, Option<Refusal>);

/// What [`split_residues`] found.
enum Split {
    /// The preimage, exact.
    Exact(Domains),
    /// The preimage within the box, not exact, the relation of the classes that is, and the
    /// refusal that left the box wider: a stretch where some classes keep their points and
    /// others do not spans more than two periods ([`split_classes`]).
    Wide(Domains, ClassRelation),
    /// No split applies, or it is not exact.
    NotExact,
    /// The split before the first transfer was given up for the transfer to run first
    /// ([`preimage_in`]).
    Deferred,
}

/// The preimage within `dom` by classes of remainders ([`Split::Exact`]). When `early`, the
/// split is run before the first transfer, and is [`Split::Deferred`] when the box holds the
/// split input within two periods or when a class's run reads a guard on the remainder by
/// itself ([`Residue::alone`]).
///
/// The terms compare `x mod m` with constants for one input `x` and one modulus `m`; the
/// constants cut `[0, m)` into classes in which each such comparison is true throughout or
/// false throughout, so a backward transfer restricted to one class reads the comparisons
/// exactly ([`Walk::back_arith`]). The preimage is the union over the classes `R` of the
/// transfer's set `S_R` for `x` within `R`: the members of every `S_R`, and the members of
/// each `S_R` outside that common part whose remainder is in `R`. The other inputs must
/// have the same sets in every class whose set is not empty, so that the union is a box.
///
/// Design (COMPLEXITY.md rows S22e-quad and S22e-wide). (A) The runs of the classes share what
/// they compute without reading the class ([`Kept`]), and a term is read once for every class
/// as one summary over the classes ([`Walk::by_class`]): an `if` on the remainder takes its arms'
/// summaries class by class, `O(log G)`; a term that reads no remainder has one transfer in
/// every class, so it is summarized once, over the box, and that one summary stands in every
/// class (`min` and `max` with a constant, an `if` on a test that reads no remainder, the
/// affine maps). A chain of `k` such guards and terms costs `O(k log k)` in all, where each
/// class's own read of it cost `G` transfers. Measured over `[-5000, 5000]`, from `k` to `8k`:
/// guards `i mod 1024 == j` with arms `min(t + 1, 2^40)`, 2.24M to 17.6M instructions (`k` =
/// 8; main 21.7M to 5.25G), and `k` tests `i >= 7j` above `k` such guards, 6.44M to 53.7M
/// (`k` = 16; main 22.4M to 358M at 16 to 64).
///
/// (B) Where a stretch of `x` in which some classes keep their points and others do not spans
/// more than two periods, the set of its points is a piece for each period, more than a box
/// lists in the stretch's width (row C17). Main then ran the linear stage on the term. That
/// stage was slow and inexact for a cause in its translation, not in the term: it gave each
/// occurrence of `x mod m` its own pair of auxiliary variables, so `k` guards held `k` pairs
/// whose projection is above linear (one pair for each `x mod m` since S22-transfer-rem), and
/// its check of exactness decides the negated body, `k` disjuncts. Now the split answers
/// itself ([`Split::Wide`]): the classes' sets are one relation with one pair of auxiliary
/// variables for the split input, one flat disjunct for each piece ([`residue_relation`]); the
/// box is narrowed to its projection over the box's hull, linear in the pieces
/// ([`project_classes`]); and the box is exact when every member lies in the set of its
/// class, a sweep over the pieces with the classes marked in a Fenwick tree, `O(P log P)` for
/// `P` pieces, with no Presburger decision ([`covers`]). Before the first transfer such an
/// answer is kept, and the transfer and the split over its box run as
/// without it ([`preimage_in`]): over that narrower box the split may be exact where over the
/// whole box it is not. Measured from `k` to `8k`: `k` guards `i mod 1024 != j`, 17.3M to
/// 20.6M (`k` = 4; main 0.86G and 3.0G at 8 and 16, inexact), and `many_remainders(k)` below
/// `if (i mod 1024 == 0) { false }`, 85.9M to 498M (`k` = 4; main 11.3G and 84.1G at 8 and
/// 16, inexact); both are now exact.
///
/// Complexity tradeoff: a term the summary does not read is read by each class's run, `G`
/// times the cost of one transfer of it for `G` classes, and `G` is at most `2d + 1` for `d`
/// distinct constants compared: `O(G n log n)`, up to `O(n^2 log n)`, where that transfer is
/// `O(n log n)`. Such terms are listed at [`Walk::by_class`] (an `if` whose arms read different
/// inputs, a test of a term that reads a remainder, values that may leave `i64`). The split is
/// not tried when the terms compare remainders of two inputs or two moduli, and it is given
/// up when a class's transfer is not exact or when two classes narrow another input
/// differently; those inputs get the linear stage's answer, as before. Why: the classes of
/// two pairs combine as a product, `G1 * G2` transfers, and boxes that differ in two inputs
/// have a union that is not a box (row C14). Trigger: a guard `x mod m == c` for `d`
/// distinct `c` above such a term (the cost); two remainders compared; another input
/// narrowed by class. Test:
/// `l01_25_preimage_catalog::s22::chain_mod7_scales`,
/// `l01_25_preimage_catalog::s22::many_remainders_scales`,
/// `l01_25_preimage_catalog::s22::remainder_chains_outside_the_shared_summary_keep_their_preimages`
/// and `l01_25_preimage_catalog::s22::a_split_by_remainders_is_given_up_where_it_cannot_be_exact`;
/// COMPLEXITY.md rows S22e, S22e-quad and S22e-wide.
/// A complete solution would hold the congruence facet in the backward transfer's sets (`x mod
/// m` in a set of classes beside the interval), so that one transfer carries every class at
/// once.
///
/// Complexity tradeoff: over many periods the box keeps a mixed stretch's middle periods as
/// one piece, its first and last members in the class read once more ([`mod_pre`]), not a
/// piece for each period, which would be the stretch's width divided by `m` pieces with no
/// bound in the size of the term. Such a box is not exact ([`covers`] finds a member outside
/// its class's set) and carries the classes' relation, which is exact; the linear stage is
/// not run on it, since on a mixed stretch it costs more than linear (main: 0.86G to 3.0G
/// instructions for `k` = 8 to 16 guards). Given up: a box listing every period, and the
/// narrower box the linear stage could give: [`project_classes`] projects the relation over
/// the hull of the box, so the hull of a class's members joins pieces that the linear stage's
/// projection kept apart, and the answer is a wider box (still sound, with the exact
/// relation). Trigger: a mixed stretch that the transfer's box does not narrow to within two
/// periods, for example `i mod 10 == 3` over `[0, 10^9]`; the wider box appears where a class
/// has members in pieces separated by gaps, as in three random guarded chains, which get `i
/// [-19..]` for main's `i [-19..=2, 5..=5, 8..=8, 11..]`, `i [2..]` for `i [2..=2, 5..]` and
/// `i [4..]` for `i [4..=4, 7..]`. Test: `l01_25_preimage_catalog::entries` (the `[0, 10^9]`
/// case), `l01_25_preimage_catalog::s22::remainders_over_many_periods_scale` and
/// `l01_25_preimage_catalog::s22::more_random_guarded_chains_keep_their_preimages_3000` and
/// `_3750` (the three wider boxes); COMPLEXITY.md row S22e-wide. A complete solution for the wider boxes would
/// project over each piece of the box rather than its hull, or keep the congruence facet
/// below. The cost is the projection over the box's hull, linear in the pieces, and, for
/// an answer kept before the first transfer, one more transfer and split over the
/// transfer's box, `O(n log n)`. A complete solution would give the box a congruence facet
/// (an input's interval together with the set of its remainders mod `m` that it admits), so
/// that the middle periods are one piece and the box is still exact.
fn split_residues(
    tx: &mut Tx<'_>,
    root: Tid,
    dom: &Domains,
    demand: &Demand,
    marks: &Marks,
    early: bool,
) -> Split {
    let mut deferred = false;
    *tx.split_meets.borrow_mut() = Some(DomainMeets::new());
    let found = split_classes(tx, root, dom, demand, marks, early, &mut deferred);
    *tx.split_meets.borrow_mut() = None;
    match found {
        Some((d, None)) => Split::Exact(d),
        Some((d, Some(found))) => Split::Wide(d, found),
        None if deferred => Split::Deferred,
        None => Split::NotExact,
    }
}

/// [`split_residues`]: `None` when the split is not found exact, with `deferred` set when it is
/// given up for the first transfer to run first.
fn split_classes(
    tx: &mut Tx<'_>,
    root: Tid,
    dom: &Domains,
    demand: &Demand,
    marks: &Marks,
    early: bool,
    deferred: &mut bool,
) -> Option<(Domains, Option<ClassRelation>)> {
    let (x, c, cuts) = tx.residue_cuts(dom)?;
    let m = c.unsigned_abs() as i128;
    let name = tx.name(x).clone();
    // Within two periods the transfer over the box reads every guard on the remainder exactly
    // ([`mod_pre`]).
    if early
        && let Some((Fin(lo), Fin(hi))) = dom[&name].bounds()
        && hi.div_euclid(&Num::from(m)) <= &lo.div_euclid(&Num::from(m)) + &Num::ONE
    {
        *deferred = true;
        return None;
    }
    let cuts: Rc<[i128]> = cuts.into();
    // The runs share the box's domains, made once ([`Tx::begin`]), and the meets of sets with
    // them ([`Tx::meet_domain`]): the classes whose runs find one set of `x` share it, so that
    // neither the domain nor that set is copied for each class.
    //
    // Complexity tradeoff: classes whose runs find different sets of `x` still build each set,
    // `O(H)` for each class over a domain of `H` holes (for example arms that bound `x` by a
    // different constant in each class), and the wide path below ([`residue_relation`],
    // [`covers`]) reads each class's own part. Test:
    // `l01_25_preimage_catalog::s22::split_classes_share_the_holes_scale` covers the shared case
    // only (deferred to plan row S22-scaling-10_5 in
    // wt/scratch/deferred-tests/S22-scaling-10_5.rs); COMPLEXITY.md row S22-split-holes. A
    // complete solution would keep a run's set as "this set within the domain" without meeting
    // the two, so that classes that bound `x` differently share the domain's holes too.
    let begun = tx.begin(dom);
    let empty = Rc::new(IntervalSet::empty());
    let mut sets: Vec<(Rc<IntervalSet>, IntervalSet)> = Vec::with_capacity(cuts.len() - 1);
    let mut rest: Option<RestBox> = None;
    let mut marks = marks.clone();
    let mut kept = Kept::default();
    for (index, w) in cuts.windows(2).enumerate() {
        tx.start_from(&begun, marks);
        // What the runs compute without reading the class is computed once for all of them.
        tx.run.restore(std::mem::take(&mut kept));
        tx.run.residue = Some(Residue {
            x,
            m,
            class: IntervalSet::range(End::from(w[0]), End::from(w[1] - 1)),
            index,
            cuts: cuts.clone(),
            alone: false,
        });
        let r = tx.back(root, ROOT, demand);
        let exact = r.exact && tx.run.stops.is_empty();
        let Residue { class, alone, .. } = tx.run.residue.take().expect("the class was set above");
        if early && alone {
            *deferred = true;
            return None;
        }
        if !exact {
            return None;
        }
        kept = tx.run.keep();
        marks = std::mem::take(&mut tx.run.marks);
        let (s, d) = split_box(&begun.cx, &r, tx.none(&r), &name, &empty);
        if !s.is_empty() {
            match &rest {
                Some(o) if !same_box(&begun.cx, o, &d) => return None,
                Some(_) => {}
                None => rest = Some(d),
            }
        }
        sets.push((s, class));
    }
    // The classes that share a set, each set once, in the order of their first class.
    let mut groups: Vec<(Rc<IntervalSet>, Vec<usize>)> = Vec::new();
    let mut group = Vec::with_capacity(sets.len());
    // Keyed by the set's address: `sets` holds every key's `Rc` for the whole loop, and the
    // map is read only by `entry`, never iterated; the groups are in the order of `sets`.
    let mut by_set: HashMap<*const IntervalSet, usize> = HashMap::new();
    for (j, (s, _)) in sets.iter().enumerate() {
        let g = *by_set.entry(Rc::as_ptr(s)).or_insert_with(|| {
            groups.push((s.clone(), Vec::new()));
            groups.len() - 1
        });
        groups[g].1.push(j);
        group.push(g);
    }
    let common = match &groups[..] {
        [(s, _)] => s.clone(),
        [(first, _), others @ ..] => {
            let mut common = (**first).clone();
            for (s, _) in others {
                if common.is_empty() {
                    break;
                }
                common = common.meet(s);
            }
            Rc::new(common)
        }
        [] => unreachable!("at least two classes"),
    };
    // What each set holds beyond the common part: the set itself where nothing is common.
    let owns: Vec<Rc<IntervalSet>> = (groups.iter())
        .map(|(s, _)| match common.is_empty() {
            true => s.clone(),
            false => Rc::new(common.complement_in(s)),
        })
        .collect();
    let mut pieces = IntervalSet::clone(&common).into_pieces();
    let mut wide = false;
    for (own, (_, members)) in owns.iter().zip(&groups) {
        for (lo, hi) in own.pieces() {
            // A piece is read for the classes whose remainders it holds, found by binary
            // search, not for every class of its set ([`touched`]).
            for &j in touched(lo, hi, members, &cuts, m).into_iter().flatten() {
                let class = &sets[j].1;
                // An end moves in to the nearest member of the class, which [`mod_pre`]
                // leaves on a half-line.
                let Some(within) = in_class(lo, hi, class, m) else {
                    continue;
                };
                let (hull, exact) = mod_pre(class, c, &within);
                if exact {
                    pieces.extend(hull.pieces().cloned());
                    continue;
                }
                // The merged periods between the first and the last are read once more,
                // which lists their own first and last, as the transfer's box split again
                // did before.
                for (a, b) in hull.pieces() {
                    let (part, exact) =
                        mod_pre(class, c, &IntervalSet::range(a.clone(), b.clone()));
                    wide |= !exact;
                    pieces.extend(part.pieces().cloned());
                }
            }
        }
    }
    let Some(rest) = rest else {
        let none = dom.keys().map(|k| (k.clone(), IntervalSet::empty()));
        return Some((none.collect(), None));
    };
    let mut rest = box_domains(&begun.cx, rest);
    rest.insert(name.clone(), IntervalSet::from_pieces(pieces));
    if !wide {
        return Some((rest, None));
    }
    // A stretch over more than two periods holds the class's remainders in each period, a
    // piece for each; the box holds their hull, and the relation the remainders. The box is
    // narrowed to the relation's projection, which lists the periods within the box, and is
    // exact when every member lies in the set of its class ([`covers`]).
    let parts: Vec<(&IntervalSet, &IntervalSet)> = (sets.iter().zip(&group))
        .map(|((_, class), &g)| (&*owns[g], class))
        .filter(|(own, _)| !own.is_empty())
        .collect();
    let rel = residue_relation(&name, c, &common, &parts);
    let (out, why) = project_classes(&rel, &rest);
    let sets: Vec<&IntervalSet> = sets.iter().map(|(s, _)| &**s).collect();
    if covers(&out[&name], &sets, &cuts, m) {
        return Some((out, None));
    }
    Some((out, Some((rel, why))))
}

/// The box of the inputs other than the split input in one class's run of [`split_classes`],
/// as [`Tx::whole`] gives it, with no set copied.
type RestBox = BTreeMap<Arc<str>, BoxSet>;

/// The set of an input in a [`RestBox`]: shared with the run, or the domain of an input of the
/// context's read number `i` ([`LetIn::read`]) that the run does not narrow.
enum BoxSet {
    Set(Rc<IntervalSet>),
    Read(usize),
}

impl BoxSet {
    fn get<'a>(&'a self, cx: &'a Cx, k: &str) -> &'a IntervalSet {
        match self {
            BoxSet::Set(s) => s,
            BoxSet::Read(i) => cx.reads[*i].ints(k).expect("the read holds the input"),
        }
    }
}

/// [`Tx::whole`] of the box `r` of a class's run in the context `cx`, `none` when it holds no
/// point ([`Tx::none`]): the set of the split input `name`, and the box of the others
/// ([`RestBox`]). `O(n log n)` for the `n` inputs, however large their sets are.
fn split_box(
    cx: &Cx,
    r: &Res,
    none: bool,
    name: &str,
    empty: &Rc<IntervalSet>,
) -> (Rc<IntervalSet>, RestBox) {
    let of = |k: &Arc<str>, z: BoxSet| match r.dom.get(k) {
        _ if none => BoxSet::Set(empty.clone()),
        Some(n) => BoxSet::Set(n.clone()),
        None => z,
    };
    let inputs = cx.inputs.iter();
    let mut out: RestBox = inputs
        .map(|(k, z)| (k.clone(), of(k, BoxSet::Set(z.clone()))))
        .collect();
    for (i, read) in cx.reads.iter().enumerate() {
        for v in read.vars() {
            if !out.contains_key(v) && read.ints(v).is_some() {
                out.insert(v.clone(), of(v, BoxSet::Read(i)));
            }
        }
    }
    match out.remove(name) {
        Some(BoxSet::Set(s)) => (s, out),
        _ => unreachable!("the split input is an input"),
    }
}

/// Whether two boxes of [`split_box`] in the context `cx` are equal: `O(1)` for each set they
/// share, and the comparison of the sets for the others.
fn same_box(cx: &Cx, a: &RestBox, b: &RestBox) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|((k, x), (l, y))| {
            k == l
                && match (x, y) {
                    (BoxSet::Set(x), BoxSet::Set(y)) => Rc::ptr_eq(x, y) || x == y,
                    (BoxSet::Read(i), BoxSet::Read(j)) if i == j => true,
                    _ => x.get(cx, k) == y.get(cx, k),
                }
        })
}

/// The box of [`split_box`] as domains, each set copied once.
fn box_domains(cx: &Cx, rest: RestBox) -> Domains {
    (rest.into_iter())
        .map(|(k, s)| {
            let z = match s {
                BoxSet::Set(s) => Rc::unwrap_or_clone(s),
                BoxSet::Read(_) => s.get(cx, &k).clone(),
            };
            (k, z)
        })
        .collect()
}

/// Of the classes `members`, in increasing order, those whose remainders `cuts[j]..cuts[j +
/// 1]` by `m` meet the remainders of the members of `lo..=hi`: one range of the classes, or
/// two where the remainders of the piece wrap past `m`, and all of them where the piece spans
/// a period or a half-line. They hold every class for which [`in_class`] finds a member of
/// the piece. `O(log k)` for `k` members, by binary search. Each answer is counted by its
/// kind ([`touched_paths`]).
fn touched<'a>(
    lo: &End,
    hi: &End,
    members: &'a [usize],
    cuts: &[i128],
    m: i128,
) -> [&'a [usize]; 2] {
    let (Fin(lo), Fin(hi)) = (lo, hi) else {
        count_touched(|t| &mut t.half_line);
        return [members, &[]];
    };
    if hi - lo >= Num::from(m - 1) {
        count_touched(|t| &mut t.period);
        return [members, &[]];
    }
    let rem = |x: &Num| {
        let r = x.rem_euclid(&Num::from(m));
        r.to_i128().expect("a remainder lies below the modulus")
    };
    let class = |r: i128| cuts.partition_point(|&c| c <= r) - 1;
    let within = |a: usize, b: usize| {
        let from = members.partition_point(|&j| j < a);
        let to = members.partition_point(|&j| j <= b);
        &members[from..to]
    };
    let (rl, rh) = (rem(lo), rem(hi));
    let (a, b) = (class(rl), class(rh));
    if rl <= rh {
        count_touched(|t| &mut t.one_range);
        [within(a, b), &[]]
    } else if b < a {
        count_touched(|t| &mut t.two_ranges);
        [within(a, usize::MAX), within(0, b)]
    } else {
        // The remainders wrap past `m` back into the class they started in: every class.
        count_touched(|t| &mut t.wrapped_into_its_class);
        [members, &[]]
    }
}

/// How many pieces `touched` answered by each of its five kinds on this thread since the
/// last call of [`touched_paths`] (COMPLEXITY.md S22-split-holes).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TouchedPaths {
    /// A piece with an infinite end: every class.
    pub half_line: u64,
    /// A piece of `m` or more integers: every class.
    pub period: u64,
    /// A piece whose remainders run up from its low end's to its high end's: one range.
    pub one_range: u64,
    /// A piece whose remainders wrap past `m` into an earlier class: two ranges.
    pub two_ranges: u64,
    /// A piece whose remainders wrap past `m` back into the class they start in or a later
    /// one: every class.
    pub wrapped_into_its_class: u64,
}

thread_local! {
    static TOUCHED: std::cell::Cell<TouchedPaths> = const {
        std::cell::Cell::new(TouchedPaths {
            half_line: 0,
            period: 0,
            one_range: 0,
            two_ranges: 0,
            wrapped_into_its_class: 0,
        })
    };
}

/// The counts of [`TouchedPaths`] on this thread since the last call, which resets them.
pub fn touched_paths() -> TouchedPaths {
    TOUCHED.replace(TouchedPaths::default())
}

fn count_touched(kind: impl FnOnce(&mut TouchedPaths) -> &mut u64) {
    TOUCHED.with(|c| {
        let mut t = c.get();
        *kind(&mut t) += 1;
        c.set(t);
    });
}

/// The integers of `lo..=hi` from the first to the last whose remainder by `m` lies in `class`,
/// one range of remainders, or `None` when there is none.
fn in_class(lo: &End, hi: &End, class: &IntervalSet, m: i128) -> Option<IntervalSet> {
    let Some((Fin(a), Fin(b))) = class.bounds() else {
        unreachable!("a class is a range of remainders")
    };
    let m = Num::from(m);
    let lo = match lo {
        Fin(x) => {
            let r = x.rem_euclid(&m);
            Fin(if r < *a {
                x + &(a - &r)
            } else if r > *b {
                &(x + &(&m - &r)) + a
            } else {
                x.clone()
            })
        }
        e => e.clone(),
    };
    let hi = match hi {
        Fin(x) => {
            let r = x.rem_euclid(&m);
            Fin(if r > *b {
                x - &(&r - b)
            } else if r < *a {
                &(x - &(&r + &m)) + b
            } else {
                x.clone()
            })
        }
        e => e.clone(),
    };
    match (&lo, &hi) {
        (Fin(l), Fin(h)) if l > h => None,
        _ => Some(IntervalSet::range(lo, hi)),
    }
}

/// Whether every member of `out` lies in the set of its class, `sets[j]` for the remainders
/// `cuts[j]..cuts[j + 1]` by `m`: whether `out` holds only points of the split's preimage. A
/// sweep over the ends of the pieces of `out` and of every set, in order, with the classes
/// whose set holds the stretch up to the next end marked in a Fenwick tree over the classes:
/// a stretch within `out` is covered when every class of its remainders is marked, one range
/// of classes, or two where the remainders wrap past `m`. `O(P log P)` for `P` pieces.
fn covers(out: &IntervalSet, sets: &[&IntervalSet], cuts: &[i128], m: i128) -> bool {
    // At each end a piece starts (+1) or stops (-1): a set's, of class `Some(j)`, or `out`'s.
    let mut ends: Vec<(End, i64, Option<usize>)> = Vec::new();
    let all = sets.iter().enumerate().map(|(j, s)| (Some(j), *s));
    for (j, s) in all.chain([(None, out)]) {
        for (lo, hi) in s.pieces() {
            ends.push((lo.clone(), 1, j));
            if *hi != PosInf {
                ends.push((hi.succ(), -1, j));
            }
        }
    }
    // Every end at one place is applied before the stretch after it is read, so the order
    // among them does not matter.
    ends.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    let g = sets.len();
    let mut tree = vec![0i64; g + 1];
    let add = |tree: &mut [i64], j: usize, d: i64| {
        let mut i = j + 1;
        while i <= g {
            tree[i] += d;
            i += i.isolate_lowest_one();
        }
    };
    // The number of marked classes below `j`.
    let below = |tree: &[i64], j: usize| {
        let (mut i, mut n) = (j, 0);
        while i > 0 {
            n += tree[i];
            i -= i.isolate_lowest_one();
        }
        n
    };
    let full = |tree: &[i64], (a, b): (usize, usize)| {
        below(tree, b + 1) - below(tree, a) == (b - a + 1) as i64
    };
    let class = |r: &Num| {
        let r = r.to_i128().expect("a remainder lies below the modulus");
        cuts.partition_point(|&c| c <= r) - 1
    };
    let m = Num::from(m);
    let (mut inside, mut i) = (false, 0);
    while i < ends.len() {
        let at = ends[i].0.clone();
        while let Some((e, d, j)) = ends.get(i)
            && *e == at
        {
            match j {
                Some(j) => add(&mut tree, *j, *d),
                None => inside = *d > 0,
            }
            i += 1;
        }
        if !inside {
            continue;
        }
        // The stretch from `at` to the next end, or on to `PosInf`.
        let covered = match (&at, ends.get(i).map(|e| &e.0)) {
            (Fin(u), Some(Fin(next))) if (next - u) < m => {
                let v = next - &Num::ONE;
                let (ru, rv) = (u.rem_euclid(&m), v.rem_euclid(&m));
                // The stretch wraps past `m` when its last remainder is below its first.
                // Its two ends may fall in one class, so the order of the classes does
                // not tell; the remainders do.
                let (a, b) = (class(&ru), class(&rv));
                if ru <= rv {
                    full(&tree, (a, b))
                } else {
                    full(&tree, (a, g - 1)) && full(&tree, (0, b))
                }
            }
            _ => full(&tree, (0, g - 1)),
        };
        if !covered {
            return false;
        }
    }
    true
}

/// The relation that `x` is in `common`, or in the set of one of `parts` with `x mod c` in
/// its class: `x == c * q + r` and `0 <= r < |c|`, with `q` and `r` the auxiliary variables 0
/// and 1, as the linear-relation domain defines a remainder.
fn residue_relation(
    name: &Arc<str>,
    c: i64,
    common: &IntervalSet,
    parts: &[(&IntervalSet, &IntervalSet)],
) -> Relation {
    use presburger::Atom;
    let x = Atom::Sym(name.clone());
    let (q, r) = (Lin::atom(Atom::Aux(0)), Lin::atom(Atom::Aux(1)));
    let c = i128::from(c);
    let def = Formula::and(vec![
        Formula::Con(Con::eq(&Lin::atom(x.clone()), &q.times(c).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(c.abs() - 1), &r)),
    ]);
    // One disjunct for each piece, so that the body is one disjunction, which the projection
    // reads exactly ([`presburger::project_each`]).
    let one =
        |lo: &End, hi: &End| presburger::member(&x, &IntervalSet::range(lo.clone(), hi.clone()));
    let mut body: Vec<Formula> = common.pieces().map(|(lo, hi)| one(lo, hi)).collect();
    for (s, class) in parts {
        for (lo, hi) in s.pieces() {
            body.push(Formula::and(vec![
                one(lo, hi),
                presburger::member(&Atom::Aux(1), class),
            ]));
        }
    }
    Relation {
        body: Formula::or(body),
        defs: vec![
            (0, format!("{name} div {c}"), def),
            (1, format!("{name} mod {c}"), Formula::top()),
        ],
        bit_ands: Vec::new(),
    }
}

/// Whether `f` is `true` as [`Formula::top`] makes it.
fn is_true(f: &Formula) -> bool {
    matches!(f, Formula::And(gs) if gs.is_empty())
}

/// The condition that a term's value is not an atom ([`Walk::defined`]): each divisor of a
/// quotient or remainder that the term reads wherever it is read is not 0, and `rest` holds,
/// the part an `if` adds whose arms read different divisors.
#[derive(Clone)]
struct Defined {
    /// The divisors read wherever the term is read, a set of [`Tr::sets`], so that a divisor
    /// read at many places is one condition, and two conditions with the same divisors share
    /// one set.
    divisors: Set,
    /// `d != 0` for each of `divisors`, made as the set was, two parts at a time and each kept
    /// whole ([`Formula::and_keeping`]), so it costs O(1) for each step and may name a divisor
    /// more than once.
    nonzero: Formula,
    rest: Formula,
}

impl Defined {
    /// No divisor and nothing else: the value is never an atom.
    fn top() -> Defined {
        Defined {
            divisors: EMPTY,
            nonzero: Formula::top(),
            rest: Formula::top(),
        }
    }

    /// The value is always an atom.
    fn failed() -> Defined {
        Defined {
            rest: Formula::bottom(),
            ..Defined::top()
        }
    }

    fn is_top(&self) -> bool {
        self.divisors == EMPTY && is_true(&self.rest)
    }

    /// `d != 0`.
    fn nonzero_of(d: &Lin) -> Formula {
        Formula::negate(Formula::Con(Con::eq(d, &Lin::constant(0))))
    }

    /// `self` with the divisor `d` as well. O(log n).
    fn with_divisor(self, d: &Lin, sets: &mut DivisorSets) -> Defined {
        let one = sets.single(d);
        let divisors = sets.union(self.divisors, one);
        if divisors == self.divisors {
            return self;
        }
        Defined {
            divisors,
            nonzero: keep_all(vec![self.nonzero, Defined::nonzero_of(d)]),
            rest: self.rest,
        }
    }

    /// Both conditions. The divisor sets are joined by the parts they do not share
    /// ([`DivisorSets::union`]), O(m log(n/m + 1)) for m divisors of one not in the other, and O(1)
    /// for a set met with itself or again with the same set; a set that holds the other keeps
    /// its own `nonzero`.
    fn meet(self, other: Defined, sets: &mut DivisorSets) -> Defined {
        if other.is_top() {
            return self;
        }
        if self.is_top() {
            return other;
        }
        let divisors = sets.union(self.divisors, other.divisors);
        let nonzero = match divisors {
            d if d == self.divisors => self.nonzero,
            d if d == other.divisors => other.nonzero,
            _ => keep_all(vec![self.nonzero, other.nonzero]),
        };
        let rest = match (is_true(&self.rest), is_true(&other.rest)) {
            (true, _) => other.rest,
            (_, true) => self.rest,
            _ => keep_all(vec![self.rest, other.rest]),
        };
        Defined {
            divisors,
            nonzero,
            rest,
        }
    }

    /// The condition as a formula, each part kept whole.
    fn formula(&self) -> Formula {
        keep_all(vec![self.nonzero.clone(), self.rest.clone()])
    }

    /// The condition as a formula, each divisor once and in their order, for a relation's
    /// body.
    fn flat(&self, sets: &DivisorSets) -> Formula {
        let mut parts = Vec::with_capacity(sets.len(self.divisors) as usize + 1);
        sets.each(self.divisors, &mut |d| parts.push(Defined::nonzero_of(d)));
        parts.push(self.rest.clone());
        Formula::and(parts)
    }

    /// The condition written at a call: each canonical atom that `to` maps replaced by its
    /// argument, and each quotient and remainder by a constant written there
    /// ([`Tr::instance`]). `None` when a divisor or a part of `rest` reads another auxiliary
    /// variable or a product. Time of the condition, times the log of its divisors.
    fn instance(&self, tr: &mut Tr, to: &HashMap<Arc<str>, Lin>) -> Option<Defined> {
        let mut done = HashMap::new();
        let mut divisors = Vec::with_capacity(tr.sets.len(self.divisors) as usize);
        tr.sets
            .each(self.divisors, &mut |d| divisors.push(d.clone()));
        let mut out = Defined::top();
        for d in &divisors {
            let d = tr.instance(d, to, None, &mut done)?;
            out = out.with_divisor(&d, &mut tr.sets);
        }
        if is_true(&self.rest) {
            return Some(out);
        }
        let (tr, done, failed) = (RefCell::new(tr), RefCell::new(done), Cell::new(false));
        let rest = self.rest.map_cons(&|c| {
            let lin = tr
                .borrow_mut()
                .instance(&c.lin, to, None, &mut done.borrow_mut());
            match lin {
                Some(lin) => Formula::Con(Con { lin, rel: c.rel }),
                None => {
                    failed.set(true);
                    Formula::top()
                }
            }
        });
        (!failed.get()).then_some(Defined { rest, ..out })
    }

    /// Each divisor of `divisors` that the constraint `f`, a part of a conjunction, shows is not
    /// 0: `d` for `d != 0` or `-d != 0`, `d >= 1` or `d <= -1` for `t >= 0` with `d` `t + k`
    /// or `-t - k`, `k >= 1`, and `d != 0` for `t == 0` with `d` `t + k` or `-t - k`,
    /// `k != 0`. A set in order holds the divisors with one variable part together, so each
    /// form costs a search, O(log n), and the divisors it finds.
    fn shown_nonzero(sets: &DivisorSets, divisors: Set, f: &Formula, out: &mut Vec<Lin>) {
        use presburger::Rel;
        // The divisors whose variable part is `terms`, from the constant `from` up, or down.
        let up = |terms: &Lin, from: &Lin, out: &mut Vec<Lin>| {
            sets.up(divisors, from, &|d: &Lin| d.terms == terms.terms, out);
        };
        let down = |terms: &Lin, to: &Lin, out: &mut Vec<Lin>| {
            sets.down(divisors, to, &|d: &Lin| d.terms == terms.terms, out);
        };
        let one = Lin::constant(1);
        match f {
            Formula::Not(g) => match &**g {
                Formula::Con(c) if c.rel == Rel::Eq => {
                    let neg = c.lin.times(-1);
                    for d in [&c.lin, &neg] {
                        if sets.contains(divisors, d) {
                            out.push(d.clone());
                        }
                    }
                }
                // `t < 0`, which is `-t - 1 >= 0`.
                Formula::Con(c) => {
                    let t = c.lin.times(-1).minus(&one);
                    Defined::shown_nonzero(
                        sets,
                        divisors,
                        &Formula::Con(Con::ge(&t, &Lin::constant(0))),
                        out,
                    )
                }
                _ => {}
            },
            Formula::Con(c) if c.rel == Rel::Ge => {
                let neg = c.lin.times(-1);
                up(&c.lin, &c.lin.plus(&one), out);
                down(&neg, &neg.minus(&one), out);
            }
            Formula::Con(c) => {
                let neg = c.lin.times(-1);
                for t in [&c.lin, &neg] {
                    up(t, &t.plus(&one), out);
                    down(t, &t.minus(&one), out);
                }
            }
            _ => {}
        }
    }

    /// The condition the arm `d` adds where it is taken, under the guard's formula `g` and
    /// with the guard's own divisors `known` not 0: `true` when `d`'s `rest` is `true` and
    /// each of `d`'s divisors is in `known` or is shown not 0 by a part of `g`
    /// ([`Defined::shown_nonzero`]), and `d`'s own formula otherwise, shared, O(1). `g`'s
    /// parts are read one by one only when `parts` holds, as the formula of the `if` reads
    /// them (a guard kept whole is one part there and here). Whether `known` holds `d`'s
    /// divisors is their union ([`DivisorSets::union`]): O(1) when the arm reads the guard's
    /// divisors, as `if n != 0 { x mod n } else { 0 }` and `if x mod n >= 1 { y mod n } else
    /// { 0 }` do, and O(m log(n/m + 1)) for m divisors of the arm not in the guard; then each
    /// part of the guard costs a search, O(log n), where the formula of the `if` costs the
    /// part.
    fn arm(d: &Defined, g: &Formula, parts: bool, known: Set, sets: &mut DivisorSets) -> Formula {
        if d.is_top() || !is_true(&d.rest) {
            return d.formula();
        }
        if sets.union(known, d.divisors) == known {
            return Formula::top();
        }
        let mut shown = Vec::new();
        match g {
            Formula::And(gs) if parts => {
                for p in gs.iter() {
                    Defined::shown_nonzero(sets, d.divisors, p, &mut shown);
                }
            }
            _ => Defined::shown_nonzero(sets, d.divisors, g, &mut shown),
        }
        if shown.is_empty()
            || sets.len(d.divisors) as usize > sets.len(known) as usize + shown.len()
        {
            return d.formula();
        }
        let mut covered = known;
        for x in &shown {
            let one = sets.single(x);
            covered = sets.union(covered, one);
        }
        match sets.union(covered, d.divisors) == covered {
            true => Formula::top(),
            false => d.formula(),
        }
    }
}

/// The divisors that the constraints of a chain's operands read so far show are not 0, as
/// [`Defined::shown_nonzero`] finds them, kept by their variable part, so that a constraint
/// costs O(1) and a divisor's question O(1) whatever the number of constraints before it
/// ([`Walk::defined_chain`]).
#[derive(Default)]
struct Shown {
    /// For each variable part, the least constant from which up a divisor with that part is
    /// shown not 0.
    up: HashMap<BTreeMap<presburger::Atom, Int>, Int>,
    /// For each variable part, the greatest constant from which down one is.
    down: HashMap<BTreeMap<presburger::Atom, Int>, Int>,
    /// The divisors shown not 0 one by one, by `d != 0` or `-d != 0`.
    exact: HashSet<Lin>,
}

impl Shown {
    /// The divisors `t + k` with `k >= 1` are shown not 0.
    fn above(&mut self, t: &Lin) {
        let from = &t.constant + &Int::from(1);
        let e = self
            .up
            .entry(t.terms.clone())
            .or_insert_with(|| from.clone());
        if from < *e {
            *e = from;
        }
    }

    /// The divisors `t - k` with `k >= 1` are shown not 0.
    fn below(&mut self, t: &Lin) {
        let to = &t.constant - &Int::from(1);
        let e = self
            .down
            .entry(t.terms.clone())
            .or_insert_with(|| to.clone());
        if to > *e {
            *e = to;
        }
    }

    /// The divisors that the constraint `f`, a part of a conjunction, shows are not 0, the
    /// forms of [`Defined::shown_nonzero`].
    fn add(&mut self, f: &Formula) {
        use presburger::Rel;
        match f {
            Formula::Not(g) => match &**g {
                Formula::Con(c) if c.rel == Rel::Eq => {
                    self.exact.insert(c.lin.clone());
                    self.exact.insert(c.lin.times(-1));
                }
                // `t < 0`, which is `-t - 1 >= 0`.
                Formula::Con(c) => {
                    let t = c.lin.times(-1).minus(&Lin::constant(1));
                    self.add(&Formula::Con(Con::ge(&t, &Lin::constant(0))));
                }
                _ => {}
            },
            Formula::Con(c) if c.rel == Rel::Ge => {
                self.above(&c.lin);
                self.below(&c.lin.times(-1));
            }
            Formula::Con(c) => {
                for t in [c.lin.clone(), c.lin.times(-1)] {
                    self.above(&t);
                    self.below(&t);
                }
            }
            _ => {}
        }
    }

    /// The parts of the guard `g`: each part of a conjunction when `parts` holds, as
    /// [`Defined::arm`] reads them, and `g` itself otherwise.
    fn add_guard(&mut self, g: &Formula, parts: bool) {
        match g {
            Formula::And(gs) if parts => gs.iter().for_each(|p| self.add(p)),
            _ => self.add(g),
        }
    }

    /// Whether `d` is shown not 0.
    fn holds(&self, d: &Lin) -> bool {
        self.exact.contains(d)
            || self.up.get(&d.terms).is_some_and(|k| d.constant >= *k)
            || self.down.get(&d.terms).is_some_and(|k| d.constant <= *k)
    }

    /// The condition the operand whose condition is `d` adds where it is read, with the
    /// divisors `known` not 0 there: `true` when `d`'s `rest` is `true` and each of its
    /// divisors is in `known` or shown not 0, and `d`'s own formula otherwise, as
    /// [`Defined::arm`] makes it. O(1) when `known` holds `d`'s divisors, and otherwise the
    /// union of the two and a question for each of `d`'s divisors.
    fn arm(&self, d: &Defined, known: Set, sets: &mut DivisorSets) -> Formula {
        if d.is_top() || !is_true(&d.rest) {
            return d.formula();
        }
        if sets.union(known, d.divisors) == known {
            return Formula::top();
        }
        let sets: &DivisorSets = sets;
        let mut all = true;
        sets.each(d.divisors, &mut |x| {
            all &= sets.contains(known, x) || self.holds(x)
        });
        match all {
            true => Formula::top(),
            false => d.formula(),
        }
    }
}
/// Numbers for formulas by their parts, so that two formulas made apart but alike have one
/// number: each node numbered by its kind and its parts' numbers, and each shared part once,
/// by its id ([`presburger::Id`]). A key of [`Walk::shared_call_key`] holds the number of each
/// argument's condition. Time of the nodes not numbered before.
#[derive(Default)]
struct FormulaNumbers {
    by_id: HashMap<presburger::Id, u32>,
    by_shape: HashMap<Shape, u32>,
}

/// A node of a formula over its parts' numbers ([`FormulaNumbers`]).
#[derive(PartialEq, Eq, Hash)]
enum Shape {
    Con(Con),
    Not(u32),
    And(Vec<u32>),
    Or(Vec<u32>),
}

impl FormulaNumbers {
    /// The number of `f`: after its parts, on an explicit stack, as deep as the formula.
    fn number(&mut self, f: &Formula) -> u32 {
        fn parts(g: &Formula) -> &[Formula] {
            match g {
                Formula::Con(_) => &[],
                Formula::Not(h) => std::slice::from_ref(&**h),
                Formula::And(hs) | Formula::Or(hs) => hs,
            }
        }
        let mut todo = vec![(f, false)];
        let mut out: Vec<u32> = Vec::new();
        while let Some((g, ready)) = todo.pop() {
            let id = (!matches!(g, Formula::Con(_))).then(|| presburger::Id::any(g));
            if !ready {
                if let Some(&n) = id.and_then(|id| self.by_id.get(&id)) {
                    out.push(n);
                    continue;
                }
                todo.push((g, true));
                todo.extend(parts(g).iter().rev().map(|h| (h, false)));
                continue;
            }
            let ns = out.split_off(out.len() - parts(g).len());
            let shape = match g {
                Formula::Con(c) => Shape::Con(c.clone()),
                Formula::Not(_) => Shape::Not(ns[0]),
                Formula::And(_) => Shape::And(ns),
                Formula::Or(_) => Shape::Or(ns),
            };
            let next = self.by_shape.len() as u32;
            let n = *self.by_shape.entry(shape).or_insert(next);
            if let Some(id) = id {
                self.by_id.insert(id, n);
            }
            out.push(n);
        }
        out.pop().expect("the number of the formula")
    }
}

/// The conjunction of `fs`, each kept whole ([`Formula::and_keeping`]).
fn keep_all(fs: Vec<Formula>) -> Formula {
    Formula::and_keeping(fs, |_| true)
}

/// The relations the linear-relation domain states for `terms`, tests over the free names
/// `inputs`, with one numbering of auxiliary variables; products of two symbols are atoms
/// when `products` holds. `None` when a term is outside the domain.
///
/// The terms carry no types, and `+`, `-`, `*`, `div`, `mod`, `-x` and the comparisons are
/// read as integer arithmetic, so the caller passes as `inputs` only the names that hold
/// `int`s alone (`Sig::int_params` in zedc-types; RUNG2-carrier, LADDER-study D6): at `f64`,
/// `(a + b) + c == a + (b + c)` is false, and read over integers it would be proved. A name
/// not in `inputs` puts a term that reads it outside the domain, and a literal is read only
/// when it is an integer, so a term over any other carrier is `None`.
///
/// When `products` holds, a divisor may be a term, which may be 0, where the quotient and the
/// remainder fail (`Tr::div_mod_by_term`). Each relation then holds exactly where the
/// interpreter's value of its test is `true`: the test's formula met with the condition that
/// its value is not the failure (`Walk::defined`, `Tr::definedness`). Rung 2's
/// `presburger::entails` so proves a goal only where it holds at the points where an
/// operation fails as well, and refutes only at a point where the interpreter's value of the
/// goal is not `true` (RUNG2-definedness). The condition costs O(1) for each term and scope
/// the translation reads, as the formula does.
pub fn relations(terms: &[&Term], inputs: &[Arc<str>], products: bool) -> Option<Vec<Relation>> {
    let doms: Domains = inputs
        .iter()
        .map(|n| (n.clone(), IntervalSet::top()))
        .collect();
    let mut tx = Tx::new();
    tx.start(&doms, Marks::default());
    let mut tr = Tr::new(products);
    tr.definedness = products;
    let mut out = Vec::new();
    for t in terms {
        let root = tx.terms.add(t);
        let first = tr.defs.len();
        let body = tx.relation(&mut tr, root, ROOT)?;
        out.push(Relation {
            body,
            defs: tr.written(first),
            bit_ands: tr.bit_ands(first),
        });
    }
    Some(out)
}

/// The relations of the bodies of a unit's functions, each read under one scope of the
/// unit's definitions (step L1.38's linear questions, `front::linear_questions`). Each is the
/// relation [`relations`] gives for the body closed over the definitions it reaches, with
/// its own numbering of auxiliary variables. The scope is numbered once, and what the
/// transfer finds of a term without reading the inputs (whether it reads one, its constant
/// value, its forward values: `Run::keep`) is kept from one body's run to the next, as
/// `split_residues` keeps it from one class of remainders to the next. A term of the scope
/// reads none of a body's inputs: the scope binds every name it reads but a lambda's
/// parameters, which the transfer binds where it reads the lambda, and each body is numbered
/// afresh; so an entry keyed by a term of the scope holds for every body.
/// A definition reached from many bodies is so read once, and a chain of n functions, each
/// calling the one before, costs O(n) where closing each body over its cone cost O(n²)
/// (LOAD-chain). Each body's run also makes entries that depend on the body: its terms, the
/// scopes its calls bind, and what is found of a term in those scopes. These are dropped once
/// the body is read (`Fresh`), at a cost of what the body made, so that what is kept from
/// body to body is found of the scope alone: a chain of n tests, each calling the one before,
/// held O(n²) entries when every entry was kept, and holds O(n).
///
/// The translations into the linear-relation domain are kept from body to body as well
/// (`Translations`), each a function of its key alone: a call by its lambda and the linear
/// terms of its arguments, over the inputs' names, and a term of the scope, which reads no
/// input. A caller's relation so takes its callee's translation as made for an earlier body,
/// shared and not read again, and a chain of n tests `p{i}(x) = p{i-1}(x: x) && x > i` is
/// translated in O(n), where translating each body afresh read the chain once per body,
/// O(n²) (LOAD-chain-share). The auxiliary variables are numbered once for the scope, so a
/// kept translation that holds one serves every body; a relation is its body alone, its
/// definitions read from the scope ([`Scoped::def`]) and written, numbered from 0, by
/// [`Scoped::written`], and a chain whose links each define one (`x mod 7`) is translated in
/// O(n) as well, where dropping the translations of a body that made one read the chain once
/// per body (LOAD-chain-aux).
// Complexity tradeoff: naive version, each body closed over its cone and read with a fresh
// transfer, numbering and translating every definition it reaches again: O(n²) for a chain
// of n functions (LOAD-chain, 54 times from 100 to 800), and the same for a chain of tests
// that copy their callee's constraints (LOAD-chain-share, 62.6 times), define auxiliary
// variables (LOAD-chain-aux, 90.9 times) or pass moved arguments (LOAD-chain-args, 61.5
// times). Used: one numbering and one translation state for the scope; each body keeps
// what the runs before found and drops, in time of what it made, what depends on it; a
// call's relation is kept whole as one shared part, indexed by the names its arguments hold;
// a body whose call shifts or renames its parameters is read in the callee's coordinates
// (`Frame`). Each chain is about 8 times per 8 times the links. Tradeoffs: the scope holds
// O(n) entries for the unit's lifetime; a link the kept point does not extend, or a refused
// question in moved coordinates, is decided whole, O(n²) as before (the comments at
// `presburger::extend::Extending` and `front::linear_questions`). Tests in
// `l01_38_presburger::one_scope`: `the_questions_of_a_chain_of_calls_scale`,
// `the_questions_of_a_chain_of_tests_scale`,
// `the_questions_of_a_chain_defining_auxiliary_variables_scale` and
// `the_questions_of_a_chain_moving_its_argument_scale`; COMPLEXITY.md rows LOAD-chain,
// LOAD-chain-share, LOAD-chain-aux and LOAD-chain-args.
pub struct Scoped<'t> {
    tx: Tx<'t>,
    scope: Eid,
    /// The translations kept, with the `products` they were made under.
    kept: Option<(bool, Translations)>,
    /// The auxiliary variables of every relation read under the `products` of `kept`, each
    /// numbered once for the scope, so that a kept translation that holds one serves every
    /// body (LOAD-chain-aux).
    tr: Tr,
    /// Each function the scope's lets bind, by the address of its body: its lambda's term and
    /// the scope the lambda is read in, as a call of it reaches it ([`Callee::Lam`]), so that a
    /// body's relation is the one its callers share (LOAD-chain-affine). The address is a key
    /// only while the term is borrowed, and every key and every body looked up is borrowed for
    /// `'t`, the life of the scope; the map is read only by `get`, never iterated.
    lams: HashMap<*const Term, At>,
    /// The bodies read so far, for the names of the atoms of a body that is not one of `lams`.
    read: usize,
    /// For the relation read last, each atom its parameters stand for as the input it stands
    /// for, by which [`Scoped::written`] writes the relation over the inputs.
    back: HashMap<Arc<str>, Lin>,
}

/// The translation tables of a [`Memo`], kept by [`Scoped`] from one body to the next.
#[derive(Default)]
struct Translations {
    lin: HashMap<At, Entry<Option<Lin>>>,
    formula: HashMap<At, Entry<Option<Formula>>>,
    lin_calls: HashMap<CallKey, Entry<Option<Lin>>>,
    formula_calls: HashMap<CallKey, Entry<Option<Formula>>>,
    projections: HashMap<CallKey, Entry<Option<Projection>>>,
    defined: HashMap<At, Entry<Option<Defined>>>,
    defined_calls: HashMap<CallKey, Entry<Option<Defined>>>,
}

impl Memo {
    /// Takes the translation tables.
    fn take_translations(&mut self) -> Translations {
        Translations {
            lin: std::mem::take(&mut self.lin),
            formula: std::mem::take(&mut self.formula),
            lin_calls: std::mem::take(&mut self.lin_calls),
            formula_calls: std::mem::take(&mut self.formula_calls),
            projections: std::mem::take(&mut self.projections),
            defined: std::mem::take(&mut self.defined),
            defined_calls: std::mem::take(&mut self.defined_calls),
        }
    }

    /// Puts back the tables [`Memo::take_translations`] took.
    fn put_translations(&mut self, t: Translations) {
        (self.lin, self.formula) = (t.lin, t.formula);
        (self.lin_calls, self.formula_calls) = (t.lin_calls, t.formula_calls);
        self.projections = t.projections;
        (self.defined, self.defined_calls) = (t.defined, t.defined_calls);
    }
}

impl<'t> Scoped<'t> {
    /// The scope of `lets`, a chain of `let`s whose last body is never read: each name bound
    /// to its term, read in the scope of the names bound before it.
    pub fn new(lets: &'t Term) -> Self {
        let mut tx = Tx::new();
        tx.asking = true;
        tx.start(&Domains::new(), Marks::default());
        let mut t = tx.terms.add(lets);
        let mut scope = ROOT;
        let mut lams = HashMap::new();
        let mut named = Vec::new();
        while let Node::Let(n, e, b) = tx.node(t) {
            if let Node::Lam(_, body) = tx.node(e)
                && let Some(src) = tx.terms.src[body as usize]
            {
                lams.insert(src as *const Term, (e, scope));
            }
            if let Node::Lam(..) = tx.node(e) {
                named.push((n, e));
            }
            scope = tx.let_env(n, e, scope);
            t = b;
        }
        tx.classes = identity_classes(&tx, &named);
        Scoped {
            tx,
            scope,
            kept: None,
            tr: Tr::new(false),
            lams,
            read: 0,
            back: HashMap::new(),
        }
    }

    /// The scope, with each call that does not hold its callee's claim reading the callee's
    /// body again where an elimination over symbols alone does not write the callee, as before
    /// LOAD-call-relation: the reference against which the tests check the relations written
    /// from projections over quotients and remainders, refusals included.
    pub fn reading_bodies(mut self) -> Self {
        self.tr.bodies = true;
        self
    }

    /// The body of the relation the linear-relation domain states for the test `body` of
    /// parameters `params` over the free names `inputs`, the i-th parameter standing for the
    /// i-th input, read under the scope, its auxiliary variables defined by [`Scoped::def`]:
    /// the relation [`Scoped::written`] writes is the one [`relations`] states over `inputs`
    /// for `body` closed by the scope's lets, under lets outside them that bind each
    /// parameter to its input. A parameter so names its input whatever the scope binds, a
    /// prelude word or a definition of the unit; an input named like a prelude word, `min`,
    /// is the input. Products of two symbols are atoms when `products` holds, and then the
    /// relation holds the condition that the test's value is not an atom, as [`relations`]'s
    /// does (`Tr::definedness`, RUNG2-definedness). `None` when the
    /// body is outside the domain. Every parameter is read as an integer, as in [`relations`], so the
    /// caller asks only of a function whose parameters all hold `int`s alone (RUNG2-carrier). Time of the body, of the parameters and of the parts of the
    /// scope no earlier body read.
    ///
    /// The body of a function the scope binds is read over its parameters' canonical atoms
    /// (`Walk::canonical_formula`), the relation each claimed call of it shares, so a chain
    /// of n tests each calling the one before through affine arguments (`p(x: 2 * x)`,
    /// `p(x: x + 1, y: x + 1)`, `p(x: x, y: 5)`) is translated in O(n) (LOAD-chain-affine).
    pub fn relation(
        &mut self,
        body: &'t Term,
        params: &[Arc<str>],
        inputs: &[Arc<str>],
        products: bool,
    ) -> Option<Formula> {
        debug_assert_eq!(params.len(), inputs.len(), "one input for each parameter");
        let tx = &mut self.tx;
        tx.unbuilt = false;
        // The function's lambda, when the scope binds it with these parameters.
        let lam = (self.lams.get(&(body as *const Term)).copied()).filter(|&(l, _)| {
            let Node::Lam(ps, _) = tx.node(l) else {
                return false;
            };
            ps.len() == params.len()
                && (0..ps.len()).all(|i| tx.name(tx.param(ps, i)) == &params[i])
        });
        // The atom each parameter stands for: its class's atom ([`Tx::class`]), or a name of this body's own.
        self.read += 1;
        let atoms: Vec<Arc<str>> = match lam {
            Some((l, env)) => {
                let Node::Lam(ps, b) = tx.node(l) else {
                    unreachable!("a lambda")
                };
                (0..ps.len()).map(|i| tx.class(ps, i, (b, env))).collect()
            }
            None => (params.iter())
                .map(|p| format!("{p}#q{}", self.read).into())
                .collect(),
        };
        let doms: Domains = atoms
            .iter()
            .map(|n| (n.clone(), IntervalSet::top()))
            .collect();
        // A new run over the body's atoms, with what the runs before it found of the terms
        // without reading the inputs.
        let kept = tx.run.keep();
        tx.start(&doms, Marks::default());
        tx.run.restore(kept);
        tx.fresh = Some(Fresh::new(
            tx.terms.nodes.len() as Tid,
            tx.scopes.len() as Eid,
        ));
        // The translations the bodies before made under the same `products`.
        let m = &mut tx.run.memo;
        m.log.clear();
        match self.kept.take() {
            Some((p, t)) if p == products => m.put_translations(t),
            _ => {
                let bodies = self.tr.bodies;
                self.tr = Tr::new(products);
                self.tr.bodies = bodies;
                self.tr.definedness = products;
            }
        }
        // The relation, and the condition that the test's value is not an atom where the
        // relation must hold exactly where the test is `true` ([`Tr::definedness`]).
        let definedness = self.tr.definedness;
        let (body, defined) = match lam {
            Some(l) => {
                let body = tx.question(&mut self.tr, l);
                (
                    body,
                    definedness.then(|| tx.question_defined(&mut self.tr, l)),
                )
            }
            None => {
                // Each parameter bound to its atom, read where the scope binds nothing. The
                // atom's term is the body's own, so what is found of it is dropped with the
                // body's entries.
                let root = tx.terms.add(body);
                let mut scope = self.scope;
                for (p, x) in params.iter().zip(&atoms) {
                    let (p, x) = (tx.terms.name(p), tx.terms.name(x));
                    let to = (tx.terms.own_var(x), ROOT);
                    scope = tx.bind(scope, p, to);
                }
                let body = tx.formula(&mut self.tr, root, scope);
                (
                    body,
                    definedness.then(|| tx.defined(&mut self.tr, root, scope)),
                )
            }
        };
        let body = match (body, defined) {
            (body, None) => body,
            (Some(body), Some(Some(d))) => Some(match d.is_top() {
                true => body,
                false => Formula::and(vec![d.flat(&self.tr.sets), body]),
            }),
            _ => None,
        };
        tx.run.memo.log.clear();
        tx.drop_fresh();
        self.kept = Some((products, tx.run.memo.take_translations()));
        self.back = (atoms.into_iter().zip(inputs))
            .map(|(a, x)| (a, Lin::atom(presburger::Atom::Sym(x.clone()))))
            .collect();
        body
    }

    /// Whether the last [`Scoped::relation`] met a constant written as a power that could not be
    /// built in the memory the system gave (`Walk::built`), so that a relation of `None` is a
    /// refused question, not a body outside the domain. O(1).
    pub fn unbuilt(&self) -> bool {
        self.tx.unbuilt
    }

    /// The atoms a caller reads of `f`, a part of a relation [`Scoped::relation`] gave, when a
    /// call gave it: the canonical atoms its claimed call binds, or the atoms of the arguments
    /// its callee's body was read again at; `None` for another part, as a let-bound name's. The
    /// interface [`presburger::extend::Extending::defined_with`] reads (LOAD-call-summary).
    /// Time of the atoms.
    pub fn interface(&self, f: &Formula) -> Option<Vec<presburger::Atom>> {
        if matches!(f, Formula::Con(_)) {
            return None;
        }
        let atoms = self.tr.interfaces.get(&presburger::Id::any(f))?;
        Some(atoms.iter().cloned().collect())
    }

    /// The formula that defines the auxiliary variable `n` of a relation [`Scoped::relation`]
    /// gave, over the atoms it is made of: for the remainder of a pair, its quotient's, which
    /// defines both. Each holds for some value of `n` whatever the values of those atoms, as
    /// [`presburger::extend::Extending::defined`] needs. O(1).
    pub fn def(&self, n: u32) -> Formula {
        let n = n as usize;
        let at = if self.tr.defs[n].1.remainder() {
            n - 1
        } else {
            n
        };
        self.tr.defs[at].2.clone()
    }

    /// The relation of `body`, the body [`Scoped::relation`] gave last: over its inputs, each
    /// canonical atom written as what its call binds it to and the atom of a parameter as the
    /// input it stands for, a value a claimed call binds written as its callee's term, with the
    /// definitions it reaches, its auxiliary variables numbered from 0 in the order the scope
    /// numbered them; a binding's own variable is no definition, and its constraint, `b`
    /// equal to its own number, holds.
    /// It is the relation [`relations`] states for the body closed over the definitions it
    /// reaches, but for the numbering of the auxiliary variables when a definition was made
    /// for another body first. For a message and for tests: time of the body, of the
    /// definitions it reaches and of the terms the bindings give.
    pub fn written(&self, body: &Formula) -> Relation {
        use presburger::{Atom, Factor};
        let factors = |a: &Atom| -> Vec<Factor> {
            match a {
                Atom::Aux(n) => vec![Factor::Aux(*n)],
                Atom::Sym(s) => vec![Factor::Sym(s.clone())],
                Atom::Product(f, g) => vec![f.clone(), g.clone()],
            }
        };
        let auxes = |f: &Formula| -> Vec<u32> {
            (f.atoms().iter().flat_map(factors))
                .filter_map(|f| match f {
                    Factor::Aux(n) => Some(n),
                    Factor::Sym(_) => None,
                })
                .collect()
        };
        // The definitions reached, a binding's among them: its definition reaches what its
        // arguments and its callee's term are made of.
        let mut reached: Vec<u32> = Vec::new();
        let mut seen: HashSet<u32> = HashSet::new();
        let mut todo = auxes(body);
        while let Some(n) = todo.pop() {
            if !seen.insert(n) {
                continue;
            }
            reached.push(n);
            let (_, what, def) = &self.tr.defs[n as usize];
            todo.extend(auxes(def));
            if what.remainder() {
                todo.push(n - 1);
            }
        }
        // What each canonical atom is bound to, and each value a claimed call binds.
        let mut bound: HashMap<&Arc<str>, &Lin> = HashMap::new();
        let mut values: HashMap<u32, &Lin> = HashMap::new();
        reached.retain(|&n| match &self.tr.defs[n as usize].1 {
            What::Bind(pairs) | What::Value(_, pairs) => {
                bound.extend(pairs.iter().map(|(c, a)| (c, a)));
                if let What::Value(l, _) = &self.tr.defs[n as usize].1 {
                    values.insert(n, l);
                }
                false
            }
            _ => true,
        });
        reached.sort_unstable();
        let at: HashMap<u32, u32> = (reached.iter().enumerate())
            .map(|(i, &n)| (n, i as u32))
            .collect();
        // Each bound atom and value written over the inputs, each after the atoms its term is
        // made of: depth first on an explicit stack, each once (a chain of calls is as deep
        // as the chain). The bindings run from caller to callee, so they hold no cycle.
        let mut done: HashMap<Factor, Lin> = HashMap::new();
        let term = |f: &Factor| -> Option<&Lin> {
            match f {
                Factor::Sym(s) => bound.get(s).copied(),
                Factor::Aux(n) => values.get(n).copied(),
            }
        };
        let mut stack: Vec<(Factor, bool)> = Vec::new();
        let mut open: HashSet<Factor> = HashSet::new();
        for f in bound.keys().map(|&s| Factor::Sym(s.clone())) {
            stack.push((f, false));
        }
        stack.extend(values.keys().map(|&n| (Factor::Aux(n), false)));
        let plain = |f: &Factor, done: &HashMap<Factor, Lin>| -> Lin {
            if let Some(l) = done.get(f) {
                return l.clone();
            }
            match f {
                Factor::Aux(n) => Lin::atom(Atom::Aux(at[n])),
                Factor::Sym(s) => {
                    (self.back.get(s).cloned()).unwrap_or_else(|| Lin::atom(f.atom()))
                }
            }
        };
        while let Some((f, ready)) = stack.pop() {
            if done.contains_key(&f) {
                continue;
            }
            let l = term(&f).expect("a bound atom or value");
            if ready {
                let out = renumbered(l, &|g| plain(g, &done));
                done.insert(f, out);
                continue;
            }
            if !open.insert(f.clone()) {
                continue;
            }
            stack.push((f, true));
            for g in l.terms.keys().flat_map(factors) {
                if term(&g).is_some() && !done.contains_key(&g) && !open.contains(&g) {
                    stack.push((g, false));
                }
            }
        }
        let lin = |l: &Lin| renumbered(l, &|g| plain(g, &done));
        let binds = |c: &Con| {
            let mut terms = c.lin.terms.iter();
            matches!((terms.next(), terms.next()), (Some((Atom::Aux(n), _)), None)
                if matches!(self.tr.defs[*n as usize].1, What::Bind(_)))
        };
        let renumber = |f: &Formula| {
            f.map_cons(&|c| {
                if binds(c) {
                    return Formula::top();
                }
                Formula::Con(Con {
                    lin: lin(&c.lin),
                    rel: c.rel,
                })
            })
        };
        let defs = (reached.iter().enumerate())
            .map(|(i, &n)| {
                let (_, what, def) = &self.tr.defs[n as usize];
                (i as u32, what.written(Some(&lin)), renumber(def))
            })
            .collect();
        let bit_ands = (reached.iter().enumerate())
            .filter_map(|(i, &n)| match &self.tr.defs[n as usize].1 {
                What::BitAnd(a, b) => Some((i as u32, lin(a), lin(b))),
                _ => None,
            })
            .collect();
        Relation {
            body: renumber(body),
            defs,
            bit_ands,
        }
    }

    /// The number of scopes and remembered entries the scope holds from one body to the next:
    /// O(n) after n bodies, whatever the bodies read (LOAD-chain).
    pub fn held(&self) -> usize {
        let (tx, m) = (&self.tx, &self.tx.run.memo);
        let kept = self.kept.as_ref().map_or(0, |(_, t)| {
            t.lin.len()
                + t.formula.len()
                + t.lin_calls.len()
                + t.formula_calls.len()
                + t.projections.len()
        });
        kept + tx.scopes.len()
            + tx.scope_ids.len()
            + tx.powers.len()
            + tx.run.sums.len()
            + tx.run.fwds.len()
            + m.fwd.len()
            + m.constant.len()
            + m.mentions.len()
            + m.clip.len()
            + m.by_class.len()
            + m.reads_mod.len()
    }
}

/// The linear stage: the relation of the demand over the box `dom`, the box narrowed to its
/// projections and whether the box entails the relation, with the refusal that left the latter
/// undecided; or, where the solver refused a projection, the box with the bounds the box
/// stage gives the refused inputs ([`boxed_projections`]) and the refusal. `None` when the
/// term is outside the domain or the relation is refused.
#[allow(clippy::type_complexity)]
fn linear(
    tx: &mut Tx<'_>,
    root: Tid,
    dom: &Domains,
    demand: &Demand,
) -> Option<(
    Relation,
    Result<(Domains, bool, Option<Refusal>), (Domains, Refusal)>,
)> {
    tx.start(dom, Marks::default());
    let mut tr = Tr::new(false);
    tr.by_class = true;
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
        defs: tr.written(0),
        bit_ands: tr.bit_ands(0),
    };
    let go = || -> Result<(Domains, bool, Option<Refusal>), (Domains, Refusal)> {
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
        let (out, why, refused) = boxed_projections(&whole, dom, &syms);
        if is_empty(&out) {
            let none = out
                .keys()
                .map(|k| (k.clone(), IntervalSet::empty()))
                .collect();
            return Ok((none, true, None));
        }
        if let Some(cause) = refused {
            return Err((out, cause));
        }
        let outside = Formula::and(vec![
            rel.defined(),
            within(&out),
            Formula::negate(rel.body.clone()),
        ]);
        Ok(match presburger::decide(&outside) {
            Ok(meets) => (out, !meets, why),
            Err(why) => (out, false, Some(why)),
        })
    };
    let found = go();
    Some((rel, found))
}

/// The translation of terms into the linear-relation domain: the definitions of the auxiliary
/// variables made so far.
struct Tr {
    defs: Vec<(u32, What, Formula)>,
    products: bool,
    /// For each dividend and divisor that is not a constant, the number of the quotient of the
    /// pair [`Tr::div_mod_by_term`] made for them, so that `a div n` and `a mod n` share it.
    pairs: HashMap<(Lin, Lin), u32>,
    /// The keys of `pairs`, in the order made, so that [`Tr::truncate`] removes the pairs it
    /// undoes from the end.
    made: Vec<(Lin, Lin)>,
    /// Whether an `if` whose guard tests the remainder of an input by a constant is written by
    /// its summaries over the remainder's classes ([`Walk::lin_by_class`]): in the linear
    /// stage, whose inputs have the domains the summaries are read over.
    by_class: bool,
    /// For each form of an `if` [`Walk::lin_by_class`] wrote (its first term, [`Terms::form`]) and
    /// scope, the number of its variable: a copy of the term is the same variable.
    cases: HashMap<(Tid, Eid), u32>,
    /// The keys of `cases`, in the order made, for [`Tr::truncate`].
    cased: Vec<(Tid, Eid)>,
    /// The claimed call of each function, by its lambda's body and scope: the arguments'
    /// linear terms its canonical atoms are bound to, and the variable of the binding. A
    /// function has one, so each canonical atom has one binding (LOAD-chain-affine).
    claims: HashMap<At, (Vec<Lin>, u32)>,
    /// The keys of `claims`, in the order made, as `made` is for `pairs`.
    claimed: Vec<At>,
    /// The atoms a caller reads of each relation a call of a function gave, by the relation:
    /// the canonical atoms a claimed call binds, and the atoms of the arguments of a callee's
    /// body read again ([`Scoped::interface`], LOAD-call-summary). Kept when definitions are
    /// undone, since a stale entry only names atoms no question reads.
    interfaces: HashMap<presburger::Id, HashSet<presburger::Atom>>,
    /// Whether a call that does not hold its callee's claim reads the callee's body again
    /// where an elimination over symbols alone does not write the callee, as before
    /// LOAD-call-relation, rather than writing its projection over quotients and remainders
    /// ([`projected`], [`value_projected`]): the reference [`Scoped::reading_bodies`] gives the
    /// tests.
    bodies: bool,
    /// Whether a relation holds exactly where the interpreter's value of its test is `true`,
    /// a point where an operation fails included ([`relations`] for rung 2, RUNG2-definedness):
    /// the relation is the test's formula met with the condition that its value is not an atom
    /// ([`Walk::defined`]), and `==` and `!=` of operands that may fail compare the failures
    /// as the interpreter does ([`Walk::exactly_equal`]). Only a quotient or remainder by a
    /// term ([`Tr::div_mod_by_term`]) fails at a point of the domain.
    definedness: bool,
    /// The sets of divisors of the conditions [`Walk::defined`] makes ([`Defined`]).
    sets: DivisorSets,
    /// The numbers of the conditions' other parts, for the keys of calls
    /// ([`Walk::shared_call_key`]).
    numbers: FormulaNumbers,
}

impl Tr {
    fn new(products: bool) -> Tr {
        Tr {
            defs: Vec::new(),
            products,
            pairs: HashMap::new(),
            made: Vec::new(),
            by_class: false,
            cases: HashMap::new(),
            cased: Vec::new(),
            claims: HashMap::new(),
            claimed: Vec::new(),
            interfaces: HashMap::new(),
            bodies: false,
            definedness: false,
            sets: DivisorSets::default(),
            numbers: FormulaNumbers::default(),
        }
    }

    /// The definitions from `first` on, as a [`Relation`] lists them.
    fn written(&self, first: usize) -> Vec<(u32, String, Formula)> {
        (self.defs[first..].iter())
            .map(|(n, w, f)| (*n, w.to_string(), f.clone()))
            .collect()
    }

    /// The `bitAnd` variables from `first` on, as [`Relation::bit_ands`] lists them.
    fn bit_ands(&self, first: usize) -> Vec<(u32, Lin, Lin)> {
        (self.defs[first..].iter())
            .filter_map(|(n, w, _)| match w {
                What::BitAnd(a, b) => Some((*n, a.clone(), b.clone())),
                _ => None,
            })
            .collect()
    }

    /// Undoes the definitions from `mark` on, and the pairs and claims among them.
    fn truncate(&mut self, mark: usize) {
        self.defs.truncate(mark);
        while let Some(key) = self.made.last()
            && self.pairs[key] as usize >= mark
        {
            self.pairs.remove(key);
            self.made.pop();
        }
        while let Some(key) = self.cased.last()
            && self.cases[key] as usize >= mark
        {
            self.cases.remove(key);
            self.cased.pop();
        }
        while let Some(lam) = self.claimed.last()
            && self.claims[lam].1 as usize >= mark
        {
            self.claims.remove(lam);
            self.claimed.pop();
        }
    }

    /// Records that a caller reads the relation `f` of a call at the atoms of `at`, where `f`
    /// is a conjunction, a part a caller's relation may keep whole.
    fn bound(&mut self, f: &Formula, at: &[Lin]) {
        if matches!(f, Formula::And(_)) {
            let atoms = at.iter().flat_map(|l| l.terms.keys().cloned());
            self.interfaces
                .entry(presburger::Id::any(f))
                .or_default()
                .extend(atoms);
        }
    }

    /// Records the call `args` of the lambda `lam` as its claimed call, bound by the variable
    /// `n`.
    fn claim(&mut self, lam: At, args: Vec<Lin>, n: u32) {
        self.claims.insert(lam, (args, n));
        self.claimed.push(lam);
    }

    /// The number of the quotient of `a div c` and `a mod c` for a constant `c` other than 0,
    /// its remainder numbered after it: the pair made for `a` and `c` before, or a new one,
    /// `a == c·q + r` and `0 <= r <= |c| - 1` (Euclidean). One pair for each dividend and
    /// divisor, so that every `x mod m` and `x div m` of one input names the same quotient and
    /// remainder. O(log of the pairs) and the terms of `a`.
    // Complexity tradeoff: the divisor is an `Int` of any size (R5-CLAUDE-4), so its written
    // digits are the cost of each operation on it; the pair is found by the same key. Why: as
    // an `i128`, a divisor from `2^127` up was read as no constant and the question was
    // dropped with no message. Test: `l01_38_presburger::pncx_probe::pncx_divisor_past_i128_is_read`.
    fn pair_by_constant(&mut self, a: &Lin, c: &Int) -> u32 {
        let key = (a.clone(), Lin::constant(c.clone()));
        if let Some(&n) = self.pairs.get(&key) {
            return n;
        }
        let n = self.defs.len() as u32;
        self.pairs.insert(key.clone(), n);
        self.made.push(key);
        let (q, r) = (
            Lin::atom(presburger::Atom::Aux(n)),
            Lin::atom(presburger::Atom::Aux(n + 1)),
        );
        let def = Formula::and(vec![
            Formula::Con(Con::eq(a, &q.times(c.clone()).plus(&r))),
            Formula::Con(Con::ge(&r, &Lin::constant(0))),
            Formula::Con(Con::ge(&Lin::constant(&c.abs() - &Int::from(1)), &r)),
        ]);
        let shown = |op| What::ByConstant(op, a.clone(), c.clone());
        self.defs.push((n, shown("div"), def));
        self.defs.push((n + 1, shown("mod"), Formula::top()));
        n
    }

    /// The term `l` of a callee's relation, over the canonical atoms `to` maps, written at a
    /// call: each such atom replaced by its argument, and each quotient or remainder by a
    /// constant ([`Tr::pair_by_constant`]) by the pair of its dividend so written and the same
    /// divisor, which is the call's own, since a pair is a function of its dividend
    /// (LOAD-call-relation). The dividends are those of `pairs`, a [`Projection`]'s, or, without
    /// it, those of the definitions. `done` holds the pairs written so far, so each is written
    /// once for all the terms of one call. `None` when an atom is a product or another
    /// auxiliary variable, whose definition the call would need a copy of. Time of `l` and of
    /// the dividends it reaches not yet in `done`, times the log of the terms.
    fn instance(
        &mut self,
        l: &Lin,
        to: &HashMap<Arc<str>, Lin>,
        pairs: Option<&HashMap<u32, (Lin, Int)>>,
        done: &mut HashMap<u32, u32>,
    ) -> Option<Lin> {
        use presburger::Atom;
        // Each term added in place, O(log) for each atom, as [`at_arguments`] does.
        let mut terms: BTreeMap<Atom, Int> = BTreeMap::new();
        let mut constant = l.constant.clone();
        for (a, k) in &l.terms {
            let at = match a {
                Atom::Sym(s) => match to.get(s) {
                    Some(arg) => arg.clone(),
                    None => Lin::atom(a.clone()),
                },
                Atom::Aux(n) => {
                    // The quotient, and whether `n` is its remainder, with its dividend.
                    let (q, rem, a, c) = match pairs {
                        Some(pairs) => match pairs.get(n) {
                            Some((a, c)) => (*n, 0, a.clone(), c.clone()),
                            None => {
                                let q = n.checked_sub(1)?;
                                let (a, c) = pairs.get(&q)?;
                                (q, 1, a.clone(), c.clone())
                            }
                        },
                        None => {
                            let (m, what, _) = self.defs.get(*n as usize)?;
                            let (q, rem) = match what {
                                What::ByConstant("mod", ..) => (n.checked_sub(1)?, 1),
                                What::ByConstant(..) => (*n, 0),
                                _ => return None,
                            };
                            let What::ByConstant(_, a, c) = &self.defs.get(q as usize)?.1 else {
                                return None;
                            };
                            if *m != *n {
                                return None;
                            }
                            (q, rem, a.clone(), c.clone())
                        }
                    };
                    let p = match done.get(&q) {
                        Some(&p) => p,
                        None => {
                            let a = self.instance(&a, to, pairs, done)?;
                            let p = self.pair_by_constant(&a, &c);
                            done.insert(q, p);
                            p
                        }
                    };
                    Lin::atom(Atom::Aux(p + rem))
                }
                Atom::Product(..) => return None,
            };
            constant = &constant + &(k * &at.constant);
            for (b, d) in at.terms {
                let v = match terms.remove(&b) {
                    Some(o) => &o + &(k * &d),
                    None => k * &d,
                };
                if !v.is_zero() {
                    terms.insert(b, v);
                }
            }
        }
        Some(Lin { terms, constant })
    }

    fn aux(&mut self, what: What, def: Formula) -> presburger::Atom {
        let n = self.defs.len() as u32;
        self.defs.push((n, what, def));
        presburger::Atom::Aux(n)
    }

    /// `a div n`, for `p` `IntDiv`, or `a mod n`, for a divisor `n` that is not a constant:
    /// the quotient `q` and remainder `r` as auxiliary variables with `a == n * q + r` and
    /// `0 <= r <= |n| - 1` (Euclidean), `n * q` expanded into product atoms ([`Lin::product`]).
    /// The definition is one disjunct for each sign of `n`, so a premise that fixes the sign
    /// leaves one; where `n` is 0 the operation fails, and `q` and `r` are left free. A term
    /// that reads them is so not defined there, and [`relations`] meets each test with the
    /// condition that its value is not the failure ([`Walk::defined`]), so that nothing is
    /// proved or refuted of the free values (RUNG2-definedness). `a div n` and `a mod n` share
    /// the pair. `None` when `n` is a constant or holds a product.
    fn div_mod_by_term(&mut self, p: Prim, a: &Lin, n: &Lin) -> Option<Lin> {
        use presburger::Atom::Aux;
        if n.terms.is_empty() {
            return None;
        }
        let key = (a.clone(), n.clone());
        let pick = |k: u32| Lin::atom(Aux(if p == Prim::IntDiv { k } else { k + 1 }));
        if let Some(&k) = self.pairs.get(&key) {
            return Some(pick(k));
        }
        let k = self.defs.len() as u32;
        let (q, r) = (Lin::atom(Aux(k)), Lin::atom(Aux(k + 1)));
        // Complexity tradeoff: `n * q` is an atom, so a fact that needs it read as a product,
        // beyond the products of premise pairs that `presburger::products` adds, is not
        // proved. Why: integer arithmetic with products of variables is undecidable. Test:
        // `l01_38_presburger::mod_symbol::from_a_divisor_that_may_be_zero_neither_is_proved`.
        // COMPLEXITY.md row S39.
        // Naive version: integer arithmetic with products of variables, undecidable; used: `n * q`
        // as one atom, which keeps the fact in Presburger arithmetic, which the solver decides.
        let split = Con::eq(a, &n.product(&q)?.plus(&r));
        let zero = Lin::constant(0);
        // `s·n >= 1`, the split, and `0 <= r <= s·n - 1`.
        let sign = |s: i64| {
            let m = n.times(s);
            Formula::and(vec![
                Formula::Con(Con::ge(&m, &Lin::constant(1))),
                Formula::Con(split.clone()),
                Formula::Con(Con::ge(&r, &zero)),
                Formula::Con(Con::ge(&m.minus(&Lin::constant(1)), &r)),
            ])
        };
        let def = Formula::or(vec![sign(1), sign(-1), Formula::Con(Con::eq(n, &zero))]);
        let shown = |op| What::ByTerm(op, a.clone(), n.clone());
        self.defs.push((k, shown("div"), def));
        self.defs.push((k + 1, shown("mod"), Formula::top()));
        self.pairs.insert(key.clone(), k);
        self.made.push(key);
        Some(pick(k))
    }
}

/// What an auxiliary variable stands for, as a message writes it: kept as its parts, so that
/// a relation of a [`Scoped`] scope writes its variables numbered from 0 in its own order
/// ([`What::written`]), whatever the scope numbers them.
#[derive(Clone)]
enum What {
    /// `a div c` or `a mod c`, the operator first, for a constant `c`.
    ByConstant(&'static str, Lin, Int),
    /// `a div n` or `a mod n`, the operator first, for a term `n`.
    ByTerm(&'static str, Lin, Lin),
    /// `if g then a else b`.
    If(Formula, Lin, Lin),
    /// `abs(a)`.
    Abs(Lin),
    /// `min(a, b)`.
    Min(Lin, Lin),
    /// `max(a, b)`.
    Max(Lin, Lin),
    /// `bitAnd(a, b)`, which its definition bounds and does not fix ([`bit_and_bounds`]).
    BitAnd(Lin, Lin),
    /// `a1 if g1, a2 if g2, …`: the value `ai` where `gi` holds, the `gi` disjoint.
    Cases(Vec<(Formula, Lin)>),
    /// The binding of a claimed call of a test ([`Tr::claims`]): each canonical atom of its
    /// callee and the argument it is bound to. Its variable `b` is its own number, so that no
    /// two bindings look alike to the solver, and the call is its callee's relation and that
    /// equality.
    Bind(Vec<(Arc<str>, Lin)>),
    /// The value of a claimed call of an integer function: its callee's term over the
    /// canonical atoms, and the binding of each.
    Value(Lin, Vec<(Arc<str>, Lin)>),
}

impl What {
    /// Whether it is the remainder of a pair, defined by its quotient's formula, the one
    /// numbered before it.
    fn remainder(&self) -> bool {
        matches!(self, What::ByConstant("mod", ..) | What::ByTerm("mod", ..))
    }

    /// As a message writes it, each linear term `l` written `to(l)`, or as it is. Time of
    /// its parts.
    fn written(&self, to: Option<&dyn Fn(&Lin) -> Lin>) -> String {
        let l = |l: &Lin| match to {
            Some(to) => to(l),
            None => l.clone(),
        };
        let f = |g: &Formula| match to {
            Some(to) => g.map_cons(&|c| {
                Formula::Con(Con {
                    lin: to(&c.lin),
                    rel: c.rel,
                })
            }),
            None => g.clone(),
        };
        match self {
            What::ByConstant(op, a, c) => format!("{} {op} {c}", operand(&l(a))),
            What::ByTerm(op, a, n) => format!("{} {op} {}", operand(&l(a)), operand(&l(n))),
            What::If(g, a, b) => format!("if {} then {} else {}", f(g), l(a), l(b)),
            What::Cases(cases) => (cases.iter())
                .map(|(g, a)| format!("{} if {}", l(a), f(g)))
                .collect::<Vec<_>>()
                .join(", "),
            What::Abs(a) => format!("abs({})", l(a)),
            What::Min(a, b) => format!("min({}, {})", l(a), l(b)),
            What::Max(a, b) => format!("max({}, {})", l(a), l(b)),
            What::BitAnd(a, b) => format!("bitAnd({}, {})", l(a), l(b)),
            What::Bind(pairs) => bindings(pairs, &l),
            What::Value(v, pairs) if pairs.is_empty() => format!("{}", l(v)),
            What::Value(v, pairs) => format!("{} where {}", l(v), bindings(pairs, &l)),
        }
    }
}

/// The bounds of `x = bitAnd(a, b)`, one disjunct for each pair of signs of `a` and `b`, each
/// integer read as an infinite two's-complement word (L1.39d), so that the bounds hold for
/// every sign, not only the `int[0..]` operands L1.39a admits:
///
/// | `a`  | `b`  | rows                     |
/// |------|------|--------------------------|
/// | ≥ 0  | ≥ 0  | `0 <= x`, `x <= a`, `x <= b` |
/// | ≥ 0  | < 0  | `0 <= x`, `x <= a`       |
/// | < 0  | ≥ 0  | `0 <= x`, `x <= b`       |
/// | < 0  | < 0  | `x <= a`, `x <= b`       |
///
/// Each row holds since a bit of `x` is set only where it is set in both operands: `x` is
/// nonnegative where one operand is (its high bits are clear), and `x <= a` where `a` is
/// nonnegative (`x` is `a` with some bits cleared) or both are negative (`a - x` is the
/// nonnegative `a & !b`). `x <= a` fails where only `a` is negative: `bitAnd(-1, 5)` is 5. The
/// rows bound `x` and do not fix it, so the variable is listed in [`Relation::bit_ands`].
/// Plan row RUNG2-bit; test `l01_39a_bit_words::rung2`.
fn bit_and_bounds(x: &Lin, a: &Lin, b: &Lin) -> Formula {
    let zero = Lin::constant(0);
    let nonneg = |l: &Lin| Formula::Con(Con::ge(l, &zero));
    let neg = |l: &Lin| Formula::Con(Con::ge(&Lin::constant(-1), l));
    let below = |l: &Lin| Formula::Con(Con::ge(l, x));
    Formula::or(vec![
        Formula::and(vec![nonneg(a), nonneg(b), nonneg(x), below(a), below(b)]),
        Formula::and(vec![nonneg(a), neg(b), nonneg(x), below(a)]),
        Formula::and(vec![neg(a), nonneg(b), nonneg(x), below(b)]),
        Formula::and(vec![neg(a), neg(b), below(a), below(b)]),
    ])
}

/// The bindings `pairs`, as a message writes them: `c = a`, each argument written `l(a)`.
fn bindings(pairs: &[(Arc<str>, Lin)], l: &dyn Fn(&Lin) -> Lin) -> String {
    let each = pairs.iter().map(|(c, a)| format!("{c} = {}", l(a)));
    each.collect::<Vec<_>>().join(", ")
}

impl fmt::Display for What {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.written(None))
    }
}

/// `l` with each atom's factor `f` replaced by `to(f)`, a product of two factors by the product
/// of what they are replaced by. Time of the terms of `l` and of what they are replaced by,
/// times the log of their number.
fn renumbered(l: &Lin, to: &dyn Fn(&presburger::Factor) -> Lin) -> Lin {
    use presburger::{Atom, Factor};
    let mut out = Lin::constant(l.constant.clone());
    for (a, c) in &l.terms {
        let v = match a {
            Atom::Aux(n) => to(&Factor::Aux(*n)),
            Atom::Sym(s) => to(&Factor::Sym(s.clone())),
            Atom::Product(f, g) => (to(f).product(&to(g)))
                .expect("two factors, each replaced by a term with no product, multiply"),
        };
        out = out.plus(&v.times(c.clone()));
    }
    out
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
            revision::tonicity(&op(p, None)?, arg)
        }
        (Lt | Le, 0) | (Gt | Ge, 1) | (Not, 0) => Tonicity::Down,
        (Lt | Le, 1) | (Gt | Ge, 0) | (And | Or, _) => Tonicity::Up,
        _ => return None,
    };
    (t != Tonicity::None).then_some(t)
}

/// The revision table's operator for a primitive, with the constant exponent of `^`.
fn op(p: Prim, exponent: Option<Exponent>) -> Option<Op> {
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

/// How a product reads as a power: its first factor, the scope that factor is read in, and the
/// number of factors; `None` when two factors differ. A term that is not a product is its own
/// one factor.
type Power = Option<(Tid, Eid, Count)>;

/// The number of factors of a power, held exactly. Nested squaring names double the count at
/// each name, so the count at depth `d` has `d` bits.
#[derive(Clone)]
struct Count(Num);

impl Count {
    fn one() -> Count {
        Count(Num::ONE)
    }

    fn add(&self, other: &Count) -> Count {
        Count(&self.0 + &other.0)
    }

    /// Two or more factors.
    fn is_several(&self) -> bool {
        self.0 > Num::ONE
    }

    fn exponent(&self) -> Exponent {
        Exponent::Num(self.0.clone())
    }
}

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
    /// A literal compared with a value whose carrier is inferred: the value, the literal's
    /// own term, and the arms that give the literal at a float or a rational (DESIGN.md L1.26;
    /// [`follow_own`]).
    Follow(Tid, Tid, &'t [(Pattern, Term)]),
    /// A term the scalar catalog does not cover.
    Other,
}

/// The literal's own term in the match the elaborator writes for a literal compared with a
/// value whose carrier is inferred: an arm `is f64`, `is rat` or `is f32` for each carrier it follows,
/// each to a literal, and last the literal itself. Any other match is outside the catalog.
pub(super) fn follow_own(arms: &[(Pattern, Term)]) -> Option<&Term> {
    let ((Pattern::Wild, own), rest) = arms.split_last()? else {
        return None;
    };
    let carrier = |(p, v): &(Pattern, Term)| {
        matches!(p, Pattern::Is(t) if *t == Type::f64() || *t == Type::rat() || *t == Type::f32())
            && matches!(v, Term::Lit(_))
    };
    (!rest.is_empty() && rest.iter().all(carrier)).then_some(own)
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

/// The form of a term: its kind, its constant or name, and the forms of its parts, so that
/// two terms of one form compute the same in one scope ([`Terms::form`]).
#[derive(PartialEq, Eq, Hash)]
enum Form {
    Int(i64),
    Bool(bool),
    Var(Name),
    App(Tid, Vec<Tid>),
    Prim(std::mem::Discriminant<Prim>, Vec<Tid>),
    Let(Name, Tid, Tid),
    If(Tid, Tid, Tid),
    /// A literal of another kind, a literal that follows a carrier (`Node::Follow`, whose arms
    /// hold such literals), a lambda, a primitive as a value, or a term outside the catalog:
    /// the term itself.
    Own(Tid),
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
    ints: Vec<Num>,
    /// Each term's first term of the same form ([`Terms::form`]).
    forms: HashMap<Tid, Tid>,
    /// The given subterms reached more than once in one given term (one [`Shared`] held in
    /// two places), so that [`Walk::chain`] reads each through once.
    shared: HashSet<Tid>,
    by_form: HashMap<Form, Tid>,
    /// The given [`Shared`] each number held in one stands for, so that a result made of it
    /// ([`Tx::shared`]) holds it, not a copy.
    held: HashMap<Tid, &'t Shared>,
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

    /// Numbers `root` and its parts. A subterm the given term shares (one [`Shared`] reached
    /// twice) is numbered once: the walk keeps the shared subterms it has met by their ids, so
    /// it takes time of the term's distinct parts. A part held inline (the root, an argument)
    /// is reached only through its parent, so it is numbered when its parent is, with no
    /// lookup. Ids are only looked up, never ordered, so the numbers follow the walk alone.
    // Complexity tradeoff: the naive numbering walks the term as a tree, once per path, which
    // is exponential in depth where parts are shared (`k` branches over one shared arm: 18,554.7
    // times the work from 2 to 16 without the visited set). Used: an explicit stack and a
    // visited set of the shared parts' ids, linear in the distinct parts, with no recursion on
    // depth. Cost: a hash map entry per shared part for the call. Test:
    // `l01_25_preimage_catalog::scaling::long_shared_arms`; COMPLEXITY.md row S21.
    fn add(&mut self, root: &'t Term) -> Tid {
        let mut seen = HashMap::new();
        let mut todo = Vec::new();
        let r = self.number(root, &mut todo);
        while let Some((t, id)) = todo.pop() {
            let node = match t {
                Term::Lit(Value::Int(n)) => {
                    self.ints.push(Num::from(*n));
                    Node::Int(*n)
                }
                Term::Lit(Value::Bool(b)) => Node::Bool(*b),
                Term::Lit(v) => {
                    if let Value::Big(n) = v {
                        self.ints.push(Num::from(&**n));
                    }
                    Node::Lit(v)
                }
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
                    Node::App(f, self.ids(args, &mut todo))
                }
                Term::Prim(p, args) => Node::Prim(*p, self.ids(args, &mut todo)),
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
                Term::Match(v, arms) if let Some(own) = follow_own(arms) => Node::Follow(
                    self.id(v, &mut seen, &mut todo),
                    self.number(own, &mut todo),
                    &arms[..arms.len() - 1],
                ),
                _ => Node::Other,
            };
            self.nodes[id as usize] = node;
        }
        r
    }

    /// The number of the shared subterm `s`, numbered now and its parts left to `todo` when
    /// its id is new.
    fn id(
        &mut self,
        s: &'t Shared,
        seen: &mut HashMap<u64, Tid>,
        todo: &mut Vec<(&'t Term, Tid)>,
    ) -> Tid {
        use std::collections::hash_map::Entry as Seen;
        match seen.entry(s.id()) {
            Seen::Occupied(e) => {
                self.shared.insert(*e.get());
                *e.get()
            }
            Seen::Vacant(e) => {
                let t = self.number(s, todo);
                self.held.insert(t, s);
                *e.insert(t)
            }
        }
    }

    /// A new number for `t`, its parts left to `todo`.
    fn number(&mut self, t: &'t Term, todo: &mut Vec<(&'t Term, Tid)>) -> Tid {
        let id = self.nodes.len() as Tid;
        self.nodes.push(Node::Other);
        self.src.push(Some(t));
        todo.push((t, id));
        id
    }

    fn ids(&mut self, ts: &'t [Term], todo: &mut Vec<(&'t Term, Tid)>) -> Span {
        let at = self.kids.len();
        for t in ts {
            let id = self.number(t, todo);
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

    /// The first term numbered with the form of `t`: a term copied, which a given term is
    /// when it was cloned rather than shared, is one term here, so that what is kept by term
    /// ([`Walk::by_class`]) is computed once for every copy. `O(1)` per term, each read once.
    fn form(&mut self, t: Tid) -> Tid {
        if let Some(&f) = self.forms.get(&t) {
            return f;
        }
        let form = match self.nodes[t as usize] {
            Node::Int(n) => Form::Int(n),
            Node::Bool(b) => Form::Bool(b),
            Node::Var(x) => Form::Var(x),
            Node::App(f, args) => Form::App(self.form(f), self.forms(args)),
            Node::Prim(p, args) => Form::Prim(std::mem::discriminant(&p), self.forms(args)),
            Node::Let(x, e, b) => Form::Let(x, self.form(e), self.form(b)),
            Node::If(g, a, b) => Form::If(self.form(g), self.form(a), self.form(b)),
            Node::Lit(_) | Node::Lam(..) | Node::PrimFn(_) | Node::Follow(..) | Node::Other => {
                Form::Own(t)
            }
        };
        let f = *self.by_form.entry(form).or_insert(t);
        self.forms.insert(t, f);
        f
    }

    fn forms(&mut self, args: Span) -> Vec<Tid> {
        (0..args.len())
            .map(|i| self.form(args.get(&self.kids, i)))
            .collect()
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

    /// The name `x` as a term shared with no other: numbered past every term before it, so
    /// that what is found of it is dropped with the body that made it ([`Fresh`]).
    fn own_var(&mut self, x: Name) -> Tid {
        let t = self.nodes.len() as Tid;
        self.nodes.push(Node::Var(x));
        self.src.push(None);
        t
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

/// The cuts of the classes of each input and modulus the terms of a run compare
/// ([`Tx::remainder_cuts`]).
type CutTable = HashMap<(Name, i128), Rc<[i128]>>;

/// A term and the input and modulus whose classes [`Walk::by_class`] reads it over
/// ([`Tx::classes`]), `None` where it reads none.
type ClassKey = (At, Option<(Name, i128)>);

/// The landmarks of a run ([`Tx::landmarks`]): those found so far, and the domains whose
/// ends are landmarks too but are found only when a call first reads the landmarks
/// ([`Tx::marks`]).
#[derive(Clone, Default)]
struct Marks {
    known: Landmarks,
    ends_of: Option<Rc<Domains>>,
}

/// The finite ends of `pieces`, in order.
fn finite_ends<'a>(
    pieces: impl Iterator<Item = &'a (End, End)> + 'a,
) -> impl Iterator<Item = Num> + 'a {
    pieces.flat_map(|(a, b)| [a, b]).filter_map(|e| match e {
        Fin(v) => Some(v.clone()),
        _ => None,
    })
}

/// What one transfer over one box computes.
#[derive(Default)]
struct Run {
    stops: Vec<Stop>,
    /// The stops reported, by kind and term number: a term stopped at twice is reported once.
    seen: HashSet<(StopKind, Tid)>,
    /// The bodies of the lambdas whose calls are being read, each with its place on the stack.
    active: HashMap<Tid, usize>,
    marks: Marks,
    /// Whether `marks` holds the ends of the inputs of the context's reads ([`Tx::marks`]).
    marked: bool,
    /// The inputs of the run given another domain than the scope its reads were made in gives
    /// them ([`SummaryRead::scope_ints`]), by name: each read over its own where a read holds
    /// it ([`Tx::invert_read`]).
    shadow: Vec<(Arc<str>, Rc<IntervalSet>)>,
    /// The summaries met, each numbered once.
    sums: HashMap<Summary, u32>,
    /// The number the next summary met is given.
    sids: u32,
    fwds: HashMap<u32, Fwd>,
    backs: HashMap<(u32, Demand), Res>,
    scanned: HashSet<u32>,
    /// Whether an input's domain is empty, so that no point exists.
    void: bool,
    memo: Memo,
    /// The class of remainders the run is restricted to, by [`split_residues`].
    residue: Option<Residue>,
    /// In a run that is not split, the classes of the remainder that the `if` being read
    /// tests, over which [`Walk::by_class`] reads it ([`Walk::back_by_class`]).
    classes: Option<ClassCuts>,
    /// In a run that is not split, the cuts of the classes of each input and modulus the
    /// terms compare, found once ([`Tx::remainder_cuts`]).
    cut_table: Option<Rc<CutTable>>,
    /// The sets of integers of the forward transfer, shared ([`SharedInts`]).
    ints: SharedInts,
}

/// The sets of integers of one run's forward transfer that are found more than once, each
/// made once and shared ([`Ints`]): the domain of each input, each integer literal, and the
/// result of each operator on two sets. The guards of a chain of `k` levels each read `x mod
/// 1024` of their own copy of `x`: each copy's set is the one domain, so the remainder is
/// taken once, not `k` times over the `H` pieces of the domain (COMPLEXITY.md S22-fwd-holes).
#[derive(Default)]
struct SharedInts {
    /// By the domain's address, which the entry keeps alive: the entry's set is made from the
    /// domain's `Rc` itself (`Ints::shared`). The map is read only by `entry`, never iterated.
    inputs: HashMap<*const IntervalSet, Ints>,
    literals: HashMap<i64, Ints>,
    /// By the operator and the operands' ids ([`Ints::id`]), which no other set takes, even
    /// after the operands are dropped, so the entry need not hold them. No power: see `pows`.
    ops: HashMap<OpKey, Ints>,
    /// The powers, by the exponent and the operand's id ([`Ints::id`]).
    pows: HashMap<(Num, u64), Ints>,
}

/// An operator other than a power, and the ids of its two operands ([`Ints::id`]).
type OpKey = (std::mem::Discriminant<Op>, u64, u64);

/// The classes of remainders `x mod m` that [`Walk::by_class`] reads a term over: class `i`
/// is `cuts[i]..cuts[i + 1]`.
#[derive(Clone)]
struct ClassCuts {
    x: Name,
    m: i128,
    cuts: Rc<[i128]>,
}

/// A class of remainders: the run reads only the points whose input `x` has `x mod m` in
/// `class`, a set within `[0, m)`. The class is number `index` of those the split cuts at
/// `cuts`: class `i` is `cuts[i]..cuts[i + 1]`.
struct Residue {
    x: Name,
    m: i128,
    class: IntervalSet,
    index: usize,
    cuts: Rc<[i128]>,
    /// Whether the run read a guard on the remainder by itself ([`Walk::back_arith`]), not from
    /// the summary over every class ([`Walk::by_class`]).
    alone: bool,
}

/// What a run computes without reading its class of remainders, kept from one class's run to
/// the next by [`split_residues`]: the forward values, constants, inputs read, clips and
/// reaches, the summaries of calls by number with their forward values, the summaries over
/// every class ([`Walk::by_class`]), and the forward transfer's shared sets of integers
/// ([`SharedInts`]), which the runs find by the domains they share ([`Tx::begin`]).
#[derive(Default)]
struct Kept {
    sums: HashMap<Summary, u32>,
    sids: u32,
    fwds: HashMap<u32, Fwd>,
    fwd: HashMap<At, Entry<Fwd>>,
    constant: HashMap<At, Entry<Option<Value>>>,
    mentions: HashMap<At, Entry<Option<bool>>>,
    clip: HashMap<At, Entry<Option<IntervalSet>>>,
    by_class: HashMap<ClassKey, Entry<Option<ByClass>>>,
    reads_mod: HashMap<At, Entry<bool>>,
    ints: SharedInts,
}

impl Run {
    /// Takes what the run computed without reading its class.
    fn keep(&mut self) -> Kept {
        let m = &mut self.memo;
        Kept {
            sums: std::mem::take(&mut self.sums),
            sids: self.sids,
            fwds: std::mem::take(&mut self.fwds),
            fwd: std::mem::take(&mut m.fwd),
            constant: std::mem::take(&mut m.constant),
            mentions: std::mem::take(&mut m.mentions),
            clip: std::mem::take(&mut m.clip),
            by_class: std::mem::take(&mut m.by_class),
            reads_mod: std::mem::take(&mut m.reads_mod),
            ints: std::mem::take(&mut self.ints),
        }
    }

    /// Puts back what [`Run::keep`] took, at the start of a run over the same box.
    fn restore(&mut self, k: Kept) {
        let m = &mut self.memo;
        (self.sums, self.sids, self.fwds) = (k.sums, k.sids, k.fwds);
        (m.fwd, m.constant, m.mentions) = (k.fwd, k.constant, k.mentions);
        (m.clip, m.by_class) = (k.clip, k.by_class);
        m.reads_mod = k.reads_mod;
        self.ints = k.ints;
    }
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
    /// The integers it may be, shared with every value that holds them ([`Ints`]).
    ints: Ints,
    /// Whether it may be `true`, and `false`.
    bools: (bool, bool),
    /// Whether it may be a failure: an atom such as `#divByZero`, which every primitive but
    /// `==` and `!=` passes through.
    fails: bool,
    /// Whether it may be a value of another kind: a string, a float, a function.
    other: bool,
}

impl Fwd {
    fn int(ints: Ints) -> Fwd {
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
            ints: Ints::empty(),
            bools: (false, false),
            fails: false,
            other: false,
        }
    }

    fn top() -> Fwd {
        Fwd {
            ints: Ints::of(IntervalSet::top()),
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
            Demand::Ints(z) => self.is_int() && self.ints.set().is_subset(z),
            Demand::Bool(w) => self.is_bool() && !(if *w { self.bools.1 } else { self.bools.0 }),
        }
    }
}

/// What the transfer has computed, for each term and scope, so that a name bound once is
/// followed once however often it is read (the rule of low complexity, Part G), from
/// whichever summary it is read. The pair fixes the value: the inputs of the transfer are the
/// same in every context, and a parameter is read through the scope that binds it, which
/// differs for each summary, since the parameter's name holds the summary's number.
// Complexity tradeoff: the naive transfer reads a `let`-bound name's term again at each use,
// 2^k for `let`s k deep (296 ms at k = 14), O(n·depth) for `constant` read at every node, and
// with a memo per summary about n^1.8 through chains of calls (42 ms at 48, 727 ms at 384
// functions). Used: one memo per transfer, keyed by (term number, scope number), so each term
// is read once per scope it is read in: linear in the (term, scope) pairs reached, about
// n^1.2 measured on the call chains (5.9, 68 and 645 ms at 48, 384 and 3072). Tradeoffs:
// memory for every entry until the transfer ends; keys are numbers ([`Terms`], scopes by
// `scope_ids`), never addresses, so a number is not reused while kept. Nothing is refused
// here; no depth or fuel is counted (the old `TRANSFER_FUEL` and `CALL_DEPTH` are gone).
// Tests: `l01_25_preimage_catalog::scaling::the_transfer_scales`,
// `a_long_chain_of_lets_is_not_cut` and the `long_*` tests; COMPLEXITY.md rows S1, S1b, S6,
// S11, S19 and S21.
#[derive(Default)]
struct Memo {
    mentions: HashMap<At, Entry<Option<bool>>>,
    constant: HashMap<At, Entry<Option<Value>>>,
    /// The closed parts held in a [`Shared`], by the set of names bound within ([`Walk::close`]).
    close: HashMap<(At, Lid), Entry<Option<Shared>>>,
    fwd: HashMap<At, Entry<Fwd>>,
    back: HashMap<(At, Demand), Entry<Res>>,
    /// The piecewise-affine summary of an integer term of one input ([`Walk::pa`]).
    pa: HashMap<At, Entry<Option<Pa>>>,
    /// The interval an integer demand on a term is met with before it is read ([`Walk::clip`]).
    clip: HashMap<At, Entry<Option<IntervalSet>>>,
    /// The summaries of a term in every class of remainders of a split ([`Walk::by_class`]).
    by_class: HashMap<ClassKey, Entry<Option<ByClass>>>,
    /// Whether a term may read a remainder, so that its transfer may depend on a split's class
    /// ([`Walk::reads_mod`]).
    reads_mod: HashMap<At, Entry<bool>>,
    scan: HashSet<At>,
    lin: HashMap<At, Entry<Option<Lin>>>,
    formula: HashMap<At, Entry<Option<Formula>>>,
    /// The translations of calls, by the lambda and the translations of the arguments: a
    /// body's value depends on its parameters only through their values, so calls whose
    /// arguments translate alike translate alike, however they are reached.
    lin_calls: HashMap<CallKey, Entry<Option<Lin>>>,
    formula_calls: HashMap<CallKey, Entry<Option<Formula>>>,
    /// The relations of callees with every variable but their canonical atoms eliminated
    /// ([`Walk::projection`]), by the same keys as `formula_calls`.
    projections: HashMap<CallKey, Entry<Option<Projection>>>,
    /// The condition that a term's value is not an atom ([`Walk::defined`]).
    defined: HashMap<At, Entry<Option<Defined>>>,
    /// [`Memo::defined`] of calls whose arguments cannot fail, by the keys of `formula_calls`.
    defined_calls: HashMap<CallKey, Entry<Option<Defined>>>,
    /// The translation entries in the order they were made, which a translation that is
    /// undone removes.
    log: Vec<Logged>,
    /// The entries that hold only where the stack of lambdas being read holds what it held
    /// when they began ([`Entry`]), each with that height and what removes it, in the order
    /// they were made, so with heights that do not fall: [`Tx::leave`] removes those above
    /// the height it leaves the stack at.
    held: Vec<(usize, Unheld)>,
}

/// A memo entry: its value, and the lowest place on the stack of lambdas being read at which
/// a call it read stopped, where that place is below the stack's height when it began, or
/// `usize::MAX`. An entry of the first kind holds while the stack holds what it held then,
/// since its value depends on those lambdas alone, and is kept until the stack is lower; a
/// result that reads it stopped at that place too (ST-formula-k2-rec). The second kind holds
/// wherever it is reached.
type Entry<V> = (V, usize);

/// Removes an entry of the first kind of [`Entry`] from its table, unless the table holds
/// another entry under its key by then.
type Unheld = Box<dyn FnOnce(&mut Memo)>;

/// A call to translate: the lambda, by its body and scope, its arguments' linear terms, and,
/// when an argument may fail ([`Tr::definedness`]), the condition that each argument is not an
/// atom, by the number of its divisor set and of its other part ([`Walk::shared_call_key`]);
/// empty when none may.
type CallKey = (At, Vec<Lin>, Vec<(Set, u32)>);

/// A callee's relation with every variable but its canonical atoms and the inputs it reads
/// eliminated ([`Walk::projection`]): constraints over symbols, and over the quotients and
/// remainders by constants of `pairs` where an elimination over symbols alone would leave a
/// congruence (LOAD-call-relation).
#[derive(Clone)]
struct Projection {
    rows: Arc<[Con]>,
    /// For an integer function, its value term over the same atoms ([`value_projected`]).
    value: Option<Lin>,
    /// Each quotient the rows read, by its number (its remainder numbered after it): its
    /// dividend, over the symbols kept and the quotients and remainders numbered before it, and
    /// its divisor, a constant other than 0.
    pairs: Arc<HashMap<u32, (Lin, Int)>>,
}

/// The relation `r` of a callee over the canonical atoms of the canonical key `key`
/// ([`Walk::claimable`]) with each other variable eliminated ([`presburger::eliminated`]):
/// the auxiliary variables `r` reads, through the definitions in `tr` that define them, one
/// level after another, and the canonical atoms of the claimed calls in it, which their
/// bindings define. Each such variable has one value, or some, at each value of the atoms
/// kept, so the result holds at a value of the canonical atoms exactly where `r` holds with
/// the definitions at some values of the others: written at a call's arguments, it is the
/// callee's relation at them. Where an elimination over symbols alone leaves a variable (a
/// congruence), the quotients and remainders by constants are kept, over the bound atoms
/// written as what they are bound to ([`Normal`]), and their own definitions' rows dropped,
/// since the pairs [`Tr::instance`] makes at a call hold them there (LOAD-call-relation).
/// Each definition is read once (a visited set over the numbers). `None` when `r` or a
/// definition chooses (a disjunction or a negation), an atom is a product or an auxiliary
/// variable without a definition, a binding binds an atom of `key`, or an atom other than a
/// kept pair stays ([`presburger::eliminated`]).
// Complexity tradeoff: naive version, a call that does not hold its callee's claim reads the
// callee's body again, O(m) a call for a callee of m links, O(n·m) over a chain of n links.
// Used: the callee's canonical relation with every variable but the canonical atoms and the
// inputs eliminated (Fourier–Motzkin with the dark shadow, exact or nothing), made once per
// callee and key (`Memo::projections`) and written at each call's arguments, O(the rows left)
// a call (one or two rows for one parameter; 8.0 times the bytes from 50 to 400 links).
// Tradeoffs: memory for one projection per callee and key; where the relation or a
// definition chooses (a disjunction or a negation), reads a product, binds an atom of the key
// or leaves a variable (a congruence such as `x mod 4 == 1`), the body is read again as
// before. Test
// `l01_38_presburger::one_scope::the_questions_of_a_chain_with_a_second_call_of_a_large_callee_scale`;
// COMPLEXITY.md row LOAD-affine-cone.
fn projected(tr: &Tr, r: &Formula, key: &[Lin]) -> Option<Projection> {
    use presburger::Atom;
    let own: HashSet<&Arc<str>> = (key.iter().flat_map(|l| l.terms.keys()))
        .filter_map(|a| match a {
            Atom::Sym(s) => Some(s),
            _ => None,
        })
        .collect();
    let (mut rows, mut bound, mut seen) = (Vec::new(), HashSet::new(), HashSet::new());
    let mut todo = vec![r];
    while let Some(f) = todo.pop() {
        if f.chooses() {
            return None;
        }
        for c in f.cons() {
            for a in c.lin.terms.keys() {
                match a {
                    Atom::Product(..) => return None,
                    Atom::Aux(n) if seen.insert(*n) => {
                        let (m, what, _) = tr.defs.get(*n as usize)?;
                        // A remainder is defined by its quotient's formula, numbered before it.
                        let at = match what.remainder() {
                            true => n.checked_sub(1)?,
                            false => *n,
                        };
                        if m != n {
                            return None;
                        }
                        if at != *n && !seen.insert(at) {
                            continue;
                        }
                        let (_, what, def) = tr.defs.get(at as usize)?;
                        if matches!(def, Formula::And(gs) if gs.is_empty()) {
                            return None;
                        }
                        if let What::Bind(pairs) | What::Value(_, pairs) = what {
                            bound.extend(pairs.iter().map(|(c, _)| c.clone()));
                        }
                        todo.push(def);
                    }
                    Atom::Aux(_) | Atom::Sym(_) => {}
                }
            }
            rows.push(c.clone());
        }
    }
    if bound.iter().any(|c| own.contains(c)) {
        return None;
    }
    let keep = |a: &Atom| matches!(a, Atom::Sym(s) if !bound.contains(s));
    if let Some(out) = presburger::eliminated(&rows, &keep) {
        return Some(Projection {
            rows: out.into(),
            value: None,
            pairs: Arc::default(),
        });
    }
    // The tests' reference reads the body again at the call ([`Scoped::reading_bodies`]).
    if tr.bodies {
        return None;
    }
    // The elimination leaves a congruence (`x mod 4 == 1`), which no rows over the kept
    // symbols state: the quotients and remainders by constants are kept too, each a function
    // of its dividend, so [`Tr::instance`] writes it at a call as the pair of the dividend
    // written there (LOAD-call-relation). Each row is written over the kept symbols and pairs
    // ([`Normal`]), and pairs of one dividend and divisor are one: the links of a chain
    // `h{j}(x) = h{j-1}(x: x) && x mod 4 == 1` leave one pair, not one for each link.
    let mut normal = Normal::new(tr, &seen);
    let mut once: HashSet<Con> = HashSet::new();
    let mut written: Vec<Con> = Vec::with_capacity(rows.len());
    for c in &rows {
        let lin = normal.lin(&c.lin).unwrap_or_else(|| normal.renamed(&c.lin));
        if lin.terms.is_empty() {
            let holds = match c.rel {
                presburger::Rel::Ge => !lin.constant.is_negative(),
                presburger::Rel::Eq => lin.constant.is_zero(),
            };
            if holds {
                continue;
            }
        }
        let c = Con { lin, rel: c.rel };
        if once.insert(c.clone()) {
            written.push(c);
        }
    }
    let keep = |a: &Atom| match a {
        Atom::Sym(s) => !normal.binds.contains_key(s),
        Atom::Aux(n) => normal.kept(*n),
        Atom::Product(..) => false,
    };
    let rows = presburger::eliminated(&written, &keep)?;
    // The rows of each pair's own definition, which the pair [`Tr::instance`] makes at a call
    // holds there: the relation written at a call is the callee's read at it, in its shape.
    let mut defined: HashSet<Con> = HashSet::new();
    let reps: Vec<u32> = normal.reps.keys().copied().collect();
    for q in reps {
        for c in normal.tr.defs[q as usize].2.cons() {
            let lin = normal.lin(&c.lin).unwrap_or_else(|| normal.renamed(&c.lin));
            defined.insert(Con { lin, rel: c.rel });
        }
    }
    let rows: Vec<Con> = rows.into_iter().filter(|c| !defined.contains(c)).collect();
    Some(Projection {
        rows: rows.into(),
        value: None,
        pairs: normal.pairs(),
    })
}

/// The value term `l` of an integer callee over the canonical atoms of the canonical key
/// `key` ([`Walk::claimable`]) written over its canonical atoms and the inputs it reads, and
/// the quotients and remainders by constants of their terms ([`Normal`]): each value a claimed
/// call in it binds written as its callee's term so written, and each atom bound so as what it
/// is bound to (LOAD-call-relation). A call that does not hold the claim writes it at its
/// arguments ([`Tr::instance`]), O(the term and its pairs), where reading the body again costs
/// O(its cone). Each definition is read once (a visited set over the numbers). `None` when a
/// binding binds an atom of `key`, or an atom is a product or an auxiliary variable of
/// another kind (`if`, `min`, `abs`, a quotient by a term), whose definition a call would need
/// a copy of.
fn value_projected(tr: &Tr, l: &Lin, key: &[Lin]) -> Option<Projection> {
    use presburger::Atom;
    let own: HashSet<&Arc<str>> = (key.iter().flat_map(|l| l.terms.keys()))
        .filter_map(|a| match a {
            Atom::Sym(s) => Some(s),
            _ => None,
        })
        .collect();
    // Each auxiliary variable `l` reaches through the definitions, once.
    let mut seen: HashSet<u32> = HashSet::new();
    let mut todo: Vec<Lin> = vec![l.clone()];
    while let Some(t) = todo.pop() {
        for a in t.terms.keys() {
            let Atom::Aux(n) = a else { continue };
            if !seen.insert(*n) {
                continue;
            }
            let at = match tr.defs.get(*n as usize)?.1.remainder() {
                true => n.checked_sub(1)?,
                false => *n,
            };
            seen.insert(at);
            match &tr.defs.get(at as usize)?.1 {
                What::ByConstant(_, a, _) => todo.push(a.clone()),
                What::Value(v, pairs) => {
                    todo.push(v.clone());
                    todo.extend(pairs.iter().map(|(_, a)| a.clone()));
                }
                _ => return None,
            }
        }
    }
    let mut normal = Normal::new(tr, &seen);
    if normal.binds.keys().any(|c| own.contains(c)) {
        return None;
    }
    let value = normal.lin(l)?;
    Some(Projection {
        rows: Arc::default(),
        value: Some(value),
        pairs: normal.pairs(),
    })
}

/// The terms of a callee's relation written over the symbols no binding binds and the
/// quotients and remainders by constants of terms so written, one pair for each dividend and
/// divisor ([`projected`], [`value_projected`]): each atom a binding binds written as what it
/// is bound to, each value a claimed call of an integer function binds as its callee's term,
/// and each pair as the pair of its dividend so written. Exact, since the relation holds each
/// binding's equality and each pair is a function of its dividend. Each atom is written once
/// (a memo, filled with an explicit stack, since a chain of n links binds n atoms one to the
/// next), so all the terms together take time of the definitions read and of their own terms,
/// times the log of the terms.
struct Normal<'a> {
    tr: &'a Tr,
    /// What each bound atom is bound to.
    binds: HashMap<Arc<str>, Lin>,
    /// Each atom's written form, `None` where it is not written.
    memo: HashMap<presburger::Atom, Option<Lin>>,
    /// The representative of each dividend written and divisor: the first pair of them.
    by_key: HashMap<(Lin, Int), u32>,
    /// Each representative's dividend, written, and divisor.
    reps: HashMap<u32, (Lin, Int)>,
}

impl<'a> Normal<'a> {
    /// The bindings of the definitions `seen` holds.
    fn new(tr: &'a Tr, seen: &HashSet<u32>) -> Normal<'a> {
        let mut binds = HashMap::new();
        for &n in seen {
            if let What::Bind(pairs) | What::Value(_, pairs) = &tr.defs[n as usize].1 {
                binds.extend(pairs.iter().map(|(c, a)| (c.clone(), a.clone())));
            }
        }
        Normal {
            tr,
            binds,
            memo: HashMap::new(),
            by_key: HashMap::new(),
            reps: HashMap::new(),
        }
    }

    /// The atoms the written form of `a` is made from, and whether it is written as it is.
    fn parts(&self, a: &presburger::Atom) -> Option<Vec<presburger::Atom>> {
        use presburger::Atom;
        let atoms = |l: &Lin| l.terms.keys().cloned().collect::<Vec<_>>();
        match a {
            Atom::Sym(s) => Some(self.binds.get(s).map(atoms).unwrap_or_default()),
            Atom::Aux(n) => match &self.tr.defs.get(*n as usize)?.1 {
                What::ByConstant("mod", ..) => Some(vec![Atom::Aux(n.checked_sub(1)?)]),
                What::ByConstant(_, a, _) => Some(atoms(a)),
                What::Value(v, _) => Some(atoms(v)),
                _ => None,
            },
            Atom::Product(..) => None,
        }
    }

    /// The written form of `a`, its parts written first.
    fn atom(&mut self, a: &presburger::Atom) -> Option<Lin> {
        use presburger::Atom;
        if let Some(w) = self.memo.get(a) {
            return w.clone();
        }
        let mut stack: Vec<(Atom, bool)> = vec![(a.clone(), false)];
        let mut open: HashSet<Atom> = HashSet::new();
        while let Some((b, ready)) = stack.pop() {
            if self.memo.contains_key(&b) {
                continue;
            }
            let Some(parts) = self.parts(&b) else {
                self.memo.insert(b, None);
                continue;
            };
            if !ready {
                if !open.insert(b.clone()) {
                    // A binding that reaches itself.
                    self.memo.insert(b, None);
                    continue;
                }
                stack.push((b, true));
                for p in parts {
                    if !self.memo.contains_key(&p) {
                        stack.push((p, false));
                    }
                }
                continue;
            }
            let w = self.made(&b);
            self.memo.insert(b, w);
        }
        self.memo.get(a).cloned().flatten()
    }

    /// The written form of `a`, its parts' written forms in the memo.
    fn made(&mut self, a: &presburger::Atom) -> Option<Lin> {
        use presburger::Atom;
        match a {
            Atom::Sym(s) => match self.binds.get(s) {
                Some(to) => self.over(&to.clone()),
                None => Some(Lin::atom(a.clone())),
            },
            Atom::Aux(n) => match &self.tr.defs[*n as usize].1 {
                What::ByConstant("mod", ..) => {
                    let q = self.memo.get(&Atom::Aux(n - 1))?.clone()?;
                    let Some(Atom::Aux(q)) = q.terms.keys().next().cloned() else {
                        unreachable!("a quotient is written as a pair")
                    };
                    Some(Lin::atom(Atom::Aux(q + 1)))
                }
                What::ByConstant(_, d, c) => {
                    let (d, c) = (self.over(&d.clone())?, c.clone());
                    let r = *self.by_key.entry((d.clone(), c.clone())).or_insert(*n);
                    self.reps.entry(r).or_insert((d, c));
                    Some(Lin::atom(Atom::Aux(r)))
                }
                What::Value(v, _) => self.over(&v.clone()),
                _ => None,
            },
            Atom::Product(..) => None,
        }
    }

    /// `l` with each atom replaced by its written form in the memo. Time of the terms, times
    /// the log of their number.
    fn over(&self, l: &Lin) -> Option<Lin> {
        let mut terms: BTreeMap<presburger::Atom, Int> = BTreeMap::new();
        let mut constant = l.constant.clone();
        for (a, k) in &l.terms {
            let at = self.memo.get(a)?.as_ref()?;
            constant = &constant + &(k * &at.constant);
            for (b, d) in &at.terms {
                let v = match terms.remove(b) {
                    Some(o) => &o + &(k * d),
                    None => k * d,
                };
                if !v.is_zero() {
                    terms.insert(b.clone(), v);
                }
            }
        }
        Some(Lin { terms, constant })
    }

    /// The written form of `l`.
    fn lin(&mut self, l: &Lin) -> Option<Lin> {
        for a in l.terms.keys() {
            self.atom(a)?;
        }
        self.over(l)
    }

    /// `l` with each pair written replaced by its representative, other atoms as they are.
    fn renamed(&self, l: &Lin) -> Lin {
        use presburger::Atom;
        let mut terms: BTreeMap<Atom, Int> = BTreeMap::new();
        for (a, k) in &l.terms {
            let a = match (a, self.memo.get(a)) {
                (Atom::Aux(_), Some(Some(w))) if w.terms.len() == 1 && w.constant.is_zero() => {
                    match w.terms.iter().next() {
                        Some((b @ Atom::Aux(_), one)) if one.is_unit() && !one.is_negative() => {
                            b.clone()
                        }
                        _ => a.clone(),
                    }
                }
                _ => a.clone(),
            };
            let v = match terms.remove(&a) {
                Some(o) => &o + k,
                None => k.clone(),
            };
            if !v.is_zero() {
                terms.insert(a, v);
            }
        }
        Lin {
            terms,
            constant: l.constant.clone(),
        }
    }

    /// Whether `n` is a representative pair's quotient or remainder.
    fn kept(&self, n: u32) -> bool {
        self.reps.contains_key(&n) || n.checked_sub(1).is_some_and(|q| self.reps.contains_key(&q))
    }

    /// The representatives, as a [`Projection`] holds them.
    fn pairs(&self) -> Arc<HashMap<u32, (Lin, Int)>> {
        Arc::new(self.reps.clone())
    }
}

/// The classes of the parameters of the functions `lams` binds (each its name and lambda):
/// a call that passes a parameter of its caller as it is, `p(x: x)`, joins that parameter to
/// its callee's, and each class of two or more is given one atom, by its first parameter's
/// body and place (`x#5c0`), which no canonical atom ([`Tx::canonical`]) and no written name
/// holds. A function whose callers pass it their own parameters is then read once over the
/// class's atom for all of them, its callers' diamonds among them, `h(x: x)` called by both
/// `h2` and `p` (LOAD-chain-affine).
///
/// Two parameters of one function are never joined, since they would share an atom; nor is a
/// function that some call passes an argument not as it is (`p(x: x + 1)`, `p(x: 5)`): that
/// call binds its canonical atoms ([`Walk::binding`]), so its relation is read over them, and
/// a class holding it would read it a second time over the class's atom, its callees under
/// both reads, whose claims the two reads would then dispute, so each would be read again at
/// each call. Which join of two parameters of one function is refused depends on the order of
/// the calls; the class atoms are never bound, so any classes are sound.
///
/// Time of the functions' bodies, each part once (the terms share parts), and of the joins
/// ([`unite`]).
fn identity_classes(tx: &Tx, lams: &[(Name, Tid)]) -> HashMap<(Tid, usize), Arc<str>> {
    // Each function by its name, each parameter by its name, and the first node of each
    // function's parameters. A name bound twice is left out: its calls are not followed.
    let mut by_name: HashMap<Name, Option<usize>> = HashMap::new();
    let mut by_param: HashMap<Name, Option<(usize, usize)>> = HashMap::new();
    let mut first = Vec::with_capacity(lams.len() + 1);
    first.push(0);
    for (k, &(n, l)) in lams.iter().enumerate() {
        let Node::Lam(ps, _) = tx.node(l) else {
            unreachable!("a lambda")
        };
        by_name
            .entry(n)
            .and_modify(|e| *e = None)
            .or_insert(Some(k));
        for i in 0..ps.len() {
            (by_param.entry(tx.param(ps, i)))
                .and_modify(|e| *e = None)
                .or_insert(Some((k, i)));
        }
        first.push(first[k] + ps.len());
    }
    // The calls: each pair of parameters a call passes as it is, and each function a call
    // passes another argument. Each part once (`seen`).
    let mut joins: Vec<(usize, usize)> = Vec::new();
    let mut moved = vec![false; lams.len()];
    let mut seen: HashSet<Tid> = HashSet::new();
    for (k, &(_, l)) in lams.iter().enumerate() {
        let mut todo = vec![l];
        while let Some(t) = todo.pop() {
            if !seen.insert(t) {
                continue;
            }
            let kids = |s: Span| (0..s.len()).map(move |i| tx.arg(s, i));
            match tx.node(t) {
                Node::Lam(_, b) => todo.push(b),
                Node::App(f, args) => {
                    todo.push(f);
                    todo.extend(kids(args));
                    let callee = match tx.node(f) {
                        Node::Var(g) => by_name.get(&g).copied().flatten(),
                        _ => None,
                    };
                    let Some(c) = callee else { continue };
                    let Node::Lam(cps, _) = tx.node(lams[c].1) else {
                        unreachable!("a lambda")
                    };
                    if cps.len() != args.len() {
                        continue;
                    }
                    for j in 0..args.len() {
                        let own = match tx.node(tx.arg(args, j)) {
                            Node::Var(v) => by_param.get(&v).copied().flatten(),
                            _ => None,
                        };
                        match own {
                            Some((k2, i)) if k2 == k => joins.push((first[k] + i, first[c] + j)),
                            _ => moved[c] = true,
                        }
                    }
                }
                Node::Prim(_, args) => todo.extend(kids(args)),
                Node::Let(_, e, b) => todo.extend([e, b]),
                Node::If(g, a, b) => todo.extend([g, a, b]),
                Node::Follow(v, own, _) => todo.extend([v, own]),
                Node::Int(_)
                | Node::Bool(_)
                | Node::Lit(_)
                | Node::Var(_)
                | Node::PrimFn(_)
                | Node::Other => {}
            }
        }
    }
    // The joins of functions no call passes another argument.
    let owner = |v: usize| first.partition_point(|&f| f <= v) - 1;
    joins.retain(|&(a, b)| !moved[owner(a)] && !moved[owner(b)]);
    let (root, joined) = unite(&first, &joins);
    // Each class of two or more parameters named by its root.
    let mut out = HashMap::new();
    for (v, &r) in root.iter().enumerate() {
        if !joined[r] {
            continue;
        }
        let (k, i) = (owner(v), v - first[owner(v)]);
        let (rk, ri) = (owner(r), r - first[owner(r)]);
        let Node::Lam(_, body) = tx.node(lams[k].1) else {
            unreachable!("a lambda")
        };
        let Node::Lam(rps, rbody) = tx.node(lams[rk].1) else {
            unreachable!("a lambda")
        };
        out.insert(
            (body, i),
            format!("{}#{rbody}c{ri}", tx.name(tx.param(rps, ri))).into(),
        );
    }
    out
}

/// The classes of the parameters `0..` the last of `first`, those of function `k` numbered from
/// `first[k]`, after the joins `joins` in their order: the root of each parameter's class, and
/// whether a root's class holds two or more. A join is refused where the two classes hold
/// parameters of one function, so a class never holds two of one function.
///
/// Union by the number of functions in a class, each class's functions held at its root: a set
/// moves only into one at least as large, O(n log n) moves in all. A refusal is permanent, since
/// a class's functions only grow, so it is remembered for the two roots, and a join refused
/// again between those classes, or classes holding them, costs O(1); when a root joins a larger
/// class, its refusals move to that root with its functions, O(log n) moves each. Before the
/// smaller class's functions, the two functions of the join are looked up in the other class:
/// a join refused by its caller or its callee, `p(x: x, y: x)`, costs O(1).
// Complexity tradeoff: the first refusal between two classes that share only a third function
// (neither the join's caller nor its callee) looks through the smaller class's functions, O(m)
// for classes of m functions, so j such refusals between j distinct pairs of classes of m
// functions cost O(j m), up to about n^1.5 (a function of k parameters in k classes of k
// functions each, and k calls each joining one parameter to all k classes). Why: whether two
// classes share a function is a question of set disjointness, for which no structure answering
// in O(log n) a question is known. Trigger: a call joining one parameter
// to the classes of two parameters of a third function. Test
// `tests::refused_joins_between_two_large_classes_scale` (repeated refusals between two
// classes, the case remembered) and `tests::the_classes_are_those_of_a_join_refused_by_looking`
// (the answers of the plain union). COMPLEXITY.md row LOAD-affine-join. A complete solution
// would need a count per pair of classes sharing a function, which a function of k parameters
// starts at k(k - 1)/2 pairs.
fn unite(first: &[usize], joins: &[(usize, usize)]) -> (Vec<usize>, Vec<bool>) {
    fn find(parent: &mut [usize], mut v: usize) -> usize {
        while parent[v] != v {
            parent[v] = parent[parent[v]];
            v = parent[v];
        }
        v
    }
    let nodes = first.last().copied().unwrap_or(0);
    let owner = |v: usize| first.partition_point(|&f| f <= v) - 1;
    let mut parent: Vec<usize> = (0..nodes).collect();
    let mut funs: Vec<HashSet<usize>> = (0..nodes).map(|v| HashSet::from([owner(v)])).collect();
    let mut refused: Vec<HashSet<usize>> = vec![HashSet::new(); nodes];
    let mut joined = vec![false; nodes];
    for &(a, b) in joins {
        let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
        if ra == rb || refused[ra].contains(&rb) {
            continue;
        }
        let (big, small) = match funs[ra].len() >= funs[rb].len() {
            true => (ra, rb),
            false => (rb, ra),
        };
        if funs[rb].contains(&owner(a))
            || funs[ra].contains(&owner(b))
            || funs[small].iter().any(|x| funs[big].contains(x))
        {
            refused[ra].insert(rb);
            refused[rb].insert(ra);
            continue;
        }
        parent[small] = big;
        let f = std::mem::take(&mut funs[small]);
        funs[big].extend(f);
        for r in std::mem::take(&mut refused[small]) {
            refused[r].remove(&small);
            refused[r].insert(big);
            refused[big].insert(r);
        }
        joined[big] = true;
    }
    let root = (0..nodes).map(|v| find(&mut parent, v)).collect();
    (root, joined)
}

/// The term `l`, over the canonical atoms of the canonical key `key` ([`Walk::claimable`]),
/// with each of them replaced by its argument among `args`, when every atom of `l` is a
/// symbol: a callee whose relation is one such constraint, or whose value is one such term,
/// is written at its arguments, which costs O(the term and the arguments), and no binding is
/// needed, so the constraint joins those beside the call, and of two on one term the tighter
/// is kept ([`Formula::and`]): `p{i}(x) = p{i-1}(x: x) && x > i` stays one constraint at each
/// link. `None` when an atom is an auxiliary variable or a product, whose definitions read
/// the canonical atoms.
fn at_arguments(l: &Lin, key: &[Lin], args: &[Lin]) -> Option<Lin> {
    use presburger::Atom;
    let to: HashMap<&Arc<str>, &Lin> = (key.iter().zip(args))
        .filter_map(|(c, a)| match c.terms.keys().next()? {
            Atom::Sym(c) => Some((c, a)),
            _ => None,
        })
        .collect();
    // Each term added in place, O(log) for each atom of each argument.
    let mut terms = BTreeMap::new();
    let mut constant = l.constant.clone();
    let mut add = |a: &Atom, k: Int| {
        let v = match terms.remove(a) {
            Some(o) => &o + &k,
            None => k,
        };
        if !v.is_zero() {
            terms.insert(a.clone(), v);
        }
    };
    for (a, c) in &l.terms {
        let Atom::Sym(s) = a else {
            return None;
        };
        match to.get(s) {
            Some(arg) => {
                for (b, d) in &arg.terms {
                    add(b, c * d);
                }
                constant = &constant + &(c * &arg.constant);
            }
            None => add(a, c.clone()),
        }
    }
    Some(Lin { terms, constant })
}

/// Each canonical atom of the canonical key `key` ([`Walk::claimable`]) and its argument among
/// `args`, as [`Tr::instance`] reads them. Time of the key and the arguments.
fn arguments_of(key: &[Lin], args: &[Lin]) -> HashMap<Arc<str>, Lin> {
    use presburger::Atom;
    (key.iter().zip(args))
        .filter_map(|(c, a)| match c.terms.keys().next()? {
            Atom::Sym(c) => Some((c.clone(), a.clone())),
            _ => None,
        })
        .collect()
}

/// An entry of a translation memo.
enum Logged {
    Lin(At),
    Formula(At),
    LinCall(CallKey),
    FormulaCall(CallKey),
    Projection(CallKey),
    Defined(At),
    DefinedCall(CallKey),
}

/// One of the memo's tables.
type Table<K, V> = fn(&mut Memo) -> &mut HashMap<K, Entry<V>>;

/// A box made ready for runs over it ([`Tx::begin`]): their context and the fields of [`Run`]
/// that depend on the box alone.
struct Begun {
    cx: Cx,
    marked: bool,
    void: bool,
    shadow: Vec<(Arc<str>, Rc<IntervalSet>)>,
}

/// What [`Tx::start`] makes of the box `inputs` under the summaries `lets`, which depends on
/// the box alone: the context, with each domain shared, and the run's fields found from it.
fn begin(lets: &Lets, inputs: &Domains) -> Begun {
    let reads: Rc<[Arc<dyn SummaryRead>]> =
        (lets.values()).filter_map(|l| l.read.clone()).collect();
    let own: Sets = (inputs.iter())
        .map(|(k, v)| (k.clone(), Rc::new(v.clone())))
        .collect();
    // The reads of a run are made in one scope (`let_narrowing`).
    let shadow: Vec<_> = match reads.first() {
        Some(r) => (own.iter())
            .filter(|(k, d)| r.scope_ints(k).is_some_and(|w| *w != ***d))
            .map(|(k, d)| (k.clone(), d.clone()))
            .collect(),
        None => Vec::new(),
    };
    // An input of a read of no value has none unless `inputs` gives it another domain.
    let void = is_empty(inputs)
        || reads.iter().any(|r| {
            let given = (shadow.iter())
                .filter(|(k, _)| r.ints(k).is_some_and(IntervalSet::is_empty))
                .count();
            r.total().void > given
        });
    Begun {
        marked: reads.is_empty(),
        void,
        shadow,
        cx: Cx {
            inputs: own,
            reads,
            cut: usize::MAX,
        },
    }
}

/// A context: the inputs it reads, those of the transfer and the parameters of the summaries
/// it is within.
#[derive(Clone)]
struct Cx {
    inputs: Sets,
    /// The inputs of the summaries of [`Lets`] that are read through a tree of their bounds
    /// ([`LetIn::read`]), each found after those of `inputs`.
    reads: Rc<[Arc<dyn SummaryRead>]>,
    /// The lowest place on the stack of lambdas being read whose lambda a call stopped at,
    /// since the result being computed began. A result is remembered wherever it is reached
    /// only when that place is not below the stack's height when it began; otherwise it
    /// depends on the lambdas below that height, and is remembered while they are there
    /// ([`Entry`]).
    cut: usize,
}

impl Cx {
    /// The domain of the input `k`: of `inputs`, or else of a summary's read.
    fn get(&self, k: &str) -> Option<&IntervalSet> {
        match self.inputs.get(k) {
            Some(d) => Some(d),
            None => self.reads.iter().find_map(|r| r.ints(k)),
        }
    }

    /// [`Cx::get`], shared: `O(1)` beside the search for one of `inputs`, a copy for a read.
    fn rc(&self, k: &str) -> Option<Rc<IntervalSet>> {
        match self.inputs.get(k) {
            Some(d) => Some(d.clone()),
            None => self.get(k).map(|d| Rc::new(d.clone())),
        }
    }

    /// Whether `k` is an input ([`Cx::get`]).
    fn has(&self, k: &str) -> bool {
        self.get(k).is_some()
    }
}

/// The transfer: the terms and scopes, numbered, which outlive one box; what one run over a
/// box computes; and the context being read.
struct Tx<'t> {
    terms: Terms<'t>,
    scopes: Vec<Scope>,
    /// Each scope by the scope it extends and the binding it adds, so that a binding made
    /// twice gives one scope.
    scope_ids: HashMap<(Eid, Name, At), Eid>,
    /// How each product, by the term and scope its names lead to, reads as a power ([`Tx::power`]).
    /// It depends on the terms and scopes alone, so it outlives one box.
    powers: HashMap<At, Power>,
    /// The sets of names bound within the terms being closed. They depend on the terms alone,
    /// so they outlive one box.
    locals: Locals,
    run: Run,
    cx: Cx,
    /// The names bound by `let`s around the term, read through their summaries
    /// ([`let_preimage`]).
    lets: Lets,
    /// What the body being read by [`Scoped::relation`] made, which [`Tx::drop_fresh`] drops.
    fresh: Option<Fresh>,
    /// The atom of each parameter, by its lambda's body and its place, that one class of
    /// parameters passed as they are shares ([`identity_classes`]); a parameter of no class
    /// has its canonical atom ([`Tx::canonical`]).
    classes: HashMap<(Tid, usize), Arc<str>>,
    /// Within [`split_classes`], each set met with an input's domain ([`Tx::meet_domain`]), so
    /// that the classes whose runs meet one set with the domain share the result.
    split_meets: RefCell<Option<DomainMeets>>,
    /// Whether a constant the body being read holds could not be built ([`Walk::built`]).
    unbuilt: bool,
    /// Whether this transfer reads the questions of a scope ([`Scoped`]), where a constant
    /// written as a power is built ([`Walk::built`]); a preimage keeps it unbuilt.
    asking: bool,
}

/// The meets of sets with the inputs' domains, by the domain's address, which the entry keeps
/// alive, and the set. The address stays a key, not an id: a domain is a set of the lattice,
/// which carries none, and a scope may put a new domain for an input in the context while the
/// memo lives, which the address, held, tells apart from the one before. Only `get` and
/// `insert` read the map ([`Tx::meet_domain`]); it is never iterated.
type DomainMeets = HashMap<(*const IntervalSet, Rc<IntervalSet>), (Rc<IntervalSet>, Met)>;

/// A set met with an input's domain: empty, the whole domain, or a part of it.
#[derive(Clone)]
enum Met {
    Empty,
    Whole,
    Part(Rc<IntervalSet>),
}

/// What a body read under a [`Scoped`] scope made that depends on the body: the scopes made
/// since it began, and the entries keyed by its terms or by those scopes, in the order they
/// were made. An entry keyed by a term and a scope made before the body began depends on
/// neither: the scopes made before bind only the scope's own terms.
struct Fresh {
    /// The first term and the first scope made for the body.
    terms: Tid,
    scopes: Eid,
    /// Each removes one memo entry ([`Walk::made`]).
    memo: Vec<Unheld>,
    scope_ids: Vec<(Eid, Name, At)>,
    powers: Vec<At>,
    sums: Vec<Summary>,
}

impl Fresh {
    fn new(terms: Tid, scopes: Eid) -> Self {
        Fresh {
            terms,
            scopes,
            memo: Vec::new(),
            scope_ids: Vec::new(),
            powers: Vec::new(),
            sums: Vec::new(),
        }
    }

    /// Whether `at` depends on the body.
    fn of_body(&self, (t, env): At) -> bool {
        t >= self.terms || env >= self.scopes
    }
}

/// A memo key: the term and scope it is found at, with what else the entry depends on.
trait Key: Hash + Eq + Clone + 'static {
    fn at(&self) -> At;
}

impl Key for At {
    fn at(&self) -> At {
        *self
    }
}

impl<D: Hash + Eq + Clone + 'static> Key for (At, D) {
    fn at(&self) -> At {
        self.0
    }
}

impl Key for CallKey {
    fn at(&self) -> At {
        self.0
    }
}

impl<'t> Tx<'t> {
    fn new() -> Self {
        Tx {
            terms: Terms::default(),
            scopes: vec![Scope::new()],
            scope_ids: HashMap::new(),
            powers: HashMap::new(),
            locals: Locals::new(),
            run: Run::default(),
            cx: Cx {
                inputs: Sets::new(),
                reads: Rc::new([]),
                cut: usize::MAX,
            },
            fresh: None,
            lets: Lets::new(),
            classes: HashMap::new(),
            split_meets: RefCell::new(None),
            unbuilt: false,
            asking: false,
        }
    }

    /// Begins a run over the box `inputs`.
    fn start(&mut self, inputs: &Domains, marks: Marks) {
        let begun = self.begin(inputs);
        self.start_from(&begun, marks);
    }

    /// What [`Tx::start`] makes of the box `inputs` ([`begin`]).
    fn begin(&self, inputs: &Domains) -> Begun {
        begin(&self.lets, inputs)
    }
    /// Begins a run over the box [`Tx::begin`] made, which shares its domains: `O(s)` for its
    /// `s` shadowed inputs, however large the domains are.
    fn start_from(&mut self, begun: &Begun, marks: Marks) {
        self.run = Run {
            marks,
            marked: begun.marked,
            void: begun.void,
            shadow: begun.shadow.clone(),
            ..Run::default()
        };
        self.cx = begun.cx.clone();
    }

    /// The landmarks of the run ([`Tx::landmarks`]): the ends of the domains [`Marks`] holds,
    /// and those of the inputs of the summaries read through a tree ([`LetIn::read`]), are
    /// added the first time a lambda's call reads them, so that a run that calls none does not
    /// read those domains.
    ///
    /// Complexity tradeoff: the first call read in a run over such a summary of `k` inputs
    /// costs `O(k log k)` for their ends, also when it narrows none of them; a test that calls
    /// a lambda costs the inputs it does not narrow. Given up: the landmarks are a set made
    /// afresh for each run. Trigger: tests calling a lambda, of a name over many inputs. Test:
    /// none at scale; COMPLEXITY.md row PA-letpre-linear, residual. A complete solution would
    /// keep the ends of each summary's inputs in a persistent multiset beside its tree,
    /// changed in `O(log k)` for each input a scope narrows, and search it with the program's
    /// own landmarks.
    fn marks(&mut self) -> &Landmarks {
        if let Some(doms) = self.run.marks.ends_of.take() {
            let ends = doms.values().flat_map(|s| finite_ends(s.pieces()));
            self.run.marks.known.extend(&Landmarks::of(ends, []));
        }
        if !self.run.marked {
            self.run.marked = true;
            let mut ends = Vec::new();
            for r in self.cx.reads.iter() {
                for v in r.vars() {
                    // An input of the run of another domain has its own ends among the landmarks.
                    let pieces = self.cx.get(v).into_iter().flat_map(IntervalSet::pieces);
                    ends.extend(finite_ends(pieces));
                }
            }
            self.run.marks.known.extend(&Landmarks::of(ends, []));
        }
        &self.run.marks.known
    }

    /// The landmarks a summary's parameters and demands move out to: the terms' integer
    /// literals, the ends of the input domains and of the demand, each with its neighbors. A
    /// finite set, so a lambda has finitely many summaries. The ends of the input domains are
    /// kept as the domains themselves and found only when a call reads the landmarks
    /// ([`Tx::marks`]).
    ///
    /// Complexity tradeoff: the naive form built the whole set here, `O(p log p)` for the `p`
    /// pieces of the input domains, at every preimage, and copied it for each transfer over
    /// the box: `O(k p log p)` for `k` tests of one name with `p` holes, and `p` grows with `k`
    /// (`l01_39_reduced_product::xst::holes::laps_have_exact_ends_in_near_linear_time`, where
    /// it was 35% of the work at 256 names). Now this costs the terms' literals and the
    /// demand's ends, `O(t log t)`, and a run that reads no call never builds the rest; one
    /// that does pays `O(p log p)` once, the same set as before, so no result changes. Kept:
    /// one copy of the input domains, `O(1)` for each name, whose set of pieces is shared, not
    /// copied (INTERVAL-persistent). COMPLEXITY.md row LAPS-preimage-cost.
    fn landmarks(&self, inputs: &Domains, demand: &Demand) -> Marks {
        let demanded = match demand {
            Demand::Ints(z) => Some(z),
            Demand::Bool(_) => None,
        };
        let ints = (self.terms.ints.iter().cloned()).chain(finite_ends(
            demanded.into_iter().flat_map(IntervalSet::pieces),
        ));
        Marks {
            known: Landmarks::of(ints, []),
            ends_of: Some(Rc::new(inputs.clone())),
        }
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

    /// The input `x` and modulus `c` of the remainders `x mod c` the terms compare with
    /// constants, and the ends of the classes those constants cut `[0, |c|)` into, from `0` to
    /// `|c|`: `None` unless one input and one modulus are compared, in two or more classes.
    /// The time is that of the terms' nodes, and the sorting of the ends.
    fn residue_cuts(&self, inputs: &Domains) -> Option<(Name, i64, Vec<i128>)> {
        let mut table = self.remainder_cuts(|k| inputs.contains_key(k));
        if table.len() != 1 {
            return None;
        }
        let ((x, _), (c, cuts)) = table.drain().next()?;
        (cuts.len() > 2).then_some((x, c, cuts))
    }

    /// For each input `x` and modulus `m` of the remainders `x mod c` (`m = |c|`) the terms
    /// compare with constants, the first `c` met and the ends of the classes those constants
    /// cut `[0, m)` into, from `0` to `m`, sorted. The time is that of the terms' nodes, and
    /// the sorting of the ends.
    fn remainder_cuts(
        &self,
        is_input: impl Fn(&Arc<str>) -> bool,
    ) -> HashMap<(Name, i128), (i64, Vec<i128>)> {
        let mut table: HashMap<(Name, i128), (i64, Vec<i128>)> = HashMap::new();
        for t in 0..self.terms.nodes.len() as Tid {
            let Node::Prim(Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge | Prim::Eq | Prim::Ne, args) =
                self.node(t)
            else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let (a, b) = (self.arg(args, 0), self.arg(args, 1));
            for (r, v) in [(a, b), (b, a)] {
                let (Node::Prim(Prim::Mod, margs), Node::Int(v)) = (self.node(r), self.node(v))
                else {
                    continue;
                };
                if margs.len() != 2 {
                    continue;
                }
                let (Node::Var(x), Node::Int(c)) =
                    (self.node(self.arg(margs, 0)), self.node(self.arg(margs, 1)))
                else {
                    continue;
                };
                if c == 0 || !is_input(self.name(x)) {
                    continue;
                }
                // `x mod c` and `x mod -c` are the same remainder.
                let m = c.unsigned_abs() as i128;
                let (_, cuts) = table.entry((x, m)).or_insert_with(|| (c, vec![0, m]));
                cuts.extend([v as i128, v as i128 + 1].map(|e| e.clamp(0, m)));
            }
        }
        for (_, cuts) in table.values_mut() {
            cuts.sort_unstable();
            cuts.dedup();
        }
        table
    }

    /// The classes [`Walk::by_class`] reads over: the split's, or in a run that is not split
    /// those set by [`Walk::back_by_class`].
    fn classes(&self) -> Option<ClassCuts> {
        match &self.run.residue {
            Some(r) => Some(ClassCuts {
                x: r.x,
                m: r.m,
                cuts: r.cuts.clone(),
            }),
            None => self.run.classes.clone(),
        }
    }

    /// The classes of the remainder of `x` by `m` in a run that is not split, from the cuts of
    /// every input and modulus the terms compare, found on the first call: `None` unless the
    /// constants compared cut `[0, m)` into two or more classes.
    fn classes_of(&mut self, x: Name, m: i128) -> Option<ClassCuts> {
        if self.run.cut_table.is_none() {
            let cx = &self.cx;
            let table = (self.remainder_cuts(|k| cx.has(k)).into_iter())
                .filter(|(_, (_, cuts))| cuts.len() > 2)
                .map(|(k, (_, cuts))| (k, cuts.into()))
                .collect();
            self.run.cut_table = Some(Rc::new(table));
        }
        let cuts = self.run.cut_table.as_ref()?.get(&(x, m))?.clone();
        Some(ClassCuts { x, m, cuts })
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
        if let Some(fresh) = &mut self.fresh {
            fresh.scope_ids.push(k);
        }
        e
    }

    /// The set `local` with `x` bound by the binder `binder`, made once for each set and
    /// binding, and the name `x` is closed to.
    fn bind_local(&mut self, local: Lid, x: Name, binder: Tid) -> (Lid, Arc<str>) {
        let k = (local, x, binder);
        if let Some(made) = self.locals.ids.get(&k) {
            return made.clone();
        }
        let to: Arc<str> = format!("{}\u{0}{binder}", self.name(x)).into();
        let set = self.locals.sets[local as usize].update(x, to.clone());
        let l = self.locals.sets.len() as Lid;
        self.locals.sets.push(set);
        self.locals.ids.insert(k, (l, to.clone()));
        (l, to)
    }

    /// Records `at` as read as a power: `p`.
    fn power_made(&mut self, at: At, p: Power) {
        self.powers.insert(at, p);
        if let Some(fresh) = &mut self.fresh
            && fresh.of_body(at)
        {
            fresh.powers.push(at);
        }
    }

    /// Drops what the body read by [`Scoped::relation`] made ([`Fresh`]), in time of what it
    /// made. The entries go first, since the scopes they are keyed by are numbered again.
    fn drop_fresh(&mut self) {
        let Some(fresh) = self.fresh.take() else {
            return;
        };
        for remove in fresh.memo {
            remove(&mut self.run.memo);
        }
        for at in &fresh.powers {
            self.powers.remove(at);
        }
        for s in &fresh.sums {
            if let Some(sid) = self.run.sums.remove(s) {
                self.run.fwds.remove(&sid);
            }
        }
        for k in &fresh.scope_ids {
            self.scope_ids.remove(k);
        }
        self.scopes.truncate(fresh.scopes as usize);
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

    /// The term `t` stands for, held in a [`Shared`]: the given one where `t` is a part held in
    /// one, otherwise a new one around [`Tx::term`].
    fn shared(&self, t: Tid) -> Shared {
        match self.terms.held.get(&t) {
            Some(&s) => s.clone(),
            None => Shared::new(self.term(t)),
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
                (Node::Follow(v, x, a), Node::Follow(w, y, b)) if a == b => {
                    todo.extend([(v, w), (x, y)])
                }
                (Node::Other, Node::Other)
                    if self.terms.src[a as usize] == self.terms.src[b as usize] => {}
                _ => return false,
            }
        }
        true
    }

    /// Puts the lambda whose body is `body` on the stack of lambdas being read and gives its
    /// place, or, when it is already there, reports the stop and gives `None`, since that call
    /// would make the same call again. The stack holds distinct lambdas, so it is no higher
    /// than the number of lambdas in the term. [`Tx::leave`] ends the read.
    fn enter(&mut self, t: Tid, body: Tid) -> Option<usize> {
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
            // Naive version: the call read again at each depth it may reach, which need not
            // end; used: the stop, O(1) at the call cycle, the inputs keeping their forward
            // intervals.
            self.cx.cut = self.cx.cut.min(at);
            self.stop(StopKind::Recursion, t);
            return None;
        }
        let place = self.run.active.len();
        self.run.active.insert(body, place);
        Some(place)
    }

    /// Takes the lambda whose body is `body`, at `place`, off the stack of lambdas being read.
    fn leave(&mut self, body: Tid, place: usize) {
        self.run.active.remove(&body);
        let m = &mut self.run.memo;
        while let Some((_, unheld)) = m.held.pop_if(|(at, _)| *at > place) {
            unheld(m);
        }
    }

    /// Enters the context a summary is computed in: the inputs and the call's parameters. Gives
    /// the context left, for [`Tx::shut`], and the lambda's scope with its parameters bound.
    fn open(&mut self, call: &Call, lam: Eid) -> (Cx, Eid) {
        let mut inputs = self.cx.inputs.clone();
        for (_, n, d) in &call.params {
            inputs.insert(n.clone(), Rc::new(d.clone()));
        }
        let mut e = lam;
        for &(p, to) in &call.binds {
            e = self.bind(e, p, to);
        }
        let sub = Cx {
            inputs,
            reads: self.cx.reads.clone(),
            cut: usize::MAX,
        };
        (std::mem::replace(&mut self.cx, sub), e)
    }

    /// Returns to the context `outer`, and gives the lowest place a call in the one left
    /// stopped at.
    fn shut(&mut self, outer: Cx) -> usize {
        std::mem::replace(&mut self.cx, outer).cut
    }

    /// Whether a summary computed in a context whose calls stopped no lower than `cut`, for
    /// the lambda at `place`, holds wherever it is reached; the stops below it are passed on.
    fn closes(&mut self, cut: usize, place: usize) -> bool {
        self.cx.cut = self.cx.cut.min(cut);
        cut >= place
    }

    /// Removes the translation's entries made after the first `mark`, but for those that found
    /// no translation wherever they are reached (`None`, with no stop below them): a failure
    /// names no auxiliary variable, so undoing the attempt does not touch it.
    ///
    /// Complexity tradeoff: the naive version removed every entry the undone attempt made, the
    /// failures too. A chain of n functions each multiplying the one before by a parameter
    /// (`h(x) * x + 1`) fails at each body's comparison, and each body then read the chain
    /// below it again: O(n) per body, O(n²) for the n bodies (LOAD-chain-sep-nonlinear). Kept,
    /// a failure is found again in O(1), so the chain costs O(n). Tradeoff: a kept failure
    /// stays in the table for the scope's later bodies, as a success does. Test:
    /// `l01_38_presburger::one_scope::separate_tests_over_a_chain_of_products_scale`;
    /// COMPLEXITY.md row LOAD-chain-sep-nonlinear.
    ///
    /// Undo log or persistent snapshot (T11-preimage-log, measured 2026-11-12). The undo log
    /// costs O(1) per entry made (one push) and O(k) at `forget` for the k entries made since
    /// the mark, each already paid once to make. A persistent snapshot (the seven tables as
    /// `imbl::HashMap`) takes the snapshot and restores it in O(1), but pays O(log n) with a
    /// larger constant on every lookup and insert, and still needs the log to put back the
    /// kept failures above. Measured by instruction counts at n and 8n, the snapshot was
    /// no faster anywhere (at best 0.99x, within noise): 1.10x and 1.16x the instructions on
    /// `tests_that_forget_deep_and_wide_translations_scale` (where each `forget` undoes 800 to
    /// 6400 entries), 1.41x and 1.43x on chains of `&&` and `||` reading one shared chain,
    /// 1.01x (geometric mean) over all 134 scaling rows of l01_25, l01_38 and l01_39, and 1.5x
    /// to 2.2x the bytes on the two tests named. So the log stays. Test of the undo itself:
    /// `a_test_after_a_failed_test_reading_the_same_call_keeps_its_answer` (with a `forget`
    /// that removes nothing it panics on the stale auxiliary pair).
    fn forget(&mut self, mark: usize) {
        fn undo<K: Hash + Eq, V>(t: &mut HashMap<K, Entry<Option<V>>>, k: &K) {
            if t.get(k)
                .is_some_and(|(v, cut)| v.is_some() || *cut != usize::MAX)
            {
                t.remove(k);
            }
        }
        let m = &mut self.run.memo;
        for e in m.log.drain(mark..) {
            match e {
                Logged::Lin(k) => undo(&mut m.lin, &k),
                Logged::Formula(k) => undo(&mut m.formula, &k),
                Logged::LinCall(k) => undo(&mut m.lin_calls, &k),
                Logged::FormulaCall(k) => undo(&mut m.formula_calls, &k),
                Logged::Projection(k) => undo(&mut m.projections, &k),
                Logged::Defined(k) => undo(&mut m.defined, &k),
                Logged::DefinedCall(k) => undo(&mut m.defined_calls, &k),
            }
        }
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

    /// Whether the box `r` holds no point of the inputs, as [`Tx::whole`] gives it.
    fn none(&self, r: &Res) -> bool {
        r.none || (self.run.void && !r.dom.is_empty())
    }

    /// The box over every input, those of the reads ([`LetIn::read`]) included. A box that
    /// narrows a name of an empty domain is empty in every name, as a box found empty is; one
    /// that narrows nothing keeps the domains.
    fn whole(&self, r: &Res) -> Domains {
        let none = self.none(r);
        let of = |k: &Arc<str>, z: &IntervalSet| {
            let z = match r.dom.get(k) {
                _ if none => IntervalSet::empty(),
                Some(n) => (**n).clone(),
                None => z.clone(),
            };
            (k.clone(), z)
        };
        let mut out: Domains = self.cx.inputs.iter().map(|(k, z)| of(k, z)).collect();
        for read in self.cx.reads.iter() {
            for v in read.vars() {
                if !out.contains_key(v)
                    && let Some(z) = read.ints(v)
                {
                    let (k, z) = of(v, z);
                    out.insert(k, z);
                }
            }
        }
        out
    }

    /// The names of the inputs `r` narrows, each with the box's set, or `None` when the box
    /// holds no point ([`Tx::whole`], which gives the others their domains): `O(m log k)` for
    /// the `m` it narrows, however many inputs the reads hold.
    fn narrowed(&self, r: &Res) -> Option<Domains> {
        if self.none(r) {
            return None;
        }
        let narrowed = (r.dom.iter()).filter(|(k, _)| self.cx.has(k));
        Some(narrowed.map(|(k, n)| (k.clone(), (**n).clone())).collect())
    }

    /// Reports a stop at `t`, once for each kind. The term is held, not printed
    /// ([`Stop`]).
    // Complexity tradeoff: the naive stop printed its term when reported and kept the text
    // in a set of texts, `O(s)` for a term of printed size `s` (exponential in depth where
    // parts are shared), at each of `k` places that stop over one term: `O(k s)`. Used: the
    // stop holds the term ([`Tx::shared`], `O(1)` for a part held in a [`Shared`], a copy of
    // the parts held inline otherwise) and is kept by kind and term number, `O(1)`; the text
    // is made only when read ([`Preimage::stop_texts`]). Cost: copies of one term that print
    // alike are separate stops until read. Test:
    // `l01_25_preimage_catalog::stops::many_stops_over_one_shared_term_make_no_text`;
    // COMPLEXITY.md row S21.
    fn stop(&mut self, kind: StopKind, t: Tid) -> Res {
        if self.run.seen.insert((kind.clone(), t)) {
            let term = self.shared(t);
            self.run.stops.push(Stop { kind, term });
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
            if self.cx.get(k).is_none_or(|z| *z != joined) {
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

    /// The product `t` as a power, when it multiplies two or more factors that are all the same
    /// term: that factor, the scope it is read in, and the number of factors. Any number of
    /// factors is read (DESIGN.md sec:constraints, "How a constraint reaches the domains").
    fn power(&mut self, t: Tid, env: Eid) -> Option<(Tid, Eid, Exponent)> {
        let at = self.followed(t, env);
        self.read_powers(at);
        match &self.powers[&at] {
            Some((f, fe, k)) if k.is_several() => Some((*f, *fe, k.exponent())),
            _ => None,
        }
    }

    /// The term and scope that `t`, read in `env`, stands for once its names are followed.
    fn followed(&self, t: Tid, env: Eid) -> At {
        let (mut t, mut env) = (t, env);
        while let Node::Var(x) = self.node(t)
            && let Some(to) = self.lookup(env, x)
        {
            (t, env) = to;
        }
        (t, env)
    }

    /// Reads `at` and each product under it as a power ([`Tx::powers`]), the operands of a
    /// product before the product, on an explicit stack, since a product of `k` factors can be
    /// `k` deep. Each product is read once and compares the first factors of its two operands
    /// once, so the cost is linear in the products reached plus the size of the factors
    /// compared, however the products share operands.
    // Complexity tradeoff: the naive reading gathers each product's factors again, walking
    // down to its first factor, O(n·depth), n² for a chain of n factors (85.2M to 2,652M
    // instructions at 512 and 4,096 factors, 31.1 times). Used: each product read once, bottom
    // up, into `Tx::powers` by (term, scope), joining its operands' readings: linear in the
    // products plus the factors compared (5.48M to 43.3M, 7.9 times). Cost: one entry per
    // product reached for the life of the transfer; the count is exact (`Count`), so counts
    // that double per level cost O(d²) bits at depth d (row S30b). Nothing refused, no limit on
    // the factors. Test:
    // `l01_25_preimage_catalog::powers::reading_a_product_as_a_power_is_linear_in_its_factors`;
    // COMPLEXITY.md row S30.
    fn read_powers(&mut self, at: At) {
        let mut todo = vec![at];
        while let Some(&at) = todo.last() {
            if self.powers.contains_key(&at) {
                todo.pop();
                continue;
            }
            let (t, env) = at;
            let args = match self.node(t) {
                Node::Prim(Prim::Mul, args) if args.len() == 2 => args,
                _ => {
                    todo.pop();
                    self.power_made(at, Some((t, env, Count::one())));
                    continue;
                }
            };
            let a = self.followed(self.arg(args, 0), env);
            let b = self.followed(self.arg(args, 1), env);
            match (self.powers.get(&a), self.powers.get(&b)) {
                (Some(pa), Some(pb)) => {
                    todo.pop();
                    let p = self.joined(pa, pb);
                    self.power_made(at, p);
                }
                (pa, pb) => {
                    let (wait_a, wait_b) = (pa.is_none(), pb.is_none());
                    if wait_b {
                        todo.push(b);
                    }
                    if wait_a {
                        todo.push(a);
                    }
                }
            }
        }
    }

    /// The product of two powers: one power when their factors are the same term. A free name
    /// is the same input in every scope; any other factor must also be read in the same scope.
    /// Shared operands double the count at each name: `x1 = i * i; x2 = x1 * x1; …` reaches
    /// `2^64` factors at the 64th name, and the count is exact, so it costs `d` bits to add at
    /// depth `d`.
    fn joined(&self, a: &Power, b: &Power) -> Power {
        let ((s, se, j), (u, ue, k)) = (a.as_ref()?, b.as_ref()?);
        let alike = match (self.node(*s), self.node(*u)) {
            (Node::Var(x), Node::Var(y)) if x == y => true,
            _ => se == ue && self.same(*s, *u),
        };
        if !alike {
            return None;
        }
        Some((*s, *se, j.add(k)))
    }

    /// The set of the input domain `dom`, one for the run ([`SharedInts`]).
    fn input_ints(&mut self, dom: Rc<IntervalSet>) -> Ints {
        let shared = &mut self.run.ints.inputs;
        (shared.entry(Rc::as_ptr(&dom)))
            .or_insert_with(|| Ints::shared(dom))
            .clone()
    }

    /// The set of the literal `n`, one for the run ([`SharedInts`]).
    fn literal_ints(&mut self, n: i64) -> Ints {
        (self.run.ints.literals.entry(n))
            .or_insert_with(|| Ints::of(IntervalSet::single(n)))
            .clone()
    }

    /// [`Ints::forward`], once for each operator and operands in the run ([`SharedInts`]).
    fn forward_ints(&mut self, o: &Op, a: &Ints, b: &Ints) -> Ints {
        // Complexity tradeoff: naive version, a power made afresh at each reading, so every set
        // made from it has a new id and misses `ops` too: a run that reads `i * i * j * …`
        // again made the bounds of each product again, `O(n)` bits at depth `n`, `O(n^2)` bits
        // in all. Used: a power once per exponent and operand, keyed by the exponent's value
        // (`Num`'s hash, O(1) to compute) and the operand's id; its set is a function of those
        // alone (`revision::forward` reads one operand for a power). Test:
        // `l01_25_preimage_catalog::powers::reading_a_product_as_a_power_is_linear_in_its_factors`;
        // COMPLEXITY.md row PA-bind-cost.
        if let Op::Pow(k) = o {
            return (self.run.ints.pows.entry((k.num().clone(), a.id())))
                .or_insert_with(|| Ints::forward(o, a, b))
                .clone();
        }
        let key = (std::mem::discriminant(o), a.id(), b.id());
        let shared = &mut self.run.ints.ops;
        shared
            .entry(key)
            .or_insert_with(|| Ints::forward(o, a, b))
            .clone()
    }

    /// [`Walk::fwd`] on a new stack.
    fn fwd(&mut self, t: Tid, env: Eid) -> Fwd {
        let w = Walk::new(self);
        w.stack.run(w.fwd(t, env))
    }

    /// [`Walk::back`] on a new stack.
    fn back(&mut self, t: Tid, env: Eid, d: &Demand) -> Res {
        let w = Walk::new(self);
        w.stack.run(w.back(t, env, d.clone()))
    }

    /// [`Walk::pa`] on a new stack.
    fn pa(&mut self, t: Tid, env: Eid) -> Option<Pa> {
        let w = Walk::new(self);
        w.stack.run(w.pa(t, env))
    }

    /// [`Walk::lin`] on a new stack, adding to the translation `tr`.
    fn lin(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Lin> {
        let w = Walk::translating(self, tr);
        w.stack.run(w.lin(t, env))
    }

    /// The formula of the test `t` read in `env`, translated afresh into `tr`: an auxiliary
    /// variable belongs to the relation of the term that made it, so the translations of
    /// earlier terms are dropped, and those of `tr`'s earlier terms are not reused. Under
    /// [`Tr::definedness`], met with the condition that the test's value is not an atom
    /// ([`Walk::defined`]).
    fn relation(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Formula> {
        let m = &mut self.run.memo;
        m.lin.clear();
        m.formula.clear();
        m.lin_calls.clear();
        m.formula_calls.clear();
        m.projections.clear();
        m.defined.clear();
        m.defined_calls.clear();
        m.log.clear();
        tr.pairs.clear();
        tr.made.clear();
        tr.cases.clear();
        tr.cased.clear();
        let body = self.formula(tr, t, env)?;
        if !tr.definedness {
            return Some(body);
        }
        let d = self.defined(tr, t, env)?;
        Some(match d.is_top() {
            true => body,
            false => Formula::and(vec![d.flat(&tr.sets), body]),
        })
    }

    /// The relation of the function whose lambda is `lam`, its parameters its canonical atoms,
    /// on a new stack ([`Walk::canonical_formula`]).
    fn question(&mut self, tr: &mut Tr, (l, env): At) -> Option<Formula> {
        let Node::Lam(ps, body) = self.node(l) else {
            unreachable!("a lambda")
        };
        let key = (0..ps.len())
            .map(|i| Lin::atom(presburger::Atom::Sym(self.class(ps, i, (body, env)))))
            .collect();
        let w = Walk::translating(self, tr);
        w.stack
            .run(w.canonical_formula(l, ps, (body, env), None, key))
    }

    /// The condition that the value of the function whose lambda is `lam` is not an atom
    /// ([`Walk::defined`]), over the atoms [`Tx::question`] reads, on a new stack
    /// ([`Walk::canonical_defined`]).
    fn question_defined(&mut self, tr: &mut Tr, (l, env): At) -> Option<Defined> {
        let Node::Lam(ps, body) = self.node(l) else {
            unreachable!("a lambda")
        };
        let key = (0..ps.len())
            .map(|i| Lin::atom(presburger::Atom::Sym(self.class(ps, i, (body, env)))))
            .collect();
        let w = Walk::translating(self, tr);
        w.stack
            .run(w.canonical_defined(l, ps, (body, env), None, key))
    }

    /// The condition that the value of `t` in `env` is not an atom ([`Walk::defined`]), on a
    /// new stack.
    fn defined(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Defined> {
        let w = Walk::translating(self, tr);
        w.stack.run(w.defined(t, env))
    }

    /// The canonical atom of the `i`-th parameter of the lambda whose body and scope are
    /// `(body, lam)`: the parameter's name, `#`, and the two numbers, which no written name
    /// holds (`crate::lex::name`).
    fn canonical(&self, ps: Span, i: usize, (body, lam): At) -> Arc<str> {
        format!("{}#{body}.{lam}", self.name(self.param(ps, i))).into()
    }

    /// The atom of the `i`-th parameter of the lambda whose body and scope are `(body, lam)`
    /// that its question and a call passing it the atom as it is read it as: its class's
    /// ([`identity_classes`]), or its canonical atom. A class's atom is never bound, so the
    /// calls of a function from callers that pass it their own parameters as they are share
    /// one translation, with no binding (LOAD-chain-affine).
    fn class(&self, ps: Span, i: usize, (body, lam): At) -> Arc<str> {
        match self.classes.get(&(body, i)) {
            Some(c) => c.clone(),
            None => self.canonical(ps, i, (body, lam)),
        }
    }

    /// [`Walk::formula`] on a new stack, adding to the translation `tr`.
    fn formula(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Formula> {
        let w = Walk::translating(self, tr);
        w.stack.run(w.formula(t, env))
    }

    /// The largest magnitude of the domain of the input `var`, when it is bounded.
    fn magnitude(&self, var: &Arc<str>) -> Option<u128> {
        let (lo, hi) = self.cx.get(var)?.bounds()?;
        Some(input(lo)?.unsigned_abs().max(input(hi)?.unsigned_abs()))
    }

    /// The inputs on which `pa` takes a value in `z`, whose ends may have any size, or `None`
    /// when an end of the input's domain lies outside [`in_range`] and the caller reads the
    /// `if` as before.
    fn invert_pa(&self, pa: &Pa, z: &IntervalSet) -> Option<Res> {
        self.invert_pa_in(pa, z, false)
    }

    /// [`Tx::invert_pa`], with `hull` within the hull of the input's domain and not the domain:
    /// the holes of the domain are not cut out, so the time is that of the summary's pieces
    /// and not of the domain's (the caller meets the result with the domain,
    /// [`Tx::within_inputs`]).
    fn invert_pa_in(&self, pa: &Pa, z: &IntervalSet, hull: bool) -> Option<Res> {
        let (var, dom) = match pa {
            Pa::Const(c) => {
                return Some(if z.contains_end(&Fin(Num::from(c))) {
                    Res::all()
                } else {
                    Res::none()
                });
            }
            Pa::Linear { var, .. } | Pa::Piecewise { var, .. } => (var, self.cx.get(var)?),
        };
        let root = pa.to_treap(dom)?;
        let mut pieces = Vec::new();
        invert_treap(&root, &Tag::ID, z, &mut pieces);
        let met = if hull {
            let within = dom.hull();
            match IntervalSet::from_pieces(pieces).meet(&within) {
                met if met.is_empty() => Met::Empty,
                met if met == within => Met::Whole,
                met => Met::Part(Rc::new(met)),
            }
        } else {
            self.meet_domain(var, Rc::new(IntervalSet::from_pieces(pieces)), dom, false)
        };
        let mut r = Res::all();
        match met {
            Met::Empty => return Some(Res::none()),
            Met::Whole => {}
            Met::Part(s) => {
                r.dom.insert(var.clone(), s);
            }
        }
        Some(r)
    }

    /// Whether the box `r` holds a point of the inputs' domains: each input it narrows meets its
    /// domain, `O(p log P)` for the `p` pieces of the box's set and the `P` of the domain.
    fn reaches_inputs(&self, r: &Res) -> bool {
        !self.empty(r) && (r.dom.iter()).all(|(k, s)| self.cx.get(k).is_none_or(|d| meets(s, d)))
    }

    /// The box `r` met with the inputs' domains, each name it narrows met once, `O(p + P)`.
    fn within_inputs(&self, r: Res) -> Res {
        if self.empty(&r) {
            return r;
        }
        let mut dom = Sets::new();
        for (k, s) in &r.dom {
            let Some(d) = self.cx.get(k) else {
                dom.insert(k.clone(), s.clone());
                continue;
            };
            match self.meet_domain(k, s.clone(), d, true) {
                Met::Empty => return Res::none(),
                Met::Whole => {}
                Met::Part(met) => {
                    dom.insert(k.clone(), met);
                }
            }
        }
        Res { dom, ..r }
    }

    /// `s` met with `d`, the domain of the input `k`, `O(p + P)` for the `p` pieces of `s` and
    /// the `P` of `d`, with `read` counting them ([`read_domain`]). Within [`split_classes`]
    /// each set is met with one domain once: the runs of the classes share the domain
    /// ([`Tx::begin`]), and those that meet one set with it share the result, in `O(p)` for
    /// the search, so that `G` classes reading the same part of a domain with `H` holes cost
    /// `O(G p + H)`, not `O(G H)`.
    fn meet_domain(&self, k: &str, s: Rc<IntervalSet>, d: &IntervalSet, read: bool) -> Met {
        let met = |s: &IntervalSet| {
            if read {
                read_domain(s.len() + d.len());
            }
            match s.meet(d) {
                met if met.is_empty() => Met::Empty,
                met if met == *d => Met::Whole,
                met => Met::Part(Rc::new(met)),
            }
        };
        let mut memo = self.split_meets.borrow_mut();
        let (Some(memo), Some(shared)) = (memo.as_mut(), self.cx.inputs.get(k)) else {
            return met(&s);
        };
        // A domain the context does not hold, as a scope's narrowing gives, is met each time.
        if !std::ptr::eq(&**shared, d) {
            return met(&s);
        }
        let key = (Rc::as_ptr(shared), s);
        if let Some((_, m)) = memo.get(&key) {
            return m.clone();
        }
        let m = met(&key.1);
        memo.insert(key, (shared.clone(), m.clone()));
        m
    }

    /// The inputs on which the sum `sep` takes a value in `z`, as a box. Over one input, that
    /// of [`Tx::invert_pa`]. Over several, each input `v` lies where its term takes a value in
    /// `z` less the bounds of the other terms over their domains ([`Sep::bounds`]): `x >= 0`
    /// with `x = n + k` and `k` in `0..=10` gives `n >= -10`. That box holds every point of
    /// the preimage, and is not exact, since a point of it need not be one. `O(k)` for `k`
    /// inputs, with the inversion of each term.
    fn invert_sep(&self, sep: &Sep, z: &IntervalSet) -> Option<Res> {
        if let Some(pa) = sep.single() {
            return self.invert_pa(&pa, z);
        }
        // Each term's bounds, and their sum with its infinite ends counted, so that the sum of
        // the others is the whole sum less one term's.
        let mut terms = Vec::with_capacity(sep.terms.len());
        let mut sums = Sums {
            lo: sep.constant.clone(),
            hi: sep.constant.clone(),
            lo_inf: 0,
            hi_inf: 0,
        };
        for (v, t) in &sep.terms {
            let pa = sep.term(t);
            let Some((l, h)) = pa_bounds(&pa, self.cx.get(v)?) else {
                return Some(Res::none());
            };
            match &l {
                Val::Fin(x) => sums.lo = &sums.lo + x,
                _ => sums.lo_inf += 1,
            }
            match &h {
                Val::Fin(x) => sums.hi = &sums.hi + x,
                _ => sums.hi_inf += 1,
            }
            terms.push((pa, l, h));
        }
        let mut r = Res::unknown();
        for (pa, l, h) in &terms {
            let own = self.invert_term(pa, (l, h), &sums, z)?;
            if own.none {
                return Some(Res::none());
            }
            r.dom.extend(own.dom);
        }
        Some(r)
    }

    /// The inputs on which the term `pa` of a sum, of bounds `l..=h`, takes a value in `z`
    /// less the bounds of the sum's other terms, the sum's bounds being `sums`
    /// ([`Tx::invert_sep`]).
    fn invert_term(
        &self,
        pa: &Pa,
        (l, h): (&Val, &Val),
        sums: &Sums,
        z: &IntervalSet,
    ) -> Option<Res> {
        // The others' least and greatest sum; `None` for an infinite one.
        let others = |sum: &Int, inf: usize, own: &Val| match own {
            Val::Fin(x) if inf == 0 => Some(sum - x),
            Val::Fin(_) => None,
            _ if inf == 1 => Some(sum.clone()),
            _ => None,
        };
        let (olo, ohi) = (
            others(&sums.lo, sums.lo_inf, l),
            others(&sums.hi, sums.hi_inf, h),
        );
        // `z - [olo, ohi]`, piece by piece.
        let shift = |e: &End, by: &Int| match e {
            Fin(v) => Fin(v - &Num::from(by)),
            _ => e.clone(),
        };
        let pieces = z
            .pieces()
            .map(|(zl, zh)| {
                let lo = ohi.as_ref().map_or(NegInf, |c| shift(zl, c));
                let hi = olo.as_ref().map_or(PosInf, |c| shift(zh, c));
                (lo, hi)
            })
            .collect();
        self.invert_pa(pa, &IntervalSet::from_pieces(pieces))
    }

    /// [`Tx::invert_sep`] of the summary of the name `l`, reading its inputs through the tree
    /// of its terms' bounds ([`Tx::invert_read`]) when it has one.
    fn invert_let(&self, l: &LetIn, z: &IntervalSet) -> Option<Res> {
        let sep = l.summary.formed();
        match &l.read {
            Some(read) if sep.terms.len() > 1 => self.invert_read(&l.summary, &**read, sep, z),
            _ => self.invert_sep(sep, z),
        }
    }

    /// [`Tx::invert_sep`] of `sep`, the sum of `summary`, of two or more terms, whose inputs
    /// `read` holds, giving the same box: the sum of the terms' bounds is the total of the
    /// tree's, and only the terms that may narrow their input or end the inversion are
    /// inverted, in the order [`Tx::invert_sep`] inverts them ([`Sums::wants`]); each other
    /// term's values lie in one piece of what its input may take, so that its inversion keeps
    /// its domain. An input of the run of another domain than `read`'s ([`Run::shadow`]) is
    /// read over its own: its term's bounds there replace those the tree holds in the total,
    /// and it is inverted in its place in the order, beside the visit of the tree, whose sums
    /// over it then take more terms than they need but no fewer. `O((m + c + 1) log k)` for
    /// the `m` terms inverted of `k` and the `c` inputs of the run of another domain, with the
    /// inversion of each, where [`Tx::invert_sep`] costs `O(k)` also when none narrows (item
    /// PA-letpre-linear).
    fn invert_read(
        &self,
        summary: &LetPa,
        read: &dyn SummaryRead,
        sep: &Sep,
        z: &IntervalSet,
    ) -> Option<Res> {
        let own: Vec<(&Arc<str>, &IntervalSet)> = (self.run.shadow.iter())
            .filter(|(k, _)| read.ints(k).is_some())
            .map(|(k, d)| (k, &**d))
            .collect();
        let mut tot = read.total();
        for &(v, d) in &own {
            let was = summary.term_bounds(v, read.ints(v)?);
            let now = summary.term_bounds(v, d);
            tot.lo = &(&tot.lo - &was.lo) + &now.lo;
            tot.hi = &(&tot.hi - &was.hi) + &now.hi;
            tot.lo_inf = tot.lo_inf + now.lo_inf - was.lo_inf;
            tot.hi_inf = tot.hi_inf + now.hi_inf - was.hi_inf;
            tot.no_val = tot.no_val + now.no_val - was.no_val;
        }
        if tot.no_val > 0 {
            return Some(Res::none());
        }
        let sums = Sums {
            lo: &sep.constant + &tot.lo,
            hi: &sep.constant + &tot.hi,
            lo_inf: tot.lo_inf,
            hi_inf: tot.hi_inf,
        };
        let want = sums.wants(z);
        // Inverts the term of `v` over `dom` into `r`, giving how the inversion ends when it
        // does.
        let step = |r: &mut Res, v: &Arc<str>, dom: &IntervalSet| -> Option<Option<Res>> {
            let pa = sep.term(sep.terms.get(v)?);
            let Some((l, h)) = pa_bounds(&pa, dom) else {
                return Some(Some(Res::none()));
            };
            match self.invert_term(&pa, (&l, &h), &sums, z) {
                Some(o) if !o.none => {
                    r.dom.extend(o.dom);
                    None
                }
                o => Some(o.map(|_| Res::none())),
            }
        };
        let mut r = Res::unknown();
        let mut ended: Option<Option<Res>> = None;
        let mut next = 0;
        read.visit(&|b| want.takes(b), &mut |v| {
            if !sep.terms.contains_key(v) {
                return true;
            }
            while let Some(&(o, d)) = own.get(next)
                && **o <= **v
            {
                next += 1;
                ended = step(&mut r, o, d);
                if ended.is_some() {
                    return false;
                }
                if o == v {
                    return true;
                }
            }
            let Some(dom) = read.ints(v) else {
                ended = Some(None);
                return false;
            };
            ended = step(&mut r, v, dom);
            ended.is_none()
        });
        for &(o, d) in &own[next..] {
            if ended.is_some() {
                break;
            }
            ended = step(&mut r, o, d);
        }
        ended.unwrap_or(Some(r))
    }
}

/// The analyses of the transfer that recurse on the depth of the term, each call that may
/// recurse on a frame of [`Stack`], so that the depth is limited by memory alone. A
/// frame holds this by a shared reference, so what it reads of the [`Tx`] it reads through
/// [`Walk::with`], whose borrow ends before any call.
struct Walk<'m, 't> {
    tx: RefCell<&'m mut Tx<'t>>,
    /// The translation into the linear-relation domain, for a walk made by
    /// [`Walk::translating`].
    tr: Option<RefCell<&'m mut Tr>>,
    stack: Stack<'m>,
    /// The inner sums read as part of a larger one without their linear terms kept
    /// ([`Walk::lin_sum`]); one met a second time is translated and kept.
    summed: RefCell<HashSet<(Tid, Eid)>>,
}

impl<'m, 't> Walk<'m, 't> {
    fn new(tx: &'m mut Tx<'t>) -> Self {
        Walk {
            tx: RefCell::new(tx),
            tr: None,
            stack: Stack::default(),
            summed: RefCell::default(),
        }
    }

    /// A walk that translates into the linear-relation domain, adding to `tr`.
    fn translating(tx: &'m mut Tx<'t>, tr: &'m mut Tr) -> Self {
        Walk {
            tx: RefCell::new(tx),
            tr: Some(RefCell::new(tr)),
            stack: Stack::default(),
            summed: RefCell::default(),
        }
    }

    /// `f` on the transfer's state. `f` must not reach `self`, which it could only borrow again.
    fn with<R>(&self, f: impl FnOnce(&mut Tx<'t>) -> R) -> R {
        f(&mut self.tx.borrow_mut())
    }

    /// The integer `k`, built, in a scope's question ([`Tx::asking`]), when the kernel keeps it
    /// as an unbuilt power (`2 ^ 200`), so that a condition written with one is asked like one
    /// written out in digits (I4.5, I5.6): read as no number, it dropped the question with no
    /// message. When the system refuses the memory for it
    /// ([`zed_kernel::num::Rat::to_integer`]) it is `None`, and the relation records that
    /// ([`Scoped::unbuilt`]), so that the question is refused with a message. A preimage
    /// reads it as kept, unbuilt, as before. Complexity tradeoff: O(the bits of `k`), not of
    /// its written size: `2 ^ 100000` costs 100000 bits, and `3 ^ 2^32` 6.8·10^9. A complete
    /// solution would hold a kept power in the solver unbuilt and compare it with the
    /// formula's other constants by bit length first.
    fn built(&self, k: &zed_kernel::num::Rat) -> Option<Int> {
        if !self.with(|tx| tx.asking) {
            return Num::from(k).to_int();
        }
        match k.to_integer() {
            Ok(n) => Some(Int::from(n)),
            Err(_) => {
                self.with(|tx| tx.unbuilt = true);
                None
            }
        }
    }

    fn node(&self, t: Tid) -> Node<'t> {
        self.with(|tx| tx.node(t))
    }

    fn arg(&self, args: Span, i: usize) -> Tid {
        self.with(|tx| tx.arg(args, i))
    }

    fn param(&self, ps: Span, i: usize) -> Name {
        self.with(|tx| tx.param(ps, i))
    }

    fn lookup(&self, env: Eid, x: Name) -> Option<At> {
        self.with(|tx| tx.lookup(env, x))
    }

    fn name(&self, x: Name) -> Arc<str> {
        self.with(|tx| tx.name(x).clone())
    }

    fn let_env(&self, n: Name, e: Tid, env: Eid) -> Eid {
        self.with(|tx| tx.let_env(n, e, env))
    }

    fn call_env(&self, ps: Span, args: Span, lam: Eid, caller: Eid) -> Eid {
        self.with(|tx| tx.call_env(ps, args, lam, caller))
    }

    fn callee(&self, f: Tid, env: Eid) -> Result<Callee, Option<Arc<str>>> {
        self.with(|tx| tx.callee(f, env))
    }

    /// Whether `f` is the formula of a claimed call ([`Walk::formula_called`]): a conjunction
    /// whose last part is `b == n` for a binding `b` numbered n. As an operand of `&&` its parts are added,
    /// so its callee's relation is the kept part of the conjunction and the binding one of the
    /// new parts, which [`presburger::extend`] decides beside it. O(1).
    fn claimed(&self, f: &Formula) -> bool {
        let Formula::And(gs) = f else {
            return false;
        };
        let Some(Formula::Con(c)) = gs.last() else {
            return false;
        };
        let mut terms = c.lin.terms.iter();
        let (Some((presburger::Atom::Aux(n), _)), None) = (terms.next(), terms.next()) else {
            return false;
        };
        self.tr(|tr| matches!(tr.defs[*n as usize].1, What::Bind(_)))
    }

    /// Whether the formula of `t`, an operand of `&&` or `||`, is kept whole
    /// ([`Formula::and_keeping`]): that of a name (COMPLEXITY.md S31b), and that of a call of a
    /// function, so a caller's relation holds its callee's as one shared part and is decided
    /// from the callee's answers (`presburger::extend`, LOAD-chain-share).
    fn whole(&self, t: Tid, env: Eid) -> bool {
        match self.node(t) {
            Node::Var(_) => true,
            Node::App(f, _) => matches!(self.callee(f, env), Ok(Callee::Lam(..))),
            _ => false,
        }
    }

    /// The answer of `f()`, remembered under `k` in `table`: wherever it is reached, or, when a
    /// call it reads stopped at a lambda that was being read before it began, while the stack of
    /// lambdas being read is no lower than it was then ([`Entry`]). Each read of such an entry
    /// passes its stop on. Without the second kind, a term reached at many places under recursion
    /// was read again at each: a chain of k operands named and read at r places took O(r k), and
    /// an `if` d deep whose arms are one shared term took 2^d (ST-formula-k2-rec). A known answer
    /// takes no frame.
    fn cached<K, V, F>(
        &'m self,
        table: Table<K, V>,
        k: K,
        f: impl FnOnce() -> F + 'm,
    ) -> Deep<'m, V>
    where
        K: Key,
        V: Clone + 'static,
        F: Future<Output = V> + 'm,
    {
        #[cfg(test)]
        self.with(|tx| tests::held_read(tx, table, &k));
        let known = self.with(|tx| {
            let entry = table(&mut tx.run.memo).get(&k);
            entry.map(|(v, cut)| (v.clone(), *cut))
        });
        if let Some((v, cut)) = known {
            #[cfg(test)]
            let bypass = cut != usize::MAX && tests::BYPASS.get();
            #[cfg(not(test))]
            let bypass = false;
            if !bypass {
                #[cfg(test)]
                if tests::RECHECK.get() && !tests::BYPASS.get() {
                    return self.stack.call(move || async move {
                        tests::recheck(self, table, &k, &v, cut, f).await;
                        self.with(|tx| tx.cx.cut = tx.cx.cut.min(cut));
                        v
                    });
                }
                self.with(|tx| tx.cx.cut = tx.cx.cut.min(cut));
                return Stack::ready(v);
            }
        }
        self.stack.call(move || self.made(table, k, f))
    }

    /// `f()` read and remembered, for [`Walk::cached`].
    async fn made<K, V, F>(&'m self, table: Table<K, V>, k: K, f: impl FnOnce() -> F) -> V
    where
        K: Key,
        V: Clone + 'static,
        F: Future<Output = V>,
    {
        let (base, outer) = self.with(|tx| {
            let base = tx.run.active.len();
            (base, std::mem::replace(&mut tx.cx.cut, usize::MAX))
        });
        let v = f().await;
        self.with(|tx| {
            let cut = tx.cx.cut;
            #[cfg(test)]
            if cut < base && !none_held() {
                tests::held_made(tx, table, &k, base);
            }
            if let Some(fresh) = &mut tx.fresh
                && fresh.of_body(k.at())
            {
                let k = k.clone();
                fresh.memo.push(Box::new(move |m: &mut Memo| {
                    table(m).remove(&k);
                }));
            }
            let m = &mut tx.run.memo;
            if cut >= base {
                table(m).insert(k, (v.clone(), usize::MAX));
            } else if none_held() {
                // The memo before ST-formula-k2-rec, which the tests compare with.
            } else {
                let unheld = Box::new({
                    let k = k.clone();
                    move |m: &mut Memo| {
                        if table(m).get(&k).is_some_and(|e| e.1 != usize::MAX) {
                            table(m).remove(&k);
                        }
                    }
                });
                table(m).insert(k, (v.clone(), cut));
                m.held.push((base, unheld));
            }
            tx.cx.cut = outer.min(cut);
        });
        v
    }

    /// Whether the term reads an input, or `None` when it reads a term the catalog does not
    /// follow.
    fn mentions(&'m self, t: Tid, env: Eid) -> Deep<'m, Option<bool>> {
        self.cached(
            |m| &mut m.mentions,
            (t, env),
            move || self.mentions_at(t, env),
        )
    }

    async fn mentions_any(&'m self, ts: impl IntoIterator<Item = At>) -> Option<bool> {
        let mut m = false;
        for (t, e) in ts {
            m |= self.mentions(t, e).await?;
        }
        Some(m)
    }

    async fn mentions_at(&'m self, t: Tid, env: Eid) -> Option<bool> {
        match self.node(t) {
            Node::Int(_) | Node::Bool(_) | Node::Lit(_) | Node::PrimFn(_) => Some(false),
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.mentions(bt, be).await,
                None => Some(self.with(|tx| {
                    let x = tx.name(x);
                    tx.cx.has(x) || tx.lets.contains_key(x)
                })),
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.mentions_any([(e, env), (b, inner)]).await
            }
            Node::Lam(ps, b) => {
                // A parameter is not an input, even where it shadows one.
                let inner = self.with(|tx| {
                    let no = (tx.terms.bool(false), ROOT);
                    let mut inner = env;
                    for i in 0..ps.len() {
                        inner = tx.bind(inner, tx.param(ps, i), no);
                    }
                    inner
                });
                self.mentions(b, inner).await
            }
            Node::App(f, args) => {
                let kids = (0..args.len()).map(|i| (self.arg(args, i), env));
                let all: Vec<At> = std::iter::once((f, env)).chain(kids).collect();
                self.mentions_any(all).await
            }
            Node::Prim(_, args) => {
                let all: Vec<At> = (0..args.len()).map(|i| (self.arg(args, i), env)).collect();
                self.mentions_any(all).await
            }
            Node::If(g, a, b) => self.mentions_any([(g, env), (a, env), (b, env)]).await,
            Node::Follow(v, own, _) => self.mentions_any([(v, env), (own, env)]).await,
            Node::Other => None,
        }
    }

    /// Whether the term may read a remainder `u mod c`: `false` only when it reads none,
    /// through its bindings, and calls no lambda. A run restricted to a class of remainders
    /// reads the class only at a remainder ([`Walk::back_arith`], [`Walk::residue_test`]), so the
    /// transfer of a term for which this is `false` is the same in every class.
    fn reads_mod(&'m self, t: Tid, env: Eid) -> Deep<'m, bool> {
        self.cached(
            |m| &mut m.reads_mod,
            (t, env),
            move || self.reads_mod_at(t, env),
        )
    }

    async fn reads_mod_args(&'m self, args: Span, env: Eid) -> bool {
        for i in 0..args.len() {
            if self.reads_mod(self.arg(args, i), env).await {
                return true;
            }
        }
        false
    }

    async fn reads_mod_at(&'m self, t: Tid, env: Eid) -> bool {
        match self.node(t) {
            Node::Int(_) | Node::Bool(_) | Node::Lit(_) => false,
            Node::PrimFn(p) => p == Prim::Mod,
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.reads_mod(bt, be).await,
                None => false,
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.reads_mod(e, env).await || self.reads_mod(b, inner).await
            }
            Node::Prim(p, args) => p == Prim::Mod || self.reads_mod_args(args, env).await,
            Node::App(f, args) => {
                !matches!(self.callee(f, env), Ok(Callee::Prim(p)) if p != Prim::Mod)
                    || self.reads_mod_args(args, env).await
            }
            Node::If(g, a, b) => {
                self.reads_mod(g, env).await
                    || self.reads_mod(a, env).await
                    || self.reads_mod(b, env).await
            }
            Node::Follow(v, own, _) => {
                self.reads_mod(v, env).await || self.reads_mod(own, env).await
            }
            Node::Lam(..) | Node::Other => true,
        }
    }

    /// The term `t` read in `env`, for a term that reads no input, with each name bound in
    /// `env` replaced by the value of the term it is bound to, or by that term closed where it
    /// has none; `None` where it reads a term the catalog does not follow. The names bound
    /// within the term stay, each renamed by its binder ([`Locals`]): a `let` stays a `let`, so
    /// its bound term is run once however often it is read, and no name of a closed term put
    /// under a binder is taken by it.
    // Complexity tradeoff: the naive closing walked the term as a tree and copied the closed
    // term a name is bound to at each read, exponential in depth where parts are shared: `d`
    // nested `if`s over one shared arm, or the chain `x_k = f(x_{k-1}, x_{k-1})`, whose closed
    // term the evaluator then also ran `2^k` times. Used: a part held in a [`Shared`] is closed
    // once for each scope and set of names bound within ([`Memo::close`]) into a shared
    // result, and a name bound in the scope is replaced by its value ([`Walk::constant`],
    // remembered), so the work and the closed term are linear in the distinct triples of
    // part, scope and set. A part held inline has one place, in its parent, and is closed
    // with it, unremembered. Cost: a memo entry for each triple. Tests:
    // `l01_25_preimage_catalog::scaling::long_closing_shared_arms_in_a_called_lambda`,
    // `long_closing_a_chain_of_doubled_calls`; COMPLEXITY.md row S21.
    fn close(&'m self, t: Tid, env: Eid, local: Lid) -> Deep<'m, Option<Term>> {
        self.stack.call(move || self.close_at(t, env, local))
    }

    /// [`Walk::close`] held in a [`Shared`], remembered for a part held in one.
    fn close_shared(&'m self, t: Tid, env: Eid, local: Lid) -> Deep<'m, Option<Shared>> {
        let shut = move || async move { Some(Shared::new(self.close_at(t, env, local).await?)) };
        if self.held(t) {
            self.cached(|m| &mut m.close, ((t, env), local), shut)
        } else {
            self.stack.call(shut)
        }
    }

    /// Whether `t` is a part held in a [`Shared`] of a given term.
    fn held(&self, t: Tid) -> bool {
        self.with(|tx| tx.terms.held.contains_key(&t))
    }

    async fn close_all(&'m self, args: Span, env: Eid, local: Lid) -> Option<Vec<Term>> {
        let mut out = Vec::with_capacity(args.len());
        for i in 0..args.len() {
            out.push(self.close(self.arg(args, i), env, local).await?);
        }
        Some(out)
    }

    async fn close_at(&'m self, t: Tid, env: Eid, local: Lid) -> Option<Term> {
        Some(match self.node(t) {
            Node::Var(x) => match (self.with(|tx| tx.locals.get(local, x)), self.lookup(env, x)) {
                (Some(to), _) => Term::Var(to),
                (None, None) => Term::Var(self.name(x)),
                (None, Some((bt, be))) => match self.constant(bt, be).await {
                    Some(v) => Term::Lit(v),
                    None if self.held(bt) => (*self.close_shared(bt, be, NO_LOCAL).await?).clone(),
                    None => self.close(bt, be, NO_LOCAL).await?,
                },
            },
            Node::Int(n) => Term::Lit(Value::Int(n)),
            Node::Bool(b) => Term::Lit(Value::Bool(b)),
            Node::Lit(v) => Term::Lit(v.clone()),
            Node::PrimFn(p) => Term::PrimFn(p),
            Node::Let(n, e, b) => {
                let e = self.close_shared(e, env, local).await?;
                let (inner, to) = self.with(|tx| tx.bind_local(local, n, t));
                Term::Let(to, e, self.close_shared(b, env, inner).await?)
            }
            Node::Lam(ps, b) => {
                let (mut inner, mut names) = (local, Vec::with_capacity(ps.len()));
                for i in 0..ps.len() {
                    let p = self.param(ps, i);
                    let (l, to) = self.with(|tx| tx.bind_local(inner, p, t));
                    inner = l;
                    names.push(to);
                }
                Term::Lam(names, self.close_shared(b, env, inner).await?)
            }
            Node::App(f, args) => Term::App(
                self.close_shared(f, env, local).await?,
                self.close_all(args, env, local).await?,
            ),
            Node::Prim(p, args) => Term::Prim(p, self.close_all(args, env, local).await?),
            Node::If(g, a, b) => Term::If(
                self.close_shared(g, env, local).await?,
                self.close_shared(a, env, local).await?,
                self.close_shared(b, env, local).await?,
            ),
            Node::Follow(v, own, arms) => {
                let mut arms = arms.to_vec();
                arms.push((Pattern::Wild, self.close(own, env, local).await?));
                Term::Match(self.close_shared(v, env, local).await?, arms)
            }
            Node::Other => return None,
        })
    }

    /// The summary of a call of the lambda with parameters `ps` and body `body` in scope
    /// `lam`, with `args` read in `env`, or `None` when an argument that reads an input may be
    /// other than an integer, or reads a term the catalog does not follow.
    async fn summon(&'m self, ps: Span, body: Tid, lam: Eid, args: Span, env: Eid) -> Option<Call> {
        // Each parameter's binding, or `None` for a parameter over an interval.
        let (mut sig, mut binds, mut doms) = (Vec::new(), Vec::new(), Vec::new());
        for i in 0..ps.len() {
            let (p, a) = (self.param(ps, i), self.arg(args, i));
            if self.mentions(a, env).await? {
                let f = self.fwd(a, env).await;
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
                let dom = self.with(|tx| f.ints.set().snap(tx.marks()));
                sig.push(Arg::Ints(dom.clone()));
                doms.push((i, dom));
                binds.push((p, None));
                continue;
            }
            match self.constant(a, env).await {
                Some(Value::Int(n)) => {
                    binds.push((p, Some((self.with(|tx| tx.terms.int(n)), ROOT))));
                    sig.push(Arg::Int(n));
                }
                Some(Value::Bool(b)) => {
                    binds.push((p, Some((self.with(|tx| tx.terms.bool(b)), ROOT))));
                    sig.push(Arg::Bool(b));
                }
                _ => {
                    let (t, e) = self.with(|tx| tx.followed(a, env));
                    sig.push(Arg::At((t, e)));
                    binds.push((p, Some((t, e))));
                }
            }
        }
        Some(self.with(|tx| {
            let key = ((body, lam), sig);
            let sid = match tx.run.sums.get(&key) {
                Some(&sid) => sid,
                None => {
                    // Numbered past every summary met, those [`Tx::drop_fresh`] dropped too,
                    // whose parameters' names the terms still hold.
                    let sid = tx.run.sids;
                    tx.run.sids += 1;
                    if let Some(fresh) = &mut tx.fresh
                        && (fresh.of_body(key.0)
                            || key
                                .1
                                .iter()
                                .any(|a| matches!(a, Arg::At(at) if fresh.of_body(*at))))
                    {
                        fresh.sums.push(key.clone());
                    }
                    tx.run.sums.insert(key, sid);
                    sid
                }
            };
            let (mut doms, mut params) = (doms.into_iter(), Vec::new());
            let mut bound = Vec::with_capacity(binds.len());
            for (p, to) in binds {
                let to = match to {
                    Some(to) => to,
                    None => {
                        let (i, dom) = doms.next().expect("an interval for each parameter");
                        // A name no source name can be, one for each summary.
                        let name: Arc<str> = format!("\u{1}{i}.{sid}").into();
                        let x = tx.terms.name(&name);
                        params.push((i, name, dom));
                        (tx.terms.var(x), ROOT)
                    }
                };
                bound.push((p, to));
            }
            Call {
                sid,
                binds: bound,
                params,
            }
        }))
    }

    /// The forward value of a summarized call.
    async fn call_fwd(&'m self, call: Call, body: Tid, lam: Eid, place: usize) -> Fwd {
        if let Some(f) = self.with(|tx| tx.run.fwds.get(&call.sid).cloned()) {
            return f;
        }
        let (outer, e) = self.with(|tx| tx.open(&call, lam));
        let f = self.fwd(body, e).await;
        self.with(|tx| {
            let cut = tx.shut(outer);
            if tx.closes(cut, place) {
                tx.run.fwds.insert(call.sid, f.clone());
            }
        });
        f
    }

    /// The value of a term that reads no input, when the evaluator can compute it.
    fn constant(&'m self, t: Tid, env: Eid) -> Deep<'m, Option<Value>> {
        self.cached(
            |m| &mut m.constant,
            (t, env),
            move || self.constant_at(t, env),
        )
    }

    async fn constant_at(&'m self, t: Tid, env: Eid) -> Option<Value> {
        // A literal compared with a value that is no float or rational is its own term.
        if let Node::Follow(v, own, _) = self.node(t)
            && !self.fwd(v, env).await.other
        {
            return self.constant(own, env).await;
        }
        if self.mentions(t, env).await? {
            return None;
        }
        // From the values of the parts where the catalog reads them, so that a part is
        // run once; otherwise the closed term.
        match self.node(t) {
            Node::Int(n) => Some(Value::Int(n)),
            Node::Bool(b) => Some(Value::Bool(b)),
            Node::Lit(v) => Some(v.clone()),
            Node::Var(x) if let Some((bt, be)) = self.lookup(env, x) => self.constant(bt, be).await,
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.constant(b, inner).await
            }
            Node::Prim(p, args) => {
                let mut vs = Vec::with_capacity(args.len());
                for i in 0..args.len() {
                    vs.push(Term::Lit(self.constant(self.arg(args, i), env).await?));
                }
                eval(&Term::Prim(p, vs)).ok()
            }
            Node::If(g, a, b) => match self.constant(g, env).await? {
                Value::Bool(true) => self.constant(a, env).await,
                Value::Bool(false) => self.constant(b, env).await,
                _ => run_closed(&*self.close_all_bound(t, env).await?),
            },
            _ => run_closed(&*self.close_all_bound(t, env).await?),
        }
    }

    /// [`Walk::close`] with no name bound within the term.
    fn close_all_bound(&'m self, t: Tid, env: Eid) -> Deep<'m, Option<Shared>> {
        self.close_shared(t, env, NO_LOCAL)
    }

    async fn constant_int(&'m self, t: Tid, env: Eid) -> Option<i64> {
        match self.constant(t, env).await? {
            Value::Int(n) => Some(n),
            _ => None,
        }
    }

    /// The constant integer `t`, of any size, when it is written out: a coefficient of a summary
    /// ([`Pa`]) is unbounded, so a constant past the 64-bit range is summarized like any other.
    /// A power the kernel keeps unbuilt (`2 ^ 200`) is built ([`Walk::built`]).
    async fn constant_coef(&'m self, t: Tid, env: Eid) -> Option<Int> {
        match self.constant(t, env).await? {
            Value::Int(n) => Some(n.into()),
            Value::Big(k) => self.built(&k),
            _ => None,
        }
    }

    /// The constant exponent `t` of a `^`, when it is an integer at least 0, of any size: a
    /// kernel integer past the 64-bit range is kept as the kernel holds it, unbuilt.
    async fn exponent(&'m self, t: Tid, env: Eid) -> Option<Exponent> {
        match self.constant(t, env).await? {
            Value::Int(n) if n >= 0 => Some(Int::from(n).into()),
            Value::Big(k) if !k.is_negative() => Some(Num::from(&*k).into()),
            _ => None,
        }
    }

    // ---- Forward transfer -------------------------------------------------------------

    fn fwd(&'m self, t: Tid, env: Eid) -> Deep<'m, Fwd> {
        self.cached(|m| &mut m.fwd, (t, env), move || self.fwd_at(t, env))
    }

    async fn fwd_at(&'m self, t: Tid, env: Eid) -> Fwd {
        match self.node(t) {
            Node::Int(n) => Fwd::int(self.with(|tx| tx.literal_ints(n))),
            Node::Lit(Value::Big(n)) => Fwd::int(Ints::of(IntervalSet::point(Num::from(&**n)))),
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
                Some((bt, be)) => self.fwd(bt, be).await,
                None => self.with(|tx| {
                    let x = tx.name(x).clone();
                    if let Some(dom) = tx.cx.inputs.get(&x).cloned() {
                        return Fwd::int(tx.input_ints(dom));
                    }
                    match (tx.cx.get(&x), tx.lets.get(&x)) {
                        (Some(dom), _) => Fwd::int(Ints::of(dom.clone())),
                        (None, Some(l)) => Fwd::int(Ints::of(l.ints.clone())),
                        (None, None) => Fwd::top(),
                    }
                }),
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.fwd(b, inner).await
            }
            Node::Follow(v, own, _) => {
                // At a float or a rational the literal is one, a value of another kind.
                let mut out = self.fwd(own, env).await;
                out.other |= self.fwd(v, env).await.other;
                out
            }
            Node::If(g, a, b) => {
                let g = self.fwd(g, env).await;
                // A guard that is not a test is a failure.
                let mut out = Fwd {
                    fails: !g.is_bool(),
                    ..Fwd::none()
                };
                for (arm, live) in [(a, g.bools.0), (b, g.bools.1)] {
                    if live {
                        let f = self.fwd(arm, env).await;
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
                    let Some(place) = self.with(|tx| tx.enter(t, body)) else {
                        return Fwd::top();
                    };
                    let v = match self.summon(ps, body, lam, args, env).await {
                        Some(call) => self.call_fwd(call, body, lam, place).await,
                        None => {
                            let inner = self.call_env(ps, args, lam, env);
                            self.fwd(body, inner).await
                        }
                    };
                    self.with(|tx| tx.leave(body, place));
                    v
                }
                Ok(Callee::Prim(p)) => {
                    let c = self.with(|tx| tx.terms.call(t, p, args));
                    self.fwd(c, env).await
                }
                _ => Fwd::top(),
            },
            Node::Prim(p, args) => self.fwd_prim(t, p, args, env).await,
            _ => Fwd::top(),
        }
    }

    /// An integer operator over its operands' forward values, failing where either may be
    /// other than an integer, or where `by_zero`.
    fn arith(&'m self, o: &Op, a: &Fwd, b: &Fwd, by_zero: bool) -> Fwd {
        Fwd {
            ints: self.with(|tx| tx.forward_ints(o, &a.ints, &b.ints)),
            fails: !a.is_int() || !b.is_int() || by_zero,
            ..Fwd::none()
        }
    }

    async fn fwd_prim(&'m self, t: Tid, p: Prim, args: Span, env: Eid) -> Fwd {
        use Prim::*;
        if p.arity().is_some_and(|n| n != args.len()) {
            return Fwd::top();
        }
        if p == Mul
            && let Some((base, be, k)) = self.with(|tx| tx.power(t, env))
        {
            let b = self.fwd(base, be).await;
            return self.arith(&Op::Pow(k), &b, &b, false);
        }
        match p {
            Neg | Abs => {
                let a = self.fwd(self.arg(args, 0), env).await;
                self.arith(&op(p, None).expect("scalar"), &a, &a, false)
            }
            Pow => match self.exponent(self.arg(args, 1), env).await {
                Some(k) => {
                    let a = self.fwd(self.arg(args, 0), env).await;
                    self.arith(&Op::Pow(k), &a, &a, false)
                }
                None => Fwd::top(),
            },
            Add | Sub | Mul | IntDiv | Mod | Min | Max => {
                let a = self.fwd(self.arg(args, 0), env).await;
                let b = self.fwd(self.arg(args, 1), env).await;
                let by_zero = matches!(p, IntDiv | Mod) && b.ints.set().contains(0);
                self.arith(&op(p, None).expect("scalar"), &a, &b, by_zero)
            }
            Lt | Le | Gt | Ge | Eq | Ne => {
                let a = self.fwd(self.arg(args, 0), env).await;
                let b = self.fwd(self.arg(args, 1), env).await;
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
                let a = self.fwd(self.arg(args, 0), env).await;
                Fwd {
                    bools: (a.bools.1, a.bools.0),
                    fails: !a.is_bool(),
                    ..Fwd::none()
                }
            }
            And | Or => {
                let a = self.fwd(self.arg(args, 0), env).await;
                let b = self.fwd(self.arg(args, 1), env).await;
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

    // ---- Clipping demands ---------------------------------------------------------------

    /// An interval that holds every integer value of the term, for a term whose backward
    /// result under an integer demand `z` is its result under `z` met with the interval:
    /// an input, a literal, a name bound to such a term, a constant added to or subtracted
    /// from one, a choice between two of them, and their `min` or `max`. `None` for any other
    /// term.
    fn clip(&'m self, t: Tid, env: Eid) -> Deep<'m, Option<IntervalSet>> {
        self.cached(|m| &mut m.clip, (t, env), move || self.clip_at(t, env))
    }

    async fn clip_at(&'m self, t: Tid, env: Eid) -> Option<IntervalSet> {
        if let Node::Var(x) = self.node(t) {
            return match self.lookup(env, x) {
                Some((bt, be)) => self.clip(bt, be).await,
                None => self.with(|tx| {
                    let x = tx.name(x);
                    match tx.cx.get(x) {
                        Some(dom) => Some(dom.hull()),
                        None => tx.lets.get(x).map(|l| l.ints.hull()),
                    }
                }),
            };
        }
        // As in [`Walk::back_in`], a term that reads no input is decided by running it.
        match self.constant(t, env).await {
            Some(Value::Int(n)) => return Some(IntervalSet::single(n)),
            Some(_) => return None,
            None => {}
        }
        match self.node(t) {
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.clip(b, inner).await
            }
            Node::If(_, a, b) => {
                let fa = self.clip(a, env).await?;
                let fb = self.clip(b, env).await?;
                Some(fa.join(&fb).hull())
            }
            Node::Prim(p @ (Prim::Add | Prim::Sub), args) if args.len() == 2 => {
                let (a, b) = (self.arg(args, 0), self.arg(args, 1));
                let (ca, cb) = (
                    self.constant_int(a, env).await,
                    self.constant_int(b, env).await,
                );
                match (p, ca, cb) {
                    (Prim::Add, Some(c), None) => Some(shift(&self.clip(b, env).await?, c as i128)),
                    (Prim::Add, None, Some(c)) => Some(shift(&self.clip(a, env).await?, c as i128)),
                    (Prim::Sub, None, Some(c)) => {
                        Some(shift(&self.clip(a, env).await?, -(c as i128)))
                    }
                    (Prim::Sub, Some(c), None) => {
                        Some(reflect(&self.clip(b, env).await?, c as i128))
                    }
                    _ => None,
                }
            }
            // `min` and `max` are monotone in each operand, so their hull is the operator on
            // the operands' ends.
            Node::Prim(p @ (Prim::Min | Prim::Max), args) if args.len() == 2 => {
                let ca = self.clip(self.arg(args, 0), env).await?;
                let cb = self.clip(self.arg(args, 1), env).await?;
                let ((la, ha), (lb, hb)) = (ca.bounds()?, cb.bounds()?);
                let pick = if p == Prim::Min { End::min } else { End::max };
                Some(IntervalSet::range(
                    pick(la.clone(), lb.clone()),
                    pick(ha.clone(), hb.clone()),
                ))
            }
            _ => None,
        }
    }

    // ---- Backward transfer ------------------------------------------------------------

    fn stop(&self, kind: StopKind, t: Tid) -> Res {
        self.with(|tx| tx.stop(kind, t))
    }

    fn meet(&self, a: Res, b: Res) -> Res {
        self.with(|tx| tx.meet(a, b))
    }

    fn union(&self, a: Res, b: Res) -> Res {
        self.with(|tx| tx.union(a, b))
    }

    fn empty(&self, r: &Res) -> bool {
        self.with(|tx| tx.empty(r))
    }

    /// The box of the inputs at which the term meets the demand `d`. An integer demand is read
    /// as its meet with the term's values, so that demands that differ only outside them are
    /// one.
    async fn back(&'m self, t: Tid, env: Eid, d: Demand) -> Res {
        let d = match d {
            Demand::Ints(z) => match self.clip(t, env).await {
                Some(f) => Demand::Ints(z.meet(&f)),
                None => Demand::Ints(z),
            },
            d => d,
        };
        let call = self.cached(
            |m| &mut m.back,
            ((t, env), d.clone()),
            move || self.back_in(t, env, d),
        );
        call.await
    }

    async fn back_in(&'m self, t: Tid, env: Eid, d: Demand) -> Res {
        if let Demand::Ints(z) = &d
            && z.is_empty()
        {
            return Res::none();
        }
        // A term that reads no input is decided by running it.
        if !matches!(self.node(t), Node::Var(_))
            && let Some(v) = self.constant(t, env).await
        {
            return decided(&d, &v);
        }
        match self.node(t) {
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.back(bt, be, d).await,
                None => self.with(|tx| {
                    let x = tx.name(x);
                    match (tx.cx.get(x), &d) {
                        (Some(dom), Demand::Ints(z)) => {
                            let met = dom.meet(z);
                            if met.is_empty() {
                                return Res::none();
                            }
                            let mut r = Res::all();
                            if met != *dom {
                                r.dom.insert(x.clone(), Rc::new(met));
                            }
                            r
                        }
                        (Some(_), Demand::Bool(_)) => Res::none(),
                        // A name bound by a `let` outside the term: the inputs where its
                        // summary meets the demand.
                        (None, d) if let Some(l) = tx.lets.get(x) => match d {
                            Demand::Ints(z) => tx.invert_let(l, z).unwrap_or_else(Res::unknown),
                            Demand::Bool(_) => Res::none(),
                        },
                        (None, _) => {
                            let kind = StopKind::Foreign(x.clone());
                            tx.stop(kind, t)
                        }
                    }
                }),
            },
            Node::Int(n) => decided(&d, &Value::Int(n)),
            Node::Bool(b) => decided(&d, &Value::Bool(b)),
            Node::Lit(v) => decided(&d, v),
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.back(b, inner, d).await
            }
            Node::If(g, a, b) => {
                if let Demand::Ints(z) = &d
                    && let Some(pa) = self.pa(t, env).await
                    && let Some(r) = self.with(|tx| tx.invert_pa(&pa, z))
                {
                    return r;
                }
                if let Some(index) = self.with(|tx| tx.run.residue.as_ref().map(|r| r.index)) {
                    // A test in a class of remainders: the summary over every class, 1 where
                    // it holds and 0 where it fails.
                    if let Demand::Bool(w) = d
                        && self.fwd(t, env).await.is_bool()
                        && let Some(pa) = self.by_class(t, env).await.and_then(|c| c.get(index))
                        && let Some(r) =
                            self.with(|tx| tx.invert_pa(&pa, &IntervalSet::of(w.into(), w.into())))
                    {
                        return r;
                    }
                    // A guard on the remainder takes one arm throughout the class.
                    if let Some(yes) = self.residue_test(g, env).await {
                        let taken = yes.iter().any(|&(i, j)| i <= index && index <= j);
                        return self.back(if taken { a } else { b }, env, d).await;
                    }
                } else if let Some(r) = self.back_by_class(t, g, env, &d).await {
                    return r;
                }
                let gt = self.back(g, env, Demand::Bool(true)).await;
                let at = self.back(a, env, d.clone()).await;
                let gf = self.back(g, env, Demand::Bool(false)).await;
                let bf = self.back(b, env, d).await;
                let yes = self.meet(gt, at);
                let no = self.meet(gf, bf);
                self.union(yes, no)
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    let Some(place) = self.with(|tx| tx.enter(t, body)) else {
                        return Res::unknown();
                    };
                    let r = match self.summon(ps, body, lam, args, env).await {
                        Some(call) => (self.call_back(call, body, lam, args, env, &d, place)).await,
                        None => {
                            let inner = self.call_env(ps, args, lam, env);
                            self.back(body, inner, d).await
                        }
                    };
                    self.with(|tx| tx.leave(body, place));
                    r
                }
                Ok(Callee::Prim(p)) => {
                    let c = self.with(|tx| tx.terms.call(t, p, args));
                    self.back(c, env, d).await
                }
                Err(Some(name)) => self.stop(StopKind::Foreign(name), t),
                _ => self.stop(StopKind::Outside, t),
            },
            Node::Prim(p, args) => {
                if p.arity().is_some_and(|n| n != args.len()) {
                    return self.stop(StopKind::Outside, t);
                }
                self.back_prim(t, p, args, env, &d).await
            }
            _ => self.stop(StopKind::Outside, t),
        }
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
    #[expect(
        clippy::too_many_arguments,
        reason = "the call, its lambda and the caller's arguments, scope, demand and place are each read"
    )]
    async fn call_back(
        &'m self,
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
                let s = self.with(|tx| z.snap(tx.marks()));
                let same = s == *z;
                (Demand::Ints(s), same)
            }
            _ => (d.clone(), true),
        };
        let k = (call.sid, d);
        let r = match self.with(|tx| tx.run.backs.get(&k).cloned()) {
            Some(r) => r,
            None => {
                let (outer, e) = self.with(|tx| tx.open(&call, lam));
                let r = self.back(body, e, k.1.clone()).await;
                self.with(|tx| {
                    let cut = tx.shut(outer);
                    if tx.closes(cut, place) {
                        tx.run.backs.insert(k, r.clone());
                    }
                });
                r
            }
        };
        if r.none {
            return Res::none();
        }
        let mut out = Res::all();
        out.exact = r.exact && same;
        self.with(|tx| {
            for (k, z) in &r.dom {
                if tx.cx.get(k).is_some_and(|w| *w != **z) {
                    out.dom.insert(k.clone(), z.clone());
                }
            }
        });
        for (i, n, dom) in &call.params {
            if let Some(z) = r.dom.get(n)
                && !dom.is_subset(z)
            {
                let ra = self
                    .back(self.arg(args, *i), env, Demand::Ints((**z).clone()))
                    .await;
                out = self.meet(out, ra);
            }
        }
        out
    }

    async fn back_prim(&'m self, t: Tid, p: Prim, args: Span, env: Eid, d: &Demand) -> Res {
        use Prim::*;
        match p {
            Show | Lower | Upper | Trim | Concat => self.stop(StopKind::String(p), t),
            // `len` moves the demand to the length facet, which is not an input here; the
            // terms below it may still stop.
            Len => {
                self.scan(self.arg(args, 0), env).await;
                Res::unknown()
            }
            Not | And | Or => match *d {
                Demand::Ints(_) => Res::none(),
                Demand::Bool(w) if p == Not => {
                    self.back(self.arg(args, 0), env, Demand::Bool(!w)).await
                }
                Demand::Bool(w) => {
                    let (x, y) = (self.arg(args, 0), self.arg(args, 1));
                    let a = self.back(x, env, Demand::Bool(w)).await;
                    let b = self.back(y, env, Demand::Bool(w)).await;
                    if (p == And) == w {
                        return self.meet(a, b);
                    }
                    // `&&` and `||` here are strict: one side meeting the demand is enough
                    // only when the other cannot fail.
                    let strict =
                        self.fwd(x, env).await.is_bool() && self.fwd(y, env).await.is_bool();
                    let mut r = self.union(a, b);
                    r.exact &= strict;
                    r
                }
            },
            Lt | Le | Gt | Ge | Eq | Ne => match *d {
                Demand::Ints(_) => Res::none(),
                Demand::Bool(w) => {
                    let p = if w { p } else { negate(p) };
                    self.back_compare(t, p, args, env).await
                }
            },
            Add | Sub | Mul | IntDiv | Mod | Neg | Abs | Pow => match d {
                Demand::Ints(z) => self.back_arith(t, p, args, env, z).await,
                Demand::Bool(_) => Res::none(),
            },
            Min | Max => match d {
                Demand::Ints(z) => self.back_arith(t, p, args, env, z).await,
                // `min` and `max` of two tests are tests.
                Demand::Bool(_) => self.stop(StopKind::Outside, t),
            },
            _ => self.stop(StopKind::Outside, t),
        }
    }

    /// The comparison `t` of its operands `args` by `p`, which may be `t`'s own comparison
    /// negated.
    async fn back_compare(&'m self, t: Tid, p: Prim, args: Span, env: Eid) -> Res {
        let (a, b) = (self.arg(args, 0), self.arg(args, 1));
        let (fa, fb) = (self.fwd(a, env).await, self.fwd(b, env).await);
        // Two tests are equal where both are true or both false.
        if matches!(p, Prim::Eq | Prim::Ne) && fa.is_bool() && fb.is_bool() {
            let mut arms = Vec::new();
            for w in [true, false] {
                let ra = self.back(a, env, Demand::Bool(w)).await;
                let rb = self.back(b, env, Demand::Bool(w == (p == Prim::Eq))).await;
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
        if let Some(c) = self.constant_int(b, env).await
            && (ints || ordered_or_eq(&fa))
        {
            return self.back(a, env, Demand::Ints(ray(p, c))).await;
        }
        if let Some(c) = self.constant_int(a, env).await
            && (ints || ordered_or_eq(&fb))
        {
            return self.back(b, env, Demand::Ints(ray(mirror(p), c))).await;
        }
        let one_int = fa.is_int() || fb.is_int();
        if ints || (ordered_or_eq(&fa) && ordered_or_eq(&fb) && (p != Prim::Eq || one_int)) {
            // Between two integers, `a op b` is `a - b op 0`.
            let diff = self.with(|tx| tx.terms.diff(t, args));
            return self.back(diff, env, Demand::Ints(ray(p, 0))).await;
        }
        // Operands of other kinds, or two that may both fail, which `==` finds equal.
        self.scan(a, env).await;
        self.scan(b, env).await;
        Res::unknown()
    }

    /// Reports the stops in a term whose value the transfer does not follow. A term is
    /// scanned once in each scope: its stops are reported the first time.
    fn scan(&'m self, t: Tid, env: Eid) -> Deep<'m, ()> {
        if !self.with(|tx| tx.run.memo.scan.insert((t, env))) {
            return Stack::ready(());
        }
        self.stack.call(move || self.scan_at(t, env))
    }

    async fn scan_at(&'m self, t: Tid, env: Eid) {
        if self.mentions(t, env).await == Some(false) {
            return;
        }
        match self.node(t) {
            Node::Var(x) => {
                if let Some((bt, be)) = self.lookup(env, x) {
                    self.scan(bt, be).await;
                }
            }
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.scan(b, inner).await
            }
            Node::Follow(v, own, _) => {
                for u in [v, own] {
                    self.scan(u, env).await;
                }
            }
            Node::If(g, a, b) => {
                for u in [g, a, b] {
                    self.scan(u, env).await;
                }
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    let Some(place) = self.with(|tx| tx.enter(t, body)) else {
                        return;
                    };
                    match self.summon(ps, body, lam, args, env).await {
                        Some(call) => {
                            if self.with(|tx| tx.run.scanned.insert(call.sid)) {
                                let (outer, e) = self.with(|tx| tx.open(&call, lam));
                                self.scan(body, e).await;
                                self.with(|tx| {
                                    let cut = tx.shut(outer);
                                    tx.closes(cut, place);
                                });
                            }
                        }
                        None => {
                            let inner = self.call_env(ps, args, lam, env);
                            self.scan(body, inner).await
                        }
                    }
                    self.with(|tx| tx.leave(body, place));
                }
                Ok(Callee::Prim(p)) => {
                    let c = self.with(|tx| tx.terms.call(t, p, args));
                    self.scan(c, env).await
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
                    self.scan(self.arg(args, i), env).await;
                }
            }
            _ => {
                self.stop(StopKind::Outside, t);
            }
        }
    }

    async fn back_arith(&'m self, t: Tid, p: Prim, args: Span, env: Eid, z: &IntervalSet) -> Res {
        use Prim::*;
        let ints = Demand::Ints;
        if p == Mul
            && let Some((base, be, k)) = self.with(|tx| tx.power(t, env))
        {
            return self.back_unary(&Op::Pow(k), base, be, z).await;
        }
        let a = self.arg(args, 0);
        match p {
            Neg | Abs => {
                return self
                    .back_unary(&op(p, None).expect("scalar"), a, env, z)
                    .await;
            }
            Pow => {
                let b = self.arg(args, 1);
                return match self.exponent(b, env).await {
                    Some(k) => self.back_unary(&Op::Pow(k), a, env, z).await,
                    // A variable exponent: only the points where both operands are integers.
                    _ => self.both_ints(a, b, env).await,
                };
            }
            _ => {}
        }
        let b = self.arg(args, 1);
        let ca = self.constant_int(a, env).await;
        let cb = self.constant_int(b, env).await;
        match (p, ca, cb) {
            (Add, Some(c), _) => self.back(b, env, ints(shift(z, -(c as i128)))).await,
            (Add, _, Some(c)) | (Sub, _, Some(c)) => {
                let c = if p == Add { -(c as i128) } else { c as i128 };
                self.back(a, env, ints(shift(z, c))).await
            }
            (Sub, Some(c), _) => self.back(b, env, ints(reflect(z, c as i128))).await,
            (Mul, Some(c), _) => self.back(b, env, ints(times_pre(z, c))).await,
            (Mul, _, Some(c)) => self.back(a, env, ints(times_pre(z, c))).await,
            (IntDiv, _, Some(c)) => self.back(a, env, ints(div_pre(z, c))).await,
            (Mod, _, Some(c)) => {
                // Within the run's class of remainders of the input `a`, every point is in `z`
                // or none is.
                let m = c.unsigned_abs() as i128;
                let class = self.with(|tx| match tx.node(a) {
                    Node::Var(x) if tx.lookup(env, x).is_none() => tx
                        .run
                        .residue
                        .as_mut()
                        .filter(|r| r.x == x && r.m == m)
                        .map(|r| {
                            r.alone = true;
                            (r.class.is_subset(z), r.class.meet(z).is_empty())
                        }),
                    _ => None,
                });
                match class {
                    Some((true, _)) => return self.back(a, env, ints(IntervalSet::top())).await,
                    Some((_, true)) => return Res::none(),
                    _ => {}
                }
                let fa = self.fwd(a, env).await.ints;
                let (s, exact) = mod_pre(z, c, fa.set());
                let mut r = self.back(a, env, ints(s)).await;
                r.exact &= exact;
                r
            }
            (Min | Max, Some(c), _) => self.back(b, env, ints(minmax_pre(p, z, c))).await,
            (Min | Max, _, Some(c)) => self.back(a, env, ints(minmax_pre(p, z, c))).await,
            (Min | Max, None, None) => {
                let f = self.fwd(t, env).await.ints;
                let zf = z.meet(f.set());
                let (Some((flo, fhi)), Some((lo, hi))) = (f.bounds(), zf.bounds()) else {
                    return Res::none();
                };
                let up = IntervalSet::range(lo.clone(), fhi.clone()).is_subset(z);
                let down = IntervalSet::range(flo.clone(), hi.clone()).is_subset(z);
                // min ≥ lo: both are; max ≤ hi: both are. The other rays: either is, where the
                // other operand is an integer, since a failing operand fails the term (DESIGN.md
                // sec:failure; SOUND-exact-oracle: `max(x, 0 mod y) >= 8` with `x` in `[8, 12]`
                // fails at `y == 0`). When the demand holds the whole forward range, both rays
                // apply; the upward one is taken.
                let both = (p == Min && up) || (p == Max && down && !up);
                let either = (p == Min && down && !up) || (p == Max && up);
                if both || either {
                    let r = if up {
                        IntervalSet::range(lo.clone(), PosInf)
                    } else {
                        IntervalSet::range(NegInf, hi.clone())
                    };
                    let ra = self.back(a, env, ints(r.clone())).await;
                    let rb = self.back(b, env, ints(r)).await;
                    if both {
                        return self.meet(ra, rb);
                    }
                    let ra = if self.fwd(b, env).await.fails {
                        self.meet(ra, self.back(b, env, ints(IntervalSet::top())).await)
                    } else {
                        ra
                    };
                    let rb = if self.fwd(a, env).await.fails {
                        self.meet(rb, self.back(a, env, ints(IntervalSet::top())).await)
                    } else {
                        rb
                    };
                    return self.union(ra, rb);
                }
                self.project(p, a, b, env, z).await
            }
            // A sum or difference of two summaries of one input is a summary ([`Pa::plus`]),
            // whose preimage is exact; the projection reads each operand against the other's
            // interval, so `n + (if n > 0 { n } else { 0 })` there would read `n` as every
            // integer.
            (Add | Sub, None, None) => {
                if let Some(pa) = self.pa(t, env).await
                    && let Some(r) = self.with(|tx| tx.invert_pa(&pa, z))
                {
                    return r;
                }
                self.project(p, a, b, env, z).await
            }
            _ => self.project(p, a, b, env, z).await,
        }
    }

    /// `op(c)` in `z`, for an operator the revision table inverts exactly within the forward
    /// interval of `c`.
    async fn back_unary(&'m self, o: &Op, c: Tid, env: Eid, z: &IntervalSet) -> Res {
        if let Op::Pow(k) = o
            && k.is_zero()
        {
            // `c ^ 0` is 1 wherever `c` is an integer.
            return if z.contains(1) {
                self.back(c, env, Demand::Ints(IntervalSet::top())).await
            } else {
                Res::none()
            };
        }
        let fc = self.fwd(c, env).await.ints;
        let zc = revision::backward(o, 0, fc.set(), fc.set(), z);
        self.back(c, env, Demand::Ints(zc)).await
    }

    /// The HC4 projection onto each operand: necessary, not exact.
    ///
    /// Complexity tradeoff: each operand is narrowed alone against the other's forward
    /// interval, so the relation between the operands is given up and the box can hold
    /// points that fail the demand. Why: the exact preimage of a nonlinear operator is a
    /// region that is not a box, and finding it costs the points of the box (or is
    /// undecidable for polynomial tests over unbounded integers). Trigger: an operator with
    /// no exact catalog entry (anything but shifts, scalings, `div` and `mod` by a constant,
    /// `^`, and branches), or two operands that both read inputs. Test:
    /// `l01_25_preimage_catalog::entries::a_strict_disjunction_with_a_failing_side_is_necessary_only`.
    /// COMPLEXITY.md row C16. A complete solution is `@exact` ([`exact_preimage`]), which
    /// searches the box at a cost in its points.
    /// Naive version: the exact preimage, a search of the box at a cost in its points; used: one
    /// interval narrowing per operand, in the pieces of the two interval sets (inferred).
    async fn project(&'m self, p: Prim, a: Tid, b: Tid, env: Eid, z: &IntervalSet) -> Res {
        let o = op(p, None).expect("binary scalar operator");
        let fa = self.fwd(a, env).await.ints;
        let fb = self.fwd(b, env).await.ints;
        let za = revision::backward(&o, 0, fa.set(), fb.set(), z);
        let zb = revision::backward(&o, 1, fa.set(), fb.set(), z);
        let ra = self.back(a, env, Demand::Ints(za)).await;
        let rb = self.back(b, env, Demand::Ints(zb)).await;
        let mut r = self.meet(ra, rb);
        r.exact = self.empty(&r);
        r
    }

    async fn both_ints(&'m self, a: Tid, b: Tid, env: Eid) -> Res {
        let ra = self.back(a, env, Demand::Ints(IntervalSet::top())).await;
        let rb = self.back(b, env, Demand::Ints(IntervalSet::top())).await;
        let mut r = self.meet(ra, rb);
        r.exact = self.empty(&r);
        r
    }

    // ---- Piecewise-affine summaries -----------------------------------------------------

    /// The value of the term as a piecewise-affine function of one input ([`Pa`]), or `None`
    /// when it is not one or when it reads more than one input. Its coefficients, constants
    /// and values are unbounded ([`Int`]), and an infinite end of a piece is the limit of
    /// its line there, so `t + 1` over all integers is a summary. Keyed on the term alone, so
    /// an `if` chain whose arms read one shared term is summarized once, whatever demands
    /// reach it.
    async fn pa(&'m self, t: Tid, env: Eid) -> Option<Pa> {
        if self.with(|tx| tx.run.void) {
            return None;
        }
        // In a class of remainders, an `if` the summary over every class reads is looked up
        // there, so that the classes share one reading of the term.
        if matches!(self.node(t), Node::If(..))
            && !self.fwd(t, env).await.has_bools()
            && let Some(index) = self.with(|tx| tx.run.residue.as_ref().map(|r| r.index))
            && let Some(p) = self.by_class(t, env).await.and_then(|b| b.get(index))
        {
            return Some(p);
        }
        let call = self.cached(|m| &mut m.pa, (t, env), move || self.pa_at(t, env));
        call.await
    }

    async fn pa_at(&'m self, t: Tid, env: Eid) -> Option<Pa> {
        if !matches!(self.node(t), Node::Var(_))
            && let Some(v) = self.constant(t, env).await
        {
            return match v {
                Value::Int(c) => Some(Pa::Const(c.into())),
                Value::Big(k) => self.built(&k).map(Pa::Const),
                _ => None,
            };
        }
        match self.node(t) {
            Node::Int(c) => Some(Pa::Const(c.into())),
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.pa(bt, be).await,
                None => self.with(|tx| {
                    let name = tx.name(x);
                    if tx.cx.has(name) {
                        return Some(Pa::Linear {
                            var: name.clone(),
                            a: Int::ONE,
                            b: Int::ZERO,
                        });
                    }
                    // A name bound by a `let` outside the term, summarized once
                    // ([`LetPa::force`]).
                    tx.lets.get(name)?.summary.force()
                }),
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.pa(b, inner).await
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Prim(p)) => {
                    let c = self.with(|tx| tx.terms.call(t, p, args));
                    self.pa(c, env).await
                }
                _ => None,
            },
            Node::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => {
                self.pa_prim(t, p, args, env).await
            }
            Node::If(g, a, b) => self.pa_if(g, a, b, env).await,
            _ => None,
        }
    }

    /// An `if` whose guard narrows at most the one input its arms read: the arms' treaps
    /// sliced to the inputs that take each arm, joined in order. Exact, since both guard
    /// results must be.
    async fn pa_if(&'m self, g: Tid, a: Tid, b: Tid, env: Eid) -> Option<Pa> {
        let gt = self.back(g, env, Demand::Bool(true)).await;
        let gf = self.back(g, env, Demand::Bool(false)).await;
        if !gt.exact || !gf.exact {
            return None;
        }
        let pa = self.pa(a, env).await?;
        let pb = self.pa(b, env).await?;
        self.pa_select(g, env, &pa, &pb).await
    }

    /// The summary that is `pa` on the inputs where the test `g` holds and `pb` where it
    /// fails ([`Walk::pa_if`]).
    async fn pa_select(&'m self, g: Tid, env: Eid, pa: &Pa, pb: &Pa) -> Option<Pa> {
        let gt = self.back(g, env, Demand::Bool(true)).await;
        let gf = self.back(g, env, Demand::Bool(false)).await;
        if !gt.exact || !gf.exact {
            return None;
        }
        self.with(|tx| {
            let (yes, no) = (!tx.empty(&gt), !tx.empty(&gf));
            if gt.dom.len() > 1 || gf.dom.len() > 1 {
                return None;
            }
            let mut var: Option<&Arc<str>> = None;
            for name in gt
                .dom
                .keys()
                .chain(gf.dom.keys())
                .chain(pa.var())
                .chain(pb.var())
            {
                match var {
                    Some(v) if v != name => return None,
                    _ => var = Some(name),
                }
            }
            let Some(var) = var else {
                // Neither the guard nor the arms read an input: one arm is taken everywhere.
                return match (yes, no) {
                    (true, false) => Some(pa.clone()),
                    (false, true) => Some(pb.clone()),
                    _ => None,
                };
            };
            let dom = tx.cx.get(var)?;
            let (st, sf) = (gt.dom.get(var), gf.dom.get(var));
            let (st, sf) = (st.map_or(dom, |s| &**s), sf.map_or(dom, |s| &**s));
            select(var, dom, [yes.then_some((st, pa)), no.then_some((sf, pb))])
        })
    }

    /// `min(pa, c)`, or `max(pa, c)` where not `min`, over the domain of `pa`'s input
    /// ([`Pa::clamp`]).
    fn clamped(&'m self, pa: &Pa, min: bool, c: i64) -> Option<Pa> {
        match pa.var() {
            None => pa.clamp(min, c, &IntervalSet::empty()),
            Some(v) => self.with(|tx| pa.clamp(min, c, tx.cx.get(v)?)),
        }
    }

    /// `-u`, `u + c`, `c + u`, `u - c`, `c - u` and `c * u` for a summarized `u` and a
    /// constant `c`, `u + v` and `u - v` for two summaries of one input ([`Pa::plus`]),
    /// `min` and `max` of a summary and a constant or of two summaries of one input, and
    /// `abs(u)`; the arity was checked by the caller. `div` and `mod` by a constant get no
    /// summary: `u div c` is a step function, with one affine piece per `c` values of `u`, so
    /// its summary would grow with the width of the domain.
    async fn pa_prim(&'m self, t: Tid, p: Prim, args: Span, env: Eid) -> Option<Pa> {
        let a = self.arg(args, 0);
        match p {
            Prim::Neg => Some(self.pa(a, env).await?.affine(-1, 0)),
            Prim::Add => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_coef(a, env).await {
                    return Some(self.pa(b, env).await?.affine(1, c));
                }
                if let Some(c) = self.constant_coef(b, env).await {
                    return Some(self.pa(a, env).await?.affine(1, c));
                }
                let pa = self.pa(a, env).await?;
                pa.plus(&self.pa(b, env).await?, 1)
            }
            Prim::Sub => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_coef(b, env).await {
                    return Some(self.pa(a, env).await?.affine(1, -&c));
                }
                if let Some(c) = self.constant_coef(a, env).await {
                    return Some(self.pa(b, env).await?.affine(-1, c));
                }
                let pa = self.pa(a, env).await?;
                pa.plus(&self.pa(b, env).await?, -1)
            }
            Prim::Mul => {
                if self.with(|tx| tx.power(t, env)).is_some() {
                    return None;
                }
                let b = self.arg(args, 1);
                let (c, u) = match self.constant_coef(a, env).await {
                    Some(c) => (c, b),
                    None => (self.constant_coef(b, env).await?, a),
                };
                let pa = self.pa(u, env).await?;
                if c.is_zero() {
                    // `u` is summarized, so it has a value at every input, and the product is 0.
                    return Some(Pa::Const(Int::ZERO));
                }
                Some(pa.affine(c, 0))
            }
            Prim::Min | Prim::Max => {
                let b = self.arg(args, 1);
                let min = p == Prim::Min;
                let (c, u) = match self.constant_int(a, env).await {
                    Some(c) => (c, b),
                    None => match self.constant_int(b, env).await {
                        Some(c) => (c, a),
                        None => {
                            let pa = self.pa(a, env).await?;
                            let pb = self.pa(b, env).await?;
                            // Two lines of one input: `u` where `v - u` has the sign that
                            // makes it the one chosen, else `v`, with exact bounds.
                            if let (
                                Pa::Linear { var, a: ua, b: ub },
                                Pa::Linear {
                                    var: w,
                                    a: va,
                                    b: vb,
                                },
                            ) = (&pa, &pb)
                                && var == w
                            {
                                let d = (va - ua, vb - ub);
                                let (u, v) = ((ua.clone(), ub.clone()), (va.clone(), vb.clone()));
                                let (neg, pos) = if min { (v, u) } else { (u, v) };
                                return self.with(|tx| {
                                    Pa::by_sign(var, (&d.0, &d.1), tx.cx.get(var)?, neg, pos)
                                });
                            }
                            // Two summaries of one input: `min(u, v) = u + min(v - u, 0)`.
                            let d = pb.plus(&pa, -1)?;
                            return self.clamped(&d, min, 0)?.plus(&pa, 1);
                        }
                    },
                };
                let pa = self.pa(u, env).await?;
                self.clamped(&pa, min, c)
            }
            Prim::Abs => {
                // `abs(u) = max(u, -u) = u + max(-2 * u, 0)`: a choice on `u >= 0`. Of a line,
                // `-u` where `u` is negative and `u` elsewhere, with exact bounds ([`Pa::by_sign`]).
                let pa = self.pa(a, env).await?;
                match &pa {
                    Pa::Const(c) => return Some(Pa::Const(c.abs())),
                    Pa::Linear { var, a, b } => {
                        let (neg, pos) = ((-a, -b), (a.clone(), b.clone()));
                        return self.with(|tx| Pa::by_sign(var, (a, b), tx.cx.get(var)?, neg, pos));
                    }
                    Pa::Piecewise { .. } => {}
                }
                self.clamped(&pa.affine(-2, 0), false, 0)?.plus(&pa, 1)
            }
            _ => None,
        }
    }

    /// The summary ([`Walk::pa`]) of the term in every class of remainders of the run's split
    /// ([`split_residues`]), built once for all classes, with a test's `false` and `true` read
    /// as 0 and 1: `None` outside a split, and for a term other than those read here.
    ///
    /// - An `if` whose guard compares the split's remainder with a constant: in each class such
    ///   a guard is true throughout or false throughout, so the `if` is the arm it takes, and
    ///   the summaries of the classes are those of the `no` arm with the classes where the
    ///   guard holds taken from the `yes` arm, `O(log G)` for `G` classes. Such a comparison
    ///   as a value is read the same way, as an `if` with arms 1 and 0.
    /// - A term that reads no remainder ([`Walk::reads_mod`]): its transfer is the same in
    ///   every class, so its summary is read once, [`Walk::pa_at`], or for a test the one that
    ///   is 1 and 0 on the sets the transfer finds exactly where it holds and where it fails.
    /// - An `if` on a test that reads no remainder: when both arms are one summary in every
    ///   class, the summary of the `if` is too, sliced once ([`Walk::pa_select`]); when the
    ///   arms add constants to one tree whose summaries are a base plus a constant in each
    ///   class (`t` and `t + 1` for one `t`, [`ByClass`]), the tree is kept and its base is
    ///   sliced once, `O(log n)`, since adding a constant commutes with slicing by the guard's
    ///   sets.
    ///   Otherwise the two trees are laid over each other and each stretch of classes in which
    ///   both arms are one summary is sliced by itself ([`cls_zip`]), `O(L log n)` for `L`
    ///   such stretches, at most `G`.
    /// - `-u`, `u + c`, `u - c`, `c - u` and `c * u`: every summary is mapped, `O(1)`, and
    ///   `0 * u` is 0; `not u` is `1 - u`; `min` and `max` of `u` and a constant `c` are `u` or
    ///   `c` in every class when the forward values of `u`, the same in every class, lie on one
    ///   side of `c`, and otherwise each class's summary is clamped at `c` ([`ByClass::clamp`]),
    ///   `O((m + 1) log n)` for the `m` pieces that cross `c`.
    ///
    /// Complexity tradeoff: a term this does not read is read in each class by its own run,
    /// `O(G n log n)` for `G` classes, as before this summary (row S22e). Given up: an `if` on
    /// a test that reads no remainder whose arms read different inputs; a test of a term that
    /// reads a remainder (its set in each class is the inverse of that class's own summary);
    /// and a term whose values or coefficients may pass `i64::MAX` in magnitude (the summary
    /// checks them on the bounds of every class at once, where the transfer checks each
    /// class). Trigger: such a term between the root and the remainder guards, for example
    /// `if i >= 3 { t } else { j }` with `t` reading `i`, `t >= 0` below an `if` on the
    /// remainder, or a domain unbounded on either side. Test:
    /// `l01_25_preimage_catalog::s22::remainder_chains_outside_the_shared_summary_keep_their_preimages`,
    /// COMPLEXITY.md rows S22e-quad, S22e-wide and S22-order-chain. A complete solution would
    /// hold the congruence facet in the backward transfer's sets (`x mod m` in a set of
    /// classes beside the interval), so that one transfer carries every class at once.
    fn by_class(&'m self, t: Tid, env: Eid) -> Deep<'m, Option<ByClass>> {
        let (t, on) = self.with(|tx| (tx.terms.form(t), tx.classes().map(|c| (c.x, c.m))));
        self.cached(
            |m| &mut m.by_class,
            ((t, env), on),
            move || self.by_class_at(t, env),
        )
    }

    async fn by_class_at(&'m self, t: Tid, env: Eid) -> Option<ByClass> {
        let n = self.with(|tx| tx.classes().map(|c| c.cuts.len() - 1))?;
        // As in [`Walk::pa_at`].
        if !matches!(self.node(t), Node::Var(_))
            && let Some(v) = self.constant(t, env).await
        {
            return match v {
                Value::Int(c) => ByClass::constant(c, n),
                Value::Bool(b) => ByClass::constant(b.into(), n),
                _ => None,
            };
        }
        let read = self.by_class_node(t, env, n).await;
        if read.is_some() || matches!(self.node(t), Node::Var(_)) || self.reads_mod(t, env).await {
            return read;
        }
        // The transfer of the term is the same in every class.
        let pa = if self.fwd(t, env).await.is_bool() {
            // The transfer of a test `if` in a class asks for this summary first
            // ([`Walk::back_in`]), which is being made: reading it here would call itself
            // without end (S22-order, `x mod 3 != 0 && (if x <= 2 { false } else { x < x })`).
            // Without it the transfer reads the guard and the arms in each class, exactly.
            if matches!(self.node(t), Node::If(..)) {
                return None;
            }
            self.pa_select(t, env, &Pa::Const(Int::ONE), &Pa::Const(Int::ZERO))
                .await?
        } else {
            self.pa_at(t, env).await?
        };
        let var = pa.var().cloned();
        let x = match &var {
            Some(v) => self.with(|tx| tx.magnitude(v))?,
            None => 0,
        };
        let bound = Bound::of(&pa, x);
        ByClass::based(pa, var, bound, n)
    }

    /// [`Walk::by_class`] of the term by its kind.
    async fn by_class_node(&'m self, t: Tid, env: Eid, n: usize) -> Option<ByClass> {
        match self.node(t) {
            Node::Int(c) => ByClass::constant(c, n),
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.by_class(bt, be).await,
                None => {
                    let name = self.name(x);
                    let bound = Bound {
                        a: 1,
                        b: 0,
                        x: self.with(|tx| tx.magnitude(&name))?,
                        mul: 1,
                    };
                    let pa = Pa::Linear {
                        var: name.clone(),
                        a: Int::ONE,
                        b: Int::ZERO,
                    };
                    ByClass::based(pa, Some(name), bound, n)
                }
            },
            Node::Let(m, e, b) => {
                let inner = self.let_env(m, e, env);
                self.by_class(b, inner).await
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Prim(p)) => {
                    let c = self.with(|tx| tx.terms.call(t, p, args));
                    self.by_class(c, env).await
                }
                _ => None,
            },
            Node::Prim(p, args) if p.arity().is_none_or(|k| k == args.len()) => {
                self.by_class_prim(t, p, args, env, n).await
            }
            Node::If(g, a, b) => match self.residue_test(g, env).await {
                Some(yes) => {
                    // Each arm is read only in its own classes ([`Walk::by_class_on`]).
                    let no = ranges_complement(&yes, n);
                    let ca = self.by_class_on(a, env, &yes, n).await?;
                    let cb = self.by_class_on(b, env, &no, n).await?;
                    ByClass::choose(&ca, &cb, &yes)
                }
                None => self.by_class_if(g, a, b, env, None).await,
            },
            _ => None,
        }
    }

    /// [`Walk::by_class`] of `t`, an arm of an `if` on the split's remainder that
    /// [`ByClass::choose`] reads only in the classes of `ranges` (ranges `i..=j` of class
    /// numbers, sorted and disjoint, out of `n`): the summaries in those classes, and a
    /// placeholder that nothing reads in the others. Only an `if` on a test that reads no
    /// remainder and `min` or `max` with a constant are read this way, each from the full
    /// summaries of its operands; any other term, or a refusal, is [`Walk::by_class`].
    ///
    /// Complexity tradeoff: naive version, the arm's summaries in every class, which for these
    /// two kinds clamps or slices each of the `L` leaves of the operand's tree, `O(L)` work, and
    /// then [`ByClass::choose`] keeps the classes of `ranges` alone. In a chain of `k` levels
    /// `x mod m != r(j)`, else `if x <= c { max(t, c(j)) } else { t }`, each level keeps one
    /// class but read all `O(k)` leaves: `O(k^2)` clamps and slices (S22, rows S22e-quad and
    /// S22-order-chain; `remainder_cases_sliced_by_a_test_scale` went from 0.13G to 1.38G
    /// instructions, 10.7 times, from k = 8 to 64). Used: the operation applied only in the
    /// nodes of the tree that meet `ranges` ([`cls_clamp`], [`cls_zip`]), the others replaced by
    /// one placeholder leaf each: `O((r + L_r) log n)` for `r` ranges and the `L_r` leaves that
    /// meet them, as a range query of a segment tree (Bentley, "Solutions to Klee's rectangle
    /// problems", 1977) visits the nodes on the paths to the range's ends. Cost: the result is
    /// not cached, as the full summary is ([`Walk::by_class`]), so an arm read in full
    /// elsewhere too is read twice; and a bound ([`Bound`]) is checked only over the classes
    /// read, which can accept a term the full summary refused for a class that no case reads.
    async fn by_class_on(
        &'m self,
        t: Tid,
        env: Eid,
        ranges: &[(usize, usize)],
        n: usize,
    ) -> Option<ByClass> {
        // Read in full where no case reads the arm, as before, or every case does.
        let read = ranges.iter().map(|&(i, j)| j + 1 - i).sum::<usize>();
        if ranges.is_empty() || read == n {
            return self.by_class(t, env).await;
        }
        let read = match self.node(t) {
            Node::If(g, a, b) if self.residue_test(g, env).await.is_none() => {
                self.by_class_if(g, a, b, env, Some(ranges)).await
            }
            Node::Prim(p @ (Prim::Min | Prim::Max), args) if args.len() == 2 => {
                self.by_class_clamp(p, args, env, n, Some(ranges)).await
            }
            _ => None,
        };
        match read {
            Some(c) => Some(c),
            None => self.by_class(t, env).await,
        }
    }

    /// An arm of [`Walk::by_class_if`] read only in the classes of `on`, when it is `min` or
    /// `max` with a constant ([`Walk::by_class_on`]), and otherwise in every class.
    async fn by_class_arm(
        &'m self,
        t: Tid,
        env: Eid,
        on: Option<&[(usize, usize)]>,
    ) -> Option<ByClass> {
        if let Some(ranges) = on
            && let Node::Prim(p @ (Prim::Min | Prim::Max), args) = self.node(t)
            && args.len() == 2
            && let Some(n) = self.with(|tx| tx.classes().map(|c| c.cuts.len() - 1))
            && let Some(c) = self.by_class_clamp(p, args, env, n, Some(ranges)).await
        {
            return Some(c);
        }
        self.by_class(t, env).await
    }

    /// [`Walk::by_class`] of an `if` whose guard `g` is not on the split's remainder; with `on`,
    /// only in the classes of those ranges ([`Walk::by_class_on`]).
    async fn by_class_if(
        &'m self,
        g: Tid,
        a: Tid,
        b: Tid,
        env: Eid,
        on: Option<&[(usize, usize)]>,
    ) -> Option<ByClass> {
        if self.reads_mod(g, env).await {
            return None;
        }
        let ca = self.by_class_arm(a, env, on).await?;
        let cb = self.by_class_arm(b, env, on).await?;
        let bound = ca.bound.max(cb.bound);
        if ca.adds
            && cb.adds
            && Rc::ptr_eq(&ca.root, &cb.root)
            && let (Some(u), Some(v)) = (&ca.base, &cb.base)
            && same_pa(u, v)
        {
            // In class `i` the arms are `u + d_i + ca.shift` and `u + d_i + cb.shift`.
            let pa = u.affine(1, ca.shift);
            let pb = u.affine(1, cb.shift);
            let base = self.pa_select(g, env, &pa, &pb).await?;
            let var = base.var().cloned().or(ca.var.clone());
            return bound.holds().then(|| ByClass {
                root: ca.root.clone(),
                n: ca.n,
                var,
                bound,
                base: Some(base),
                shift: 0,
                adds: true,
            });
        }
        if let (Some(pa), Some(pb)) = (ca.uniform(), cb.uniform()) {
            let pa = self.pa_select(g, env, &pa, &pb).await?;
            let var = pa.var().cloned().or(ca.var.clone());
            return ByClass::based(pa, var, bound, ca.n);
        }
        // Complexity tradeoff: the arms differ by more than a constant in some class, so each
        // stretch of classes in which both arms are one summary is sliced by itself, `O(L log
        // n)` for the `L` leaves of the two trees laid over each other, at most the `G`
        // classes, where the cases above slice once. Why: the slices of different summaries
        // share no step. Trigger: an `if` on a test that reads no remainder whose arms read
        // the remainder in different ways, for example `if y == 0 { u + 2 } else { u }` with
        // `u = if y mod 2 != 0 { y } else { 6 - y }`. Test:
        // `store::preimage::tests::a_chain_with_clamps_is_read_in_time_near_its_length`.
        // COMPLEXITY.md rows S22e-quad and S22-order-chain. A complete solution is the one
        // named at [`Walk::by_class`].
        let var = match (&ca.var, &cb.var) {
            (Some(u), Some(v)) if u != v => return None,
            (Some(v), _) | (_, Some(v)) => Some(v.clone()),
            (None, None) => None,
        };
        let mut pairs = Vec::new();
        cls_zip(
            &ca.shifted()?,
            &cb.shifted()?,
            (ca.base.as_ref(), cb.base.as_ref()),
            (0, ca.n),
            on,
            &mut pairs,
        )?;
        let mut leaves = Vec::with_capacity(pairs.len());
        for (span, pair) in pairs {
            match pair {
                Some((pa, pb)) => leaves.push((span, self.pa_select(g, env, &pa, &pb).await?)),
                None => leaves.push((span, Pa::Const(Int::ZERO))),
            }
        }
        let bound = leaves
            .iter()
            .fold(bound, |b, (_, pa)| b.max(Bound::of(pa, b.x)));
        let mut leaves = leaves.into_iter().peekable();
        let root = cls_build(&mut leaves, (0, ca.n));
        bound.holds().then_some(ByClass {
            root,
            n: ca.n,
            var,
            bound,
            base: None,
            shift: 0,
            adds: false,
        })
    }

    /// [`Walk::pa_prim`] over every class.
    async fn by_class_prim(
        &'m self,
        t: Tid,
        p: Prim,
        args: Span,
        env: Eid,
        n: usize,
    ) -> Option<ByClass> {
        let a = self.arg(args, 0);
        match p {
            Prim::Neg => self.by_class(a, env).await?.affine((-1, 0)),
            Prim::Not => self.by_class(a, env).await?.affine((-1, 1)),
            Prim::Add => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_int(a, env).await {
                    return self.by_class(b, env).await?.affine((1, c.into()));
                }
                let c = self.constant_int(b, env).await?;
                self.by_class(a, env).await?.affine((1, c.into()))
            }
            Prim::Sub => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_int(b, env).await {
                    return self.by_class(a, env).await?.affine((1, -i128::from(c)));
                }
                let c = self.constant_int(a, env).await?;
                self.by_class(b, env).await?.affine((-1, c.into()))
            }
            Prim::Mul => {
                if self.with(|tx| tx.power(t, env)).is_some() {
                    return None;
                }
                let b = self.arg(args, 1);
                let (c, u) = match self.constant_int(a, env).await {
                    Some(c) => (c, b),
                    None => (self.constant_int(b, env).await?, a),
                };
                let cu = self.by_class(u, env).await?;
                if c == 0 {
                    return ByClass::constant(0, n);
                }
                cu.affine((c.into(), 0))
            }
            Prim::Min | Prim::Max => self.by_class_clamp(p, args, env, n, None).await,
            Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge | Prim::Eq | Prim::Ne => {
                let yes = self.residue_test(t, env).await?;
                ByClass::choose(&ByClass::constant(1, n)?, &ByClass::constant(0, n)?, &yes)
            }
            _ => None,
        }
    }

    /// [`Walk::by_class_prim`] of `min` or `max` (`p`) of a term and a constant, the arguments
    /// `args`; with `on`, only in the classes of those ranges ([`Walk::by_class_on`]).
    async fn by_class_clamp(
        &'m self,
        p: Prim,
        args: Span,
        env: Eid,
        n: usize,
        on: Option<&[(usize, usize)]>,
    ) -> Option<ByClass> {
        let (a, b) = (self.arg(args, 0), self.arg(args, 1));
        let (c, u) = match self.constant_int(a, env).await {
            Some(c) => (c, b),
            None => (self.constant_int(b, env).await?, a),
        };
        // The forward values are read over the box, the same in every class.
        let f = self.fwd(u, env).await;
        let (Fin(lo), Fin(hi)) = f.ints.bounds()? else {
            return None;
        };
        let c_num = Num::from(c);
        let (below, above) = (*hi <= c_num, *lo >= c_num);
        match (p, below, above) {
            (Prim::Min, true, _) | (Prim::Max, _, true) => self.by_class(u, env).await,
            (Prim::Min, _, true) | (Prim::Max, true, _) => ByClass::constant(c, n),
            _ => {
                let cu = self.by_class(u, env).await?;
                let min = p == Prim::Min;
                match &cu.var {
                    None => cu.clamp(min, c, &IntervalSet::empty(), on),
                    Some(v) => self.with(|tx| cu.clamp(min, c, tx.cx.get(v)?, on)),
                }
            }
        }
    }

    /// The transfer, in a run that is not split, of the `if` `t` whose guard `g` compares a
    /// remainder `x mod m` of an input with a constant: read from the summaries of `t` over the
    /// classes the terms cut `x mod m` into ([`Walk::by_class`]), so that each level of a chain
    /// of such guards is read once whatever demands reach it. For each range of classes that
    /// holds one summary, the inputs on which it meets the demand, within the members of `x`
    /// in those classes; the union of these. `None` when the run is split, `g` is not such a
    /// guard, or the summary is not found, and the arms are read as before.
    ///
    /// Before, the guard was read by [`mod_pre`], inexact over more than two periods, so the
    /// summary of the `if` ([`Walk::pa`]) was refused and each arm sent its own demand to a
    /// term the arms share: a chain of `k` such levels met up to `O(k^2)` demands at a level
    /// (row S22-order-chain). Now the cost is that of the summaries, `O(k log k)` for a chain of
    /// `k` levels, and `O(L)` inversions for a tree of `L` leaves, at most the `G` classes.
    ///
    /// Complexity tradeoff: the members of `x` in a range of classes over more than two
    /// periods are their hull's first and last periods and one piece between ([`mod_pre`], row
    /// C17), so the box is inexact there, and the linear stage gives the answer as before. Why:
    /// a piece for each period has no bound in the size of the term. Trigger: a guard on `x mod
    /// m` over a domain of `x` wider than two periods of `m`, where the `if` is read in a run
    /// that is not split (arms that read different inputs, a test of a term that reads a
    /// remainder, remainders of two inputs or two moduli). Test:
    /// `l01_25_preimage_catalog::s22::remainder_reads_outside_a_split_scale`. COMPLEXITY.md row
    /// S22-transfer-rem. A complete solution would hold the congruence facet in the transfer's
    /// sets, as named at [`Walk::by_class`].
    async fn back_by_class(&'m self, t: Tid, g: Tid, env: Eid, d: &Demand) -> Option<Res> {
        if self.with(|tx| tx.run.residue.is_some()) {
            return None;
        }
        let (x, m, _, _) = self.remainder_test(g, env).await?;
        let fwd = self.fwd(t, env).await;
        let z = match d {
            Demand::Ints(z) if !fwd.has_bools() => z.clone(),
            Demand::Bool(w) if fwd.is_bool() => IntervalSet::of((*w).into(), (*w).into()),
            _ => return None,
        };
        let classes = self.with(|tx| tx.classes_of(x, m))?;
        let outer = self.with(|tx| tx.run.classes.replace(classes.clone()));
        let by = self.by_class(t, env).await;
        self.with(|tx| tx.run.classes = outer);
        let leaves = by?.leaves()?;
        let c = i64::try_from(m).ok()?;
        let (name, dom) = self.with(|tx| {
            let name = tx.name(x).clone();
            let dom = tx.cx.rc(&name);
            (name, dom)
        });
        let dom = dom?;
        // Each leaf is read within the hull of the domain of `x` and the boxes are met with the
        // domain once at the end ([`Tx::within_inputs`]), so that a leaf costs the pieces of its
        // own box and a binary search of the domain per piece, where meeting each leaf with the
        // domain cost `O(L * P)` for `L` leaves and `P` pieces, `O(k^2)` when both grow with the
        // chain (COMPLEXITY.md S22-hole-summaries); the union is taken as a balanced tree
        // ([`Walk::union_all`]), where joined one by one each step would cost the pieces
        // gathered so far.
        let hull = dom.hull();
        let mut found = Vec::with_capacity(leaves.len());
        for ((i, j), pa) in leaves {
            let r = self.with(|tx| tx.invert_pa_in(&pa, &z, true))?;
            read_domain(1);
            let rems =
                IntervalSet::range(End::from(classes.cuts[i]), End::from(classes.cuts[j] - 1));
            let (members, exact) = mod_pre(&rems, c, &hull);
            if members.is_empty() {
                continue;
            }
            let mut within = Res::all();
            within.exact = exact;
            if members != hull {
                within.dom.insert(name.clone(), Rc::new(members));
            }
            let met = self.meet(r, within);
            // A box whose members of an input all lie in holes of its domain holds no point.
            if self.with(|tx| tx.reaches_inputs(&met)) {
                found.push(met);
            }
        }
        let out = self.union_all(found);
        Some(self.with(|tx| tx.within_inputs(out)))
    }

    /// The union of `rs` ([`Tx::union`]), joined in pairs, then pairs of pairs: each round
    /// costs the pieces of all the boxes, so `O(N log n)` for `n` boxes of `N` pieces in all.
    fn union_all(&self, mut rs: Vec<Res>) -> Res {
        while rs.len() > 1 {
            let mut next = Vec::with_capacity(rs.len().div_ceil(2));
            let mut it = rs.into_iter();
            while let Some(a) = it.next() {
                next.push(match it.next() {
                    Some(b) => self.union(a, b),
                    None => a,
                });
            }
            rs = next;
        }
        rs.pop().unwrap_or_else(Res::none)
    }

    /// The classes of the run's split in which the test `g` is true, as ranges of class
    /// numbers, when `g` compares the split's remainder `x mod c` with a constant in the way
    /// [`Walk::back_compare`] reads as a demand on the remainder, so that in each class the
    /// transfer finds the test true throughout or false throughout ([`Walk::back_arith`]).
    async fn residue_test(&'m self, g: Tid, env: Eid) -> Option<Vec<(usize, usize)>> {
        let (x, m, z, _) = self.remainder_test(g, env).await?;
        self.with(|tx| {
            let res = tx.classes()?;
            if res.x != x || res.m != m {
                return None;
            }
            let within = IntervalSet::range(End::of(0), End::from(res.m - 1));
            let mut yes = Vec::new();
            for (lo, hi) in z.meet(&within).pieces() {
                let (Fin(lo), Fin(hi)) = (lo, hi) else {
                    return None;
                };
                let (Some(lo), Some(hi)) = (lo.to_i128(), hi.to_i128()) else {
                    return None;
                };
                let i = res.cuts.partition_point(|&e| e <= lo) - 1;
                let j = res.cuts.partition_point(|&e| e <= hi) - 1;
                // The cuts hold the ends of every such test's set ([`Tx::remainder_cuts`]).
                if res.cuts[i] != lo || res.cuts[j + 1] != hi + 1 {
                    return None;
                }
                yes.push((i, j));
            }
            Some(yes)
        })
    }

    /// The input `x`, the modulus `m`, the set of remainders `z` and the term `x mod c` of a test
    /// `g` that compares `x mod c` (`m = |c|`) with a constant in the way
    /// [`Walk::back_compare`] reads as a demand on the remainder: `g` holds where `x mod c` lies
    /// in `z`.
    async fn remainder_test(&'m self, g: Tid, env: Eid) -> Option<(Name, i128, IntervalSet, Tid)> {
        let Node::Prim(p @ (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge | Prim::Eq | Prim::Ne), args) =
            self.node(g)
        else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let (a, b) = (self.arg(args, 0), self.arg(args, 1));
        if !self.fwd(a, env).await.is_int() || !self.fwd(b, env).await.is_int() {
            return None;
        }
        let (r, z) = match self.constant_int(b, env).await {
            Some(v) => (a, ray(p, v)),
            None => (b, ray(mirror(p), self.constant_int(a, env).await?)),
        };
        let Node::Prim(Prim::Mod, margs) = self.node(r) else {
            return None;
        };
        if margs.len() != 2 {
            return None;
        }
        let Node::Var(x) = self.node(self.arg(margs, 0)) else {
            return None;
        };
        if self.lookup(env, x).is_some() {
            return None;
        }
        let c = self.constant_int(self.arg(margs, 1), env).await?;
        Some((x, c.unsigned_abs() as i128, z, r))
    }

    // ---- Into the linear-relation domain ------------------------------------------------

    /// `f` on the translation, for a walk made by [`Walk::translating`].
    fn tr<R>(&self, f: impl FnOnce(&mut Tr) -> R) -> R {
        let tr = self
            .tr
            .as_ref()
            .expect("a translation runs on a walk made with one");
        f(&mut tr.borrow_mut())
    }

    /// [`Walk::cached`] for the translation into the linear-relation domain, whose entries a
    /// translation that is undone removes; `logged` names an entry for the log.
    fn translated<K, V, F>(
        &'m self,
        table: Table<K, V>,
        k: K,
        logged: fn(K) -> Logged,
        f: impl FnOnce() -> F + 'm,
    ) -> Deep<'m, V>
    where
        K: Key,
        V: Clone + Unpin + 'static,
        F: Future<Output = V> + 'm,
    {
        if self.with(|tx| table(&mut tx.run.memo).contains_key(&k)) {
            return self.cached(table, k, f);
        }
        self.stack.call(move || async move {
            let v = self.cached(table, k.clone(), f).await;
            self.with(|tx| {
                if table(&mut tx.run.memo).contains_key(&k) {
                    tx.run.memo.log.push(logged(k));
                }
            });
            v
        })
    }

    /// The key a call of the lambda `body` in scope `lam` is translated under: `None`, with
    /// what the attempt made undone, when an argument has no linear term.
    async fn call_key(&'m self, body: Tid, lam: Eid, args: Span, env: Eid) -> Option<CallKey> {
        let mark = self.tr(|tr| tr.defs.len());
        let logged = self.with(|tx| tx.run.memo.log.len());
        let mut lins = Vec::with_capacity(args.len());
        for i in 0..args.len() {
            match self.lin(self.arg(args, i), env).await {
                Some(l) => lins.push(l),
                None => {
                    self.tr(|tr| tr.truncate(mark));
                    self.with(|tx| tx.forget(logged));
                    return None;
                }
            }
        }
        Some(((body, lam), lins, Vec::new()))
    }

    /// The linear term an integer term states over the inputs.
    fn lin(&'m self, t: Tid, env: Eid) -> Deep<'m, Option<Lin>> {
        self.translated(
            |m| &mut m.lin,
            (t, env),
            Logged::Lin,
            move || self.lin_at(t, env),
        )
    }

    /// The linear term of the body of a call at `t`, with its lambda on the stack of lambdas
    /// being read; `None` when the lambda is already there.
    async fn lin_call(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Span,
        env: Eid,
    ) -> Option<Lin> {
        let place = self.with(|tx| tx.enter(t, body))?;
        let inner = self.call_env(ps, args, lam, env);
        let l = self.lin(body, inner).await;
        self.with(|tx| tx.leave(body, place));
        l
    }

    /// The linear term, in the linear stage ([`Tr::by_class`]) of a run that is not split, of
    /// the `if` `t` whose guard `g` tests the remainder `x mod m` of an input by a constant:
    /// one auxiliary variable `v` defined by the summaries of `t` over the classes the terms
    /// cut `x mod m` into ([`Walk::by_class`], as [`Walk::back_by_class`] reads them), one
    /// case for each piece ([`pa_pieces`]) of each range of classes that holds one summary,
    /// cut where a piece of a range next to it starts ([`neighbor_cuts`]): `r` in those
    /// classes, the summary's input in the piece, and `v == a * u + b`, for the remainder `r`
    /// of the pair `x mod m` names. Every copy of `t` in the same scope is the same `v`
    /// ([`Tr::cases`]). `None` where no summary is found, and the `if` is translated level by
    /// level.
    ///
    /// Level by level, a chain of `k` such guards is `k` auxiliary variables, each defined by a
    /// disjunction of its two arms, which the solver reads together: 2.1 s at k = 30 and 4.3 s
    /// at k = 60 for `c <= 2 && y mod 2 == 0` with the counted chain `c`, and 22 s for the
    /// chain of seed 2 at k = 13 (COMPLEXITY.md row S22-linear-rem). Now it is one variable
    /// whose definition has a disjunct for each piece of the summaries and each cut, at most
    /// `C + 2S` for `C` pieces with `S` starts between them, and the summary costs
    /// `O(k log k)`.
    // Complexity tradeoff: naive version and used version as above (k nested disjunctions read
    // together, 24.6 s at k = 120; one variable by cases, 104 ms at k = 480). Tradeoffs: only a
    // guard on the remainder of one input by a constant; elsewhere the `if` is translated
    // level by level, as before; the cases are kept per scope (`Tr::cases`) until
    // `Tr::truncate`. Test
    // `l01_25_preimage_catalog::s22::remainder_chains_in_the_linear_stage_scale`; COMPLEXITY.md
    // row S22-linear-rem.
    async fn lin_by_class(&'m self, t: Tid, g: Tid, env: Eid) -> Option<Lin> {
        if !self.tr(|tr| tr.by_class) || self.with(|tx| tx.run.residue.is_some()) {
            return None;
        }
        // Complexity tradeoff: the solver takes each case to its hull in the input, and the
        // hull of a range's members over a piece holds the points of the other classes
        // between them, so where another range's summary changes inside the piece, a hole that
        // the level-by-level form cut out there is lost unless the case is cut at that start.
        // Each case is cut at the starts of the two ranges next to it (`x mod m` of `x - 1`
        // and `x + 1`), not of every range: with three ranges or fewer, as for every modulus
        // 3, those are all the other ranges, the same cases as cutting at every start (in the
        // five shape tests every box of `x` lay within the level-by-level box, 17 of 60
        // strictly); with more, a hole only a farther range's start cuts out is lost, and
        // the box keeps those points (sound, inexact): at moduli 5 and 7, 2 of 120 shape boxes
        // are 1 point wider than level by level and 1 differs both ways, and the boxes hold
        // 0.2% and 0.6% more points than cut at every range. Since no summary is cut at a hole
        // of the domain ([`Pa::to_treap`]), a case no longer splits at one either: 7 of 180
        // shape boxes at moduli 3, 5, 7 grew by 2 to 4 points, 10, 8 and 0 points in all
        // against 1648, 1469 and 1315 points above the exact projection, and one box at
        // modulus 3 is 2 points wider than level by level (COMPLEXITY.md S22-hole-summaries).
        // Meeting the box with the union of
        // the pieces does not help: a range whose summary is one line has one piece over the
        // whole domain. Why: cutting at every other range's starts makes `L * S` cases for `L`
        // ranges and `S` starts, `O(k^2)` for the chain of `k` guards of
        // `spread_remainder_chain`; cutting at the neighbors makes at most `C + 2S`, `O(k)`
        // there. Tests:
        // `l01_25_preimage_catalog::s22::remainder_cases_cut_at_their_neighbors_*`.
        // COMPLEXITY.md rows S22-linear-rem and S22-case-cuts. A complete solution keeps the
        // congruence in the solver's projection of each case instead of its hull.
        let key = (self.with(|tx| tx.terms.form(t)), env);
        if let Some(n) = self.tr(|tr| tr.cases.get(&key).copied()) {
            return Some(Lin::atom(presburger::Atom::Aux(n)));
        }
        let (x, m, _, r) = self.remainder_test(g, env).await?;
        let classes = self.with(|tx| tx.classes_of(x, m))?;
        let outer = self.with(|tx| tx.run.classes.replace(classes.clone()));
        let by = self.by_class(t, env).await;
        self.with(|tx| tx.run.classes = outer);
        let by = by?;
        let cut_on = by.var.clone().map(|v| Lin::atom(presburger::Atom::Sym(v)));
        let leaves = by.leaves()?;
        let rem = self.lin(r, env).await?;
        // Each range of classes: what holds `r` in it, its summary's input and its pieces.
        let mut ranges = Vec::with_capacity(leaves.len());
        for ((i, j), pa) in leaves {
            let (lo, hi) = (classes.cuts[i], classes.cuts[j] - 1);
            let mut within = Vec::new();
            if lo > 0 {
                within.push(Formula::Con(Con::ge(&rem, &Lin::constant(lo))));
            }
            if hi < m - 1 {
                within.push(Formula::Con(Con::ge(&Lin::constant(hi), &rem)));
            }
            let u = pa
                .var()
                .map(|v| Lin::atom(presburger::Atom::Sym(v.clone())));
            ranges.push((within, u, pa_pieces(&pa)));
        }
        let starts: Vec<Vec<i128>> = (ranges.iter())
            .map(|(_, _, pieces)| piece_starts(pieces))
            .collect();
        let near = neighbor_cuts(&starts);
        let mut cases = Vec::new();
        for ((within, u, pieces), near) in ranges.iter().zip(&near) {
            // A constant summary holds on every input, so it is cut on the tree's input too.
            let cut = cut_on.is_some() && (u.is_none() || *u == cut_on);
            let on = if cut { &cut_on } else { u };
            for (piece, a, b) in pieces {
                let value = match u {
                    Some(u) => u.times(a.clone()).plus(&Lin::constant(b.clone())),
                    None => Lin::constant(b.clone()),
                };
                let (lo, hi) = match piece {
                    Some((lo, hi)) => (end_of(lo), end_of(hi)),
                    None => (None, None),
                };
                // The neighbors' starts inside `lo + 1..=hi`.
                let inside = match cut {
                    true => {
                        let from = near.partition_point(|&c| lo.is_some_and(|lo| c <= lo));
                        let to = near.partition_point(|&c| hi.is_none_or(|hi| c <= hi));
                        &near[from..to]
                    }
                    false => &[][..],
                };
                let mut first = lo;
                for last in (inside.iter().map(|&c| Some(c - 1))).chain([hi]) {
                    let mut g = within.clone();
                    if let Some(on) = on {
                        if let Some(first) = first {
                            g.push(Formula::Con(Con::ge(on, &Lin::constant(first))));
                        }
                        if let Some(last) = last {
                            g.push(Formula::Con(Con::ge(&Lin::constant(last), on)));
                        }
                    }
                    cases.push((Formula::and(g), value.clone()));
                    first = last.map(|l| l + 1);
                }
            }
        }
        self.tr(|tr| {
            let n = tr.defs.len() as u32;
            let v = Lin::atom(presburger::Atom::Aux(n));
            let def = Formula::or(
                (cases.iter())
                    .map(|(g, l)| Formula::and(vec![g.clone(), Formula::Con(Con::eq(&v, l))]))
                    .collect(),
            );
            tr.aux(What::Cases(cases), def);
            tr.cases.insert(key, n);
            tr.cased.push(key);
            Some(v)
        })
    }

    /// The linear term of the sum or difference `t`: its left operands that are sums or
    /// differences in turn are read in place down to the first that is not, or whose term is
    /// known, or that was read in place before in this walk, which is translated
    /// ([`Walk::lin`]); then each right operand is translated and added, the innermost first.
    /// The terms are read, and so translated, in the order the operands nest, as one call of
    /// `lin` for each would read them.
    // Complexity tradeoff: naive version, `lin` on each operand and `Lin::plus`, so each inner
    // sum's linear term was copied and kept: `z0 + … + z(k-1)`, read as
    // `((z0 + z1) + …) + z(k-1)`, kept a term of i names at the i-th `+`, Θ(k²) time and
    // memory (54 s at k = 16384 for the assume, against 2.1 s for the same sum written as a
    // balanced tree). Used: the left operands read in place and added into one term, O(k log
    // k) for such a chain. A left operand met in place a second time in one walk is translated
    // and kept, so an operand shared by many sums is read in place once and then known, and
    // the walk reads each term in place at most once, as before. Tradeoffs: an inner sum read
    // in place has no kept term, so a later walk that meets it alone translates it again,
    // which costs what the whole chain cost here; a chain nested on the right,
    // `z0 + (z1 + …)`, is not read in place and still keeps a term at each `+`, Θ(k²).
    // Test: `l01_39_reduced_product::scaling::a_sum_over_many_names_is_assumed_in_time_near_linear`,
    // COMPLEXITY.md row F154.
    async fn lin_sum(&'m self, t: Tid, env: Eid) -> Option<Lin> {
        use Prim::*;
        // The right operands, outermost first, each with whether it is subtracted.
        let mut rights: Vec<(bool, Tid)> = Vec::new();
        let mut at = t;
        let base = loop {
            let Node::Prim(p @ (Add | Sub), args) = self.node(at) else {
                unreachable!("a sum or difference")
            };
            rights.push((p == Sub, self.arg(args, 1)));
            let left = self.arg(args, 0);
            let inner = matches!(self.node(left), Node::Prim(Add | Sub, a) if a.len() == 2);
            if !inner
                || self.with(|tx| tx.run.memo.lin.contains_key(&(left, env)))
                || !self.summed.borrow_mut().insert((left, env))
                || self.constant(left, env).await.is_some()
            {
                break left;
            }
            at = left;
        };
        let mut sum = self.lin(base, env).await?;
        for (minus, r) in rights.into_iter().rev() {
            let l = self.lin(r, env).await?;
            if minus {
                sum.plus_assign(&l.times(-1));
            } else {
                sum.plus_assign(&l);
            }
        }
        Some(sum)
    }

    async fn lin_at(&'m self, t: Tid, env: Eid) -> Option<Lin> {
        use Prim::*;
        if let Some(v) = self.constant(t, env).await {
            // A constant past the 64-bit range is read at its size, as `constant_coef` reads
            // it (I4.1): read as no linear form, it dropped the question with no message.
            return match v {
                Value::Int(n) => Some(Lin::constant(n)),
                Value::Big(k) => self.built(&k).map(Lin::constant),
                _ => None,
            };
        }
        match self.node(t) {
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.lin(bt, be).await,
                None => self.with(|tx| {
                    let x = tx.name(x);
                    (tx.cx.has(x)).then(|| Lin::atom(presburger::Atom::Sym(x.clone())))
                }),
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.lin(b, inner).await
            }
            Node::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    match self.shared_call_key(body, lam, args, env).await {
                        Some(k) => {
                            let call = self.translated(
                                |m| &mut m.lin_calls,
                                k.clone(),
                                Logged::LinCall,
                                move || self.lin_called(t, ps, (body, lam), args, env, k),
                            );
                            call.await
                        }
                        None => self.lin_call(t, ps, (body, lam), args, env).await,
                    }
                }
                Callee::Prim(p) => {
                    let c = self.with(|tx| tx.terms.call(t, p, args));
                    self.lin(c, env).await
                }
                Callee::Lam(..) => None,
            },
            Node::If(g, a, b) => {
                if let Some(l) = self.lin_by_class(t, g, env).await {
                    return Some(l);
                }
                let g = self.formula(g, env).await?;
                let (la, lb) = (self.lin(a, env).await?, self.lin(b, env).await?);
                // One level: the parts are shown by their linear forms, in which an auxiliary
                // variable is its name, so the name costs the size of what it is made of.
                let what = What::If(g.clone(), la.clone(), lb.clone());
                self.tr(|tr| {
                    let x = Lin::atom(presburger::Atom::Aux(tr.defs.len() as u32));
                    let def = Formula::or(vec![
                        Formula::and(vec![g.clone(), Formula::Con(Con::eq(&x, &la))]),
                        Formula::and(vec![Formula::negate(g), Formula::Con(Con::eq(&x, &lb))]),
                    ]);
                    tr.aux(what, def);
                    Some(x)
                })
            }
            Node::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => {
                let arg = |i: usize| self.lin(self.arg(args, i), env);
                let products = self.tr(|tr| tr.products);
                match p {
                    Add | Sub if args.len() == 2 => self.lin_sum(t, env).await,
                    Neg => Some(arg(0).await?.times(-1)),
                    Mul => {
                        let (a, b) = (arg(0).await?, arg(1).await?);
                        if !products && !a.terms.is_empty() && !b.terms.is_empty() {
                            return None;
                        }
                        a.product(&b)
                    }
                    Pow => match self.constant_int(self.arg(args, 1), env).await? {
                        // `c^0` is 1 where `c` is defined and `c`'s failure where it is not
                        // (DESIGN.md sec:failure: a loose atom operand passes out). Where the
                        // relation does not track failure ([`Tr::definedness`]), a term
                        // translates only where it cannot fail, so the base must translate
                        // too: `(-4 div (1 + x))^0` fails at `x == -1`.
                        0 => {
                            if !self.tr(|tr| tr.definedness) {
                                arg(0).await?;
                            }
                            Some(Lin::constant(1))
                        }
                        1 => arg(0).await,
                        2 if products => {
                            let a = arg(0).await?;
                            a.product(&a)
                        }
                        _ => None,
                    },
                    IntDiv | Mod => {
                        // A divisor past the 64-bit range is read at its size (R4-CLAUDE-1): read
                        // as no constant, it dropped the question with no message.
                        let k = self.constant_coef(self.arg(args, 1), env).await;
                        if k.is_none() && products {
                            // A divisor that is not a constant: its product with the quotient
                            // is an atom, which only rung 2's translation admits.
                            let a = arg(0).await?;
                            let n = arg(1).await?;
                            return self.tr(|tr| tr.div_mod_by_term(p, &a, &n));
                        }
                        let c = k.filter(|c| !c.is_zero())?;
                        let a = arg(0).await?;
                        self.tr(|tr| {
                            let n = tr.pair_by_constant(&a, &c);
                            let n = if p == IntDiv { n } else { n + 1 };
                            Some(Lin::atom(presburger::Atom::Aux(n)))
                        })
                    }
                    Min | Max | Abs => {
                        let a = arg(0).await?;
                        let b = if p == Abs { a.times(-1) } else { arg(1).await? };
                        self.tr(|tr| {
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
                                Abs => What::Abs(a.clone()),
                                Min => What::Min(a.clone(), b.clone()),
                                _ => What::Max(a.clone(), b.clone()),
                            };
                            tr.aux(what, def);
                            Some(x)
                        })
                    }
                    // Rung 2 only, as a quotient by a term is: the linear stage reads every
                    // definition as fixing its variable (`projected`), and this one does not.
                    BitAnd if products => {
                        let (a, b) = (arg(0).await?, arg(1).await?);
                        self.tr(|tr| {
                            let x = Lin::atom(presburger::Atom::Aux(tr.defs.len() as u32));
                            let def = bit_and_bounds(&x, &a, &b);
                            tr.aux(What::BitAnd(a, b), def);
                            Some(x)
                        })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The formula a test states over the inputs.
    fn formula(&'m self, t: Tid, env: Eid) -> Deep<'m, Option<Formula>> {
        self.translated(
            |m| &mut m.formula,
            (t, env),
            Logged::Formula,
            move || self.formula_at(t, env),
        )
    }

    /// The condition, over the inputs and the auxiliary variables of the translation, that the
    /// value of `t` read in `env` is not an atom, for a relation that must hold exactly where
    /// the interpreter's value of its test is `true` ([`Tr::definedness`], RUNG2-definedness).
    /// It follows the interpreter (DESIGN.md M0.9 (a)): only a quotient or remainder by a term
    /// fails at a point of the domain, where the divisor is 0 ([`Tr::div_mod_by_term`]); every
    /// other primitive passes an atom of an operand on, `==` and `!=` compare atoms and never
    /// fail, an `if` fails where its guard fails or where the arm it takes fails, and a `let` or
    /// a call binds an atom as a value, so the body fails only where it reads one.
    ///
    /// With `D` this condition and `C` the formula of a test ([`Walk::formula`]), the test is
    /// `true` exactly where `D ∧ C` holds, and `false` exactly where `D ∧ ¬C` does, by
    /// induction on the term: where an operand is defined, its translation is its value, and
    /// `==` and `!=` of operands that may fail are exact themselves ([`Walk::exactly_equal`]).
    /// So `¬C` at an `if`'s guard, a `!` and the short-circuit operators, which the elaborator
    /// writes as `if`s, needs no condition of its own.
    ///
    /// Memoized by term and scope, and a call whose arguments cannot fail by its key
    /// ([`Walk::shared_call_key`]), as the formula is, so it costs O(1) beside each entry of
    /// the translation: each node of the condition is made once and shared.
    fn defined(&'m self, t: Tid, env: Eid) -> Deep<'m, Option<Defined>> {
        self.translated(
            |m| &mut m.defined,
            (t, env),
            Logged::Defined,
            move || self.defined_at(t, env),
        )
    }

    async fn defined_at(&'m self, t: Tid, env: Eid) -> Option<Defined> {
        use Prim::*;
        if let Some(v) = self.constant(t, env).await {
            return Some(match v {
                Value::Atom(_) => Defined::failed(),
                _ => Defined::top(),
            });
        }
        match self.node(t) {
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.defined(bt, be).await,
                None => Some(Defined::top()),
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.defined(b, inner).await
            }
            Node::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    match self.shared_call_key(body, lam, args, env).await {
                        Some(k) => {
                            let call = self.translated(
                                |m| &mut m.defined_calls,
                                k.clone(),
                                Logged::DefinedCall,
                                move || self.defined_called(t, ps, (body, lam), args, env, k),
                            );
                            call.await
                        }
                        None => self.defined_call(t, ps, (body, lam), args, env).await,
                    }
                }
                Callee::Prim(p) => {
                    let c = self.with(|tx| tx.terms.call(t, p, args));
                    self.defined(c, env).await
                }
                Callee::Lam(..) => None,
            },
            Node::If(..) if self.and_if(t).is_some() => self.defined_chain(Prim::And, t, env).await,
            Node::If(..) if self.or_if(t).is_some() => self.defined_chain(Prim::Or, t, env).await,
            // The guard's condition, and the condition of the arm it takes, where the guard
            // does not show it already ([`Defined::arm`]): `if n != 0 { x mod n } else { 0 }`
            // never fails, so that the disjunction of the two arms is `true` and needs no
            // case split.
            Node::If(g, a, b) => {
                let parts = !self.whole(g, env);
                let dg = self.defined(g, env).await?;
                let cg = self.formula(g, env).await?;
                let (da, db) = (self.defined(a, env).await?, self.defined(b, env).await?);
                let not_cg = Formula::negate(cg.clone());
                let known = dg.divisors;
                let fa = self.tr(|tr| Defined::arm(&da, &cg, parts, known, &mut tr.sets));
                let fb = self.tr(|tr| Defined::arm(&db, &not_cg, true, known, &mut tr.sets));
                if is_true(&fa) && is_true(&fb) {
                    return Some(dg);
                }
                let rest = Formula::or(vec![keep_all(vec![cg, fa]), keep_all(vec![not_cg, fb])]);
                let d = Defined {
                    rest,
                    ..Defined::top()
                };
                Some(self.tr(|tr| dg.meet(d, &mut tr.sets)))
            }
            Node::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => {
                if matches!(p, Eq | Ne) {
                    return Some(Defined::top());
                }
                let mut d = Defined::top();
                for i in 0..args.len() {
                    let e = self.defined(self.arg(args, i), env).await?;
                    d = self.tr(|tr| d.meet(e, &mut tr.sets));
                }
                if matches!(p, IntDiv | Mod)
                    && let n = self.arg(args, 1)
                    && self.constant_int(n, env).await.is_none()
                {
                    let n = self.lin(n, env).await?;
                    d = self.tr(|tr| d.with_divisor(&n, &mut tr.sets));
                }
                Some(d)
            }
            _ => None,
        }
    }

    /// The condition of the call at `t` of the lambda `(body, lam)` under its key `k`
    /// ([`Walk::shared_call_key`]). When the call may be claimed ([`Walk::claimable`]), it is
    /// its callee's condition over its canonical atoms ([`Walk::canonical_defined`]), made once
    /// for every call of it, as the relation is ([`Walk::formula_called`]): `true` when that
    /// is `true`; as it is, beside the constraint of the binding, when the call holds the
    /// callee's claim, so that the binding's definition writes the canonical atoms as the
    /// arguments; and written at the arguments when another call holds it
    /// ([`Defined::instance`]). A call reads no claim of its own here, since the claim's kind
    /// is its formula's or its term's to choose. Otherwise, and where the condition reads an
    /// auxiliary variable the writing cannot copy, it is the callee's body read in the call's
    /// scope ([`Walk::defined_call`]).
    // Complexity tradeoff: a call that holds no claim costs its callee's condition, written at
    // its arguments, O(the condition's divisors and parts), or its callee's cone where the
    // condition reads a quotient by a term or another variable of no copy, as a call that
    // holds no claim costs its callee's projection or its cone for the relation
    // ([`Walk::formula_called`]). Trigger: a function whose condition is large called with
    // another argument list by each link of a chain. Test
    // `l01_38_presburger::one_scope::the_relations_of_a_chain_dividing_by_its_argument_scale`.
    // COMPLEXITY.md row RUNG2-definedness. A complete solution is the one of the relation
    // (LOAD-call-relation): the canonical atoms indexed by the call.
    #[allow(clippy::too_many_arguments)]
    async fn defined_called(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Span,
        env: Eid,
        k: CallKey,
    ) -> Option<Defined> {
        use presburger::Atom;
        if let Some(key) = self.claimable(ps, &k) {
            // A key equal to the call's own is the entry being made, so read it here.
            let at = Some((args, env));
            let d = match key == k.1 {
                true => (self.canonical_defined_read(t, ps, (body, lam), at, key.clone())).await,
                false => {
                    self.canonical_defined(t, ps, (body, lam), at, key.clone())
                        .await
                }
            };
            if let Some(d) = d {
                if d.is_top() || key == k.1 {
                    return Some(d);
                }
                // The constraint of the binding, `b == n` or `b == value`, when the call holds
                // the claim.
                let held = self.tr(|tr| match tr.claims.get(&(body, lam)) {
                    Some((a, n)) if *a == k.1 => {
                        let at = match &tr.defs[*n as usize].1 {
                            What::Value(l, _) => l.clone(),
                            _ => Lin::constant(*n as i64),
                        };
                        Some(Formula::Con(Con::eq(&Lin::atom(Atom::Aux(*n)), &at)))
                    }
                    _ => None,
                });
                if let Some(rest) = held {
                    let b = Defined {
                        rest,
                        ..Defined::top()
                    };
                    return Some(self.tr(|tr| d.meet(b, &mut tr.sets)));
                }
                let to = arguments_of(&key, &k.1);
                if let Some(d) = self.tr(|tr| d.instance(tr, &to)) {
                    return Some(d);
                }
            }
        }
        self.defined_call(t, ps, (body, lam), args, env).await
    }

    /// [`Walk::lin_call`] for [`Walk::defined`].
    async fn defined_call(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Span,
        env: Eid,
    ) -> Option<Defined> {
        let place = self.with(|tx| tx.enter(t, body))?;
        let inner = self.call_env(ps, args, lam, env);
        let d = self.defined(body, inner).await;
        self.with(|tx| tx.leave(body, place));
        d
    }

    /// The condition of the lambda `(body, lam)` over its canonical atoms, as the canonical key
    /// `key` gives them, remembered under that key as [`Walk::canonical_formula`] remembers the
    /// relation, so every claimable call of it and its own question share one.
    fn canonical_defined(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Option<(Span, Eid)>,
        key: Vec<Lin>,
    ) -> Deep<'m, Option<Defined>> {
        let k = ((body, lam), key.clone(), Vec::new());
        self.translated(
            |m| &mut m.defined_calls,
            k,
            Logged::DefinedCall,
            move || self.canonical_defined_read(t, ps, (body, lam), args, key),
        )
    }

    /// What [`Walk::canonical_defined`] remembers: the body read under [`Walk::canonical_env`].
    async fn canonical_defined_read(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Option<(Span, Eid)>,
        key: Vec<Lin>,
    ) -> Option<Defined> {
        let place = self.with(|tx| tx.enter(t, body))?;
        let inner = self.canonical_env(ps, lam, args, &key);
        let d = self.defined(body, inner).await;
        self.with(|tx| tx.leave(body, place));
        d
    }

    /// The key a call is translated under ([`Walk::call_key`]), with, when the relation must
    /// hold exactly where its test is `true` ([`Tr::definedness`]) and an argument may fail,
    /// the condition that each argument is not an atom, by the number of its set of divisors
    /// ([`DivisorSets`]) and of its other part ([`FormulaNumbers`]). The arguments' linear terms are
    /// their values only where they are defined, and an argument that fails where another with
    /// the same term does not (`(x mod n) * 0` and `0`) gives the callee's `==` another value,
    /// so two calls share a translation only when their arguments have the same terms and the
    /// same conditions. Two calls whose arguments were made apart but alike,
    /// `f(x mod n, n) && f(x mod n, n)`, so share one, and k functions, each calling the one
    /// before twice so, are read once each. O(the arguments) beside their translations.
    async fn shared_call_key(
        &'m self,
        body: Tid,
        lam: Eid,
        args: Span,
        env: Eid,
    ) -> Option<CallKey> {
        let mut k = self.call_key(body, lam, args, env).await?;
        if !self.tr(|tr| tr.definedness) {
            return Some(k);
        }
        let mut conds = Vec::with_capacity(args.len());
        for i in 0..args.len() {
            conds.push(self.defined(self.arg(args, i), env).await?);
        }
        if conds.iter().any(|d| !d.is_top()) {
            k.2 = self.tr(|tr| {
                (conds.iter())
                    .map(|d| (d.divisors, tr.numbers.number(&d.rest)))
                    .collect()
            });
        }
        Some(k)
    }

    /// `same`, the formula of `a == b` where both operands are defined, made exact where one
    /// may fail, when the relation must hold exactly where its test is `true`
    /// ([`Tr::definedness`]): the interpreter compares atoms as data (DESIGN.md M0.9 (a)), and
    /// the one failure of the domain, `#divByZero`, merged with itself is itself, so `a == b`
    /// holds where both are defined and `same` holds, and where both fail.
    async fn exactly_equal(&'m self, same: Formula, a: Tid, b: Tid, env: Eid) -> Option<Formula> {
        if !self.tr(|tr| tr.definedness) {
            return Some(same);
        }
        let (da, db) = (self.defined(a, env).await?, self.defined(b, env).await?);
        if da.is_top() && db.is_top() {
            return Some(same);
        }
        let (da, db) = (da.formula(), db.formula());
        Some(Formula::or(vec![
            keep_all(vec![da.clone(), db.clone(), same]),
            keep_all(vec![Formula::negate(da), Formula::negate(db)]),
        ]))
    }

    /// [`Walk::lin_call`] for a test.
    async fn formula_call(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Span,
        env: Eid,
    ) -> Option<Formula> {
        let place = self.with(|tx| tx.enter(t, body))?;
        let inner = self.call_env(ps, args, lam, env);
        let f = self.formula(body, inner).await;
        self.with(|tx| tx.leave(body, place));
        f
    }

    /// The canonical key of the call `k` of a lambda of parameters `ps`, when the call may be
    /// claimed (LOAD-chain-affine): the run reads a body under a [`Scoped`] scope, the lambda
    /// is one of the scope's, an argument is not a constant, and no argument holds a product;
    /// whether the lambda's claim is free is [`Walk::binding`]'s question. Each constant is
    /// itself, so constants still fold in the callee, and so is the atom of the parameter's
    /// class ([`Tx::class`]); each other argument is the canonical atom of its parameter
    /// ([`Tx::canonical`]). A call with an argument that may fail ([`Walk::shared_call_key`])
    /// is not claimed: its canonical atoms would stand for values that may be atoms.
    fn claimable(&self, ps: Span, (lam, args, conds): &CallKey) -> Option<Vec<Lin>> {
        use presburger::Atom;
        let free = conds.is_empty()
            && self.with(|tx| {
                tx.fresh.as_ref().is_some_and(|f| !f.of_body(*lam))
                    && args.iter().any(|l| !l.terms.is_empty())
                    && !(args.iter().flat_map(|l| l.terms.keys()))
                        .any(|a| matches!(a, Atom::Product(..)))
            });
        free.then(|| {
            self.with(|tx| {
                (args.iter().enumerate())
                    .map(|(i, l)| {
                        let class = Lin::atom(Atom::Sym(tx.class(ps, i, *lam)));
                        match l.terms.is_empty() || *l == class {
                            true => l.clone(),
                            false => Lin::atom(Atom::Sym(tx.canonical(ps, i, *lam))),
                        }
                    })
                    .collect()
            })
        })
    }

    /// The variable binding the canonical atoms of `key`, the canonical key of the call `args`
    /// of the lambda `lam`, to the arguments: the claim's own when the call holds it, a new one
    /// claiming the lambda when it is free, and `None` when another call holds it. Its
    /// definition is `b == n` for its number n, or `b == value` for the value of an integer
    /// function, and each
    /// canonical atom equal to its argument: a binding holds for one value of `b` and of the
    /// atoms whatever the values of the arguments' atoms, and each canonical atom has one, so
    /// the relations of the callee read under it hold where the callee's relation holds at
    /// the arguments.
    fn binding(&self, lam: At, args: &[Lin], key: &[Lin], value: Option<Lin>) -> Option<u32> {
        use presburger::Atom;
        self.tr(|tr| {
            if let Some((a, n)) = tr.claims.get(&lam) {
                return (a.as_slice() == args).then_some(*n);
            }
            let pairs: Vec<(Arc<str>, Lin)> = (key.iter().zip(args))
                .filter(|(c, a)| c != a)
                .filter_map(|(c, a)| match c.terms.keys().next()? {
                    Atom::Sym(c) => Some((c.clone(), a.clone())),
                    _ => None,
                })
                .collect();
            // An atom bound to a term over itself or another bound atom would equate them.
            let atoms: HashSet<Atom> = pairs.iter().map(|(c, _)| Atom::Sym(c.clone())).collect();
            if (pairs.iter()).any(|(_, a)| a.terms.keys().any(|x| atoms.contains(x))) {
                return None;
            }
            let n = tr.defs.len() as u32;
            let b = Lin::atom(Atom::Aux(n));
            let at = value.clone().unwrap_or_else(|| Lin::constant(n as i64));
            let mut parts = vec![Formula::Con(Con::eq(&b, &at))];
            parts.extend(
                (pairs.iter())
                    .map(|(c, a)| Formula::Con(Con::eq(&Lin::atom(Atom::Sym(c.clone())), a))),
            );
            let what = match value {
                Some(l) => What::Value(l, pairs),
                None => What::Bind(pairs),
            };
            tr.aux(what, Formula::and(parts));
            tr.claim(lam, args.to_vec(), n);
            Some(n)
        })
    }

    /// The scope the body of the lambda `(body, lam)` of parameters `ps` is read in under the
    /// canonical key `key`: each parameter whose key is a constant bound to its argument, read
    /// in the caller's scope (`args` and that scope, as [`Tx::call_env`] binds it), and each
    /// other to its atom in the key, an input of the run.
    fn canonical_env(&self, ps: Span, lam: Eid, args: Option<(Span, Eid)>, key: &[Lin]) -> Eid {
        use presburger::Atom;
        self.with(|tx| {
            let mut e = lam;
            for (i, l) in key.iter().enumerate() {
                let p = tx.param(ps, i);
                let to = match (args, l.terms.keys().next()) {
                    (Some((args, caller)), None) => (tx.arg(args, i), caller),
                    (_, Some(Atom::Sym(c))) => {
                        tx.cx.inputs.insert(c.clone(), Rc::new(IntervalSet::top()));
                        let c = tx.terms.name(c);
                        (tx.terms.own_var(c), ROOT)
                    }
                    _ => unreachable!("a key holds constants and atoms of parameters"),
                };
                e = tx.bind(e, p, to);
            }
            e
        })
    }

    /// The relation of the lambda `(body, lam)` of parameters `ps` over its canonical atoms, as
    /// the canonical key `key` gives them, remembered under that key, so every claimed call of
    /// it and its own question share one translation (LOAD-chain-affine). `t` is the call, or
    /// the lambda for its own question, where a stop under recursion is reported.
    fn canonical_formula(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Option<(Span, Eid)>,
        key: Vec<Lin>,
    ) -> Deep<'m, Option<Formula>> {
        let k = ((body, lam), key.clone(), Vec::new());
        self.translated(
            |m| &mut m.formula_calls,
            k,
            Logged::FormulaCall,
            move || self.canonical_formula_read(t, ps, (body, lam), args, key),
        )
    }

    /// The relation of the lambda `(body, lam)` over its canonical atoms with every other
    /// variable eliminated ([`projected`]), remembered under the canonical key `key`, so it
    /// is made once from the callee's canonical relation ([`Walk::canonical_formula`]) for
    /// all the calls of it that do not hold its claim (LOAD-affine-cone).
    fn projection(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Option<(Span, Eid)>,
        key: Vec<Lin>,
    ) -> Deep<'m, Option<Projection>> {
        let k = ((body, lam), key.clone(), Vec::new());
        self.translated(
            |m| &mut m.projections,
            k,
            Logged::Projection,
            move || async move {
                let r = self.canonical_formula(t, ps, (body, lam), args, key.clone());
                let r = r.await?;
                self.tr(|tr| projected(tr, &r, &key))
            },
        )
    }

    /// The value term of the integer lambda `(body, lam)` over its canonical atoms
    /// ([`value_projected`]), remembered under the canonical key `key` in the table of
    /// [`Walk::projection`], so it is made once from the callee's canonical term
    /// ([`Walk::canonical_lin`]) for all the calls of it that do not hold its claim
    /// (LOAD-call-relation). A lambda is a test or an integer function, so the two never
    /// share a key.
    #[allow(clippy::too_many_arguments)]
    fn value_projection(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Span,
        env: Eid,
        key: Vec<Lin>,
    ) -> Deep<'m, Option<Projection>> {
        let k = ((body, lam), key.clone(), Vec::new());
        self.translated(
            |m| &mut m.projections,
            k,
            Logged::Projection,
            move || async move {
                let l = self.canonical_lin(t, ps, (body, lam), args, env, key.clone());
                let l = l.await?;
                self.tr(|tr| value_projected(tr, &l, &key))
            },
        )
    }

    /// What [`Walk::canonical_formula`] remembers: the body read under [`Walk::canonical_env`].
    async fn canonical_formula_read(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Option<(Span, Eid)>,
        key: Vec<Lin>,
    ) -> Option<Formula> {
        let place = self.with(|tx| tx.enter(t, body))?;
        let inner = self.canonical_env(ps, lam, args, &key);
        let f = self.formula(body, inner).await;
        self.with(|tx| tx.leave(body, place));
        f
    }

    /// [`Walk::canonical_formula`] for an integer function.
    fn canonical_lin(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Span,
        env: Eid,
        key: Vec<Lin>,
    ) -> Deep<'m, Option<Lin>> {
        let k = ((body, lam), key.clone(), Vec::new());
        self.translated(
            |m| &mut m.lin_calls,
            k,
            Logged::LinCall,
            move || self.canonical_lin_read(t, ps, (body, lam), args, env, key),
        )
    }

    /// What [`Walk::canonical_lin`] remembers.
    async fn canonical_lin_read(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Span,
        env: Eid,
        key: Vec<Lin>,
    ) -> Option<Lin> {
        let place = self.with(|tx| tx.enter(t, body))?;
        let inner = self.canonical_env(ps, lam, Some((args, env)), &key);
        let l = self.lin(body, inner).await;
        self.with(|tx| tx.leave(body, place));
        l
    }

    /// The formula of the call at `t` of the lambda `(body, lam)`, under the key `k`: when the
    /// call may be claimed ([`Walk::claimable`]), its callee's canonical relation, shared, and
    /// `b == n` for the binding `b`, numbered n, of its canonical atoms to the arguments (each
    /// binding at its own number: two fixed to one value share every row, a tie the solver
    /// refuses), so a call costs
    /// O(its arguments) once its callee is translated, whatever map of the parameters the
    /// arguments are (LOAD-chain-affine); when another call holds the claim, the callee's
    /// relation with every other variable eliminated ([`Walk::projection`]), made once for the
    /// callee and written at the arguments ([`Tr::instance`]), so such a call costs O(the rows
    /// left) (LOAD-affine-cone), where the elimination keeps the quotients and remainders by
    /// constants it cannot remove, each written at the call as the pair of its dividend
    /// written there (LOAD-call-relation); otherwise the callee's body read with each parameter
    /// bound to its argument ([`Walk::formula_call`]), as it is when the callee's canonical
    /// relation is outside the domain or no projection is made.
    ///
    /// A canonical relation that is one constraint over symbols is written at the arguments
    /// instead ([`at_arguments`]), with no binding and no claim.
    // Complexity tradeoff: a call that holds no claim is its callee's relation with every
    // variable but the canonical atoms and the quotients and remainders by constants
    // eliminated, written at its arguments; where no such projection is made, a call of it with
    // other arguments reads its body again, and the calls in it whose arguments then differ
    // from their callees' claimed ones, so a function called with k argument lists is read k
    // times, O(k times its cone): a callee that chooses (a disjunction or a negation: `x != j`
    // in each link), a product, a quotient by a term, or an auxiliary variable of no definition.
    // Where it is made, the rows left are one for each linear form over the kept atoms, the
    // tighter kept: O(1) for one parameter and a chain whose links share one pair (`x mod 4 ==
    // 1` in each link), and up to the cone's for two or more parameters or many pairs, written
    // at each call; no exact bound on those rows is made. Why: the claimed call binds the
    // callee's canonical atoms, which one relation can bind once; an exact elimination of a
    // choice over the integers keeps each clause, O(the cone) at each call, the same as the
    // body. Trigger: one function with a large cone of such constraints called with another
    // argument list by each link of a chain, as `h(x: x)` in `p{i}(x) = h(x: x) && p{i-1}(x: x
    // + 1)` with `h` a chain of n links `h{j}(x) = h{j-1}(x: x) && x != j`: relations 0.051 s
    // at 50 links, 4.41 s at 400 (measured once). Congruences are kept: test
    // `l01_38_presburger::one_scope::
    // the_questions_of_a_chain_calling_a_callee_that_keeps_a_congruence_scale`, deferred to plan
    // row PRES-scaling-10_5 in wt/scratch/deferred-tests/PRES-scaling-10_5.rs. COMPLEXITY.md
    // row LOAD-call-relation. A complete solution would index the canonical atoms by the call,
    // so each call binds its own copy of them without copying the relation: a relation node
    // instantiated at the call, which the solver reads with the call's atoms; or, for one
    // parameter, the callee's holes as an interval map (item LOAD-bound-holes).
    async fn formula_called(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Span,
        env: Eid,
        k: CallKey,
    ) -> Option<Formula> {
        use presburger::Atom;
        if let Some(key) = self.claimable(ps, &k) {
            // A key equal to the call's own is the entry being made, so read it here.
            if key == k.1 {
                let f = self.canonical_formula_read(t, ps, (body, lam), Some((args, env)), key);
                let f = f.await;
                if let Some(f) = &f {
                    self.tr(|tr| tr.bound(f, &k.1));
                }
                return f;
            }
            let canonical =
                self.canonical_formula(t, ps, (body, lam), Some((args, env)), key.clone());
            let r = canonical.await;
            let one = r.as_ref().and_then(|r| match r {
                Formula::Con(c) => at_arguments(&c.lin, &key, &k.1),
                _ => None,
            });
            if let (Some(lin), Some(Formula::Con(c))) = (one, &r) {
                return Some(Formula::Con(Con { lin, rel: c.rel }));
            }
            if let Some(r) = r {
                if let Some(b) = self.binding((body, lam), &k.1, &key, None) {
                    self.tr(|tr| tr.bound(&r, &key));
                    let b =
                        Formula::Con(Con::eq(&Lin::atom(Atom::Aux(b)), &Lin::constant(b as i64)));
                    return Some(Formula::and_keeping(vec![r, b], |i| i == 0));
                }
                let p = self.projection(t, ps, (body, lam), Some((args, env)), key.clone());
                let p = p.await;
                if let Some(p) = p {
                    let to = arguments_of(&key, &k.1);
                    let at = self.tr(|tr| {
                        let mut done = HashMap::new();
                        (p.rows.iter())
                            .map(|c| {
                                let lin = tr.instance(&c.lin, &to, Some(&p.pairs), &mut done)?;
                                Some(Formula::Con(Con { lin, rel: c.rel }))
                            })
                            .collect::<Option<Vec<_>>>()
                    });
                    if let Some(parts) = at {
                        let f = Formula::and(parts);
                        self.tr(|tr| tr.bound(&f, &k.1));
                        return Some(f);
                    }
                }
            }
        }
        let f = self.formula_call(t, ps, (body, lam), args, env).await;
        if let Some(f) = &f {
            self.tr(|tr| tr.bound(f, &k.1));
        }
        f
    }

    /// [`Walk::formula_called`] for an integer function: when the call may be claimed and its
    /// callee's canonical term holds no product, the variable `v` of the binding, defined by
    /// `v == ` that term; when another call holds the claim, the term written over the
    /// canonical atoms and the quotients and remainders by constants of their terms
    /// ([`Walk::value_projection`]), made once and written at the arguments ([`Tr::instance`],
    /// LOAD-call-relation); otherwise the callee's body read with each parameter bound to its
    /// argument ([`Walk::lin_call`]). A product in the term is left to the substitution, since
    /// [`Scoped::written`] writes `v` as the term, and a product of `v` would be a product of
    /// products.
    /// A canonical term over symbols alone is written at the arguments ([`at_arguments`]).
    // Complexity tradeoff: a call that holds no claim, of a callee whose term reads an
    // auxiliary variable other than a quotient or remainder by a constant or a claimed call's
    // value (`if`, `min`, `abs`, a quotient by a term), reads its callee's body again, O(its
    // cone), as [`Walk::formula_called`] does where no projection is made: such a variable
    // needs a copy of its definition at each call, which no projection writes. Trigger: an
    // integer function with a large cone of such terms called with another argument list by
    // each link of a chain. Not measured. Quotients and remainders by constants are written
    // at the call: test `l01_38_presburger::one_scope::
    // the_relations_of_a_chain_calling_an_integer_function_scale`. Deciding such a chain's
    // questions (`presburger::extend`) still grows faster than n log n with the remainders
    // along it: 0.239 s at 50 links, 14.5 s at 400 (measured once), returned by item
    // LOAD-call-relation. COMPLEXITY.md row LOAD-call-relation.
    async fn lin_called(
        &'m self,
        t: Tid,
        ps: Span,
        (body, lam): At,
        args: Span,
        env: Eid,
        k: CallKey,
    ) -> Option<Lin> {
        use presburger::Atom;
        if let Some(key) = self.claimable(ps, &k) {
            if key == k.1 {
                let l = self
                    .canonical_lin_read(t, ps, (body, lam), args, env, key)
                    .await;
                // Complexity tradeoff: naive version returns a multi-term `Lin` directly on a
                // class-keyed call (`H mod 7 + H` returns `r_k + r_{k-1} + ... + r_1 + x`),
                // leaving no per-link `Def` node so each caller carries O(k) leaf remainders and
                // refuses past three live variables. Used: when `!tr.bodies`, a multi-term `Lin`
                // holding an `Aux` and no `Product` is bound once to a fresh `Aux(n) == l`
                // (`What::Value(l, [])`), O(l.terms) per link, giving `extend::Summaries` a
                // single `Def` node per link while `Scoped::written` and `value_projected`
                // substitute `l` back unchanged (LOAD-max-div-xr I12/I26). Tradeoffs: one `Def`
                // entry per class-keyed multi-term `Aux` call.
                if let Some(v) = &l
                    && !self.tr(|tr| tr.bodies)
                    && v.terms.len() > 1
                    && v.terms.keys().any(|a| matches!(a, Atom::Aux(_)))
                    && !v.terms.keys().any(|a| matches!(a, Atom::Product(..)))
                {
                    let a = self.tr(|tr| {
                        let b = Lin::atom(Atom::Aux(tr.defs.len() as u32));
                        tr.aux(
                            What::Value(v.clone(), Vec::new()),
                            Formula::And(presburger::Shared::new(vec![Formula::Con(Con::eq(
                                &b, v,
                            ))])),
                        )
                    });
                    return Some(Lin::atom(a));
                }
                return l;
            }
            let canonical = self.canonical_lin(t, ps, (body, lam), args, env, key.clone());
            let l = canonical.await;
            if let Some(s) = l.as_ref().and_then(|l| at_arguments(l, &key, &k.1)) {
                return Some(s);
            }
            if let Some(l) = l
                && !l.terms.keys().any(|a| matches!(a, Atom::Product(..)))
            {
                if let Some(v) = self.binding((body, lam), &k.1, &key, Some(l.clone())) {
                    return Some(Lin::atom(Atom::Aux(v)));
                }
                // Another call holds the claim: the callee's term over its canonical atoms
                // ([`Walk::value_projection`]), made once, written at the arguments, its
                // quotients and remainders by constants the pairs of its dividends so written
                // ([`Tr::instance`]), O(the term and its pairs).
                // The tests' reference reads the body again ([`Scoped::reading_bodies`]).
                if self.tr(|tr| tr.bodies) {
                    return self.lin_call(t, ps, (body, lam), args, env).await;
                }
                let p = self.value_projection(t, ps, (body, lam), args, env, key.clone());
                if let Some(p) = p.await
                    && let Some(v) = &p.value
                {
                    let to = arguments_of(&key, &k.1);
                    let mut done = HashMap::new();
                    if let Some(s) = self.tr(|tr| tr.instance(v, &to, Some(&p.pairs), &mut done)) {
                        return Some(s);
                    }
                }
            }
        }
        self.lin_call(t, ps, (body, lam), args, env).await
    }

    async fn formula_at(&'m self, t: Tid, env: Eid) -> Option<Formula> {
        use Prim::*;
        if let Some(v) = self.constant(t, env).await {
            return match v {
                Value::Bool(true) => Some(Formula::top()),
                Value::Bool(false) => Some(Formula::bottom()),
                _ => None,
            };
        }
        match self.node(t) {
            Node::Var(x) => {
                let (bt, be) = self.lookup(env, x)?;
                self.formula(bt, be).await
            }
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.formula(b, inner).await
            }
            Node::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    match self.shared_call_key(body, lam, args, env).await {
                        Some(k) => {
                            let call = self.translated(
                                |m| &mut m.formula_calls,
                                k.clone(),
                                Logged::FormulaCall,
                                move || self.formula_called(t, ps, (body, lam), args, env, k),
                            );
                            call.await
                        }
                        None => self.formula_call(t, ps, (body, lam), args, env).await,
                    }
                }
                Callee::Prim(p) => {
                    let c = self.with(|tx| tx.terms.call(t, p, args));
                    self.formula(c, env).await
                }
                Callee::Lam(..) => None,
            },
            // `g && a` as the elaborator writes it, read as a chain ([`Walk::chain`]); the
            // translation two at a time reads it as any other `if`, below.
            Node::If(..) if self.and_if(t).is_some() && !two_at_a_time() => {
                self.chain(Prim::And, t, env).await
            }
            // `g || b` as the elaborator writes it, `if g { true } else { b }`, has the formula
            // of `g || b` ([`Walk::or_if`]), read as a chain ([`Walk::chain`]); the translation
            // two at a time joins its two operands at once.
            Node::If(..) if self.or_if(t).is_some() && !or_if_as_if() => {
                #[cfg(test)]
                if presburger::TWO_AT_A_TIME.get() {
                    let (g, a, b) = self.or_if(t).expect("an `if` that is a `||`");
                    let named = [g, b].map(|t| self.whole(t, env));
                    let fg = self.formula(g, env).await?;
                    self.formula(a, env).await?;
                    let fb = self.formula(b, env).await?;
                    return Some(Formula::or_keeping(vec![fg, fb], |i| named[i]));
                }
                self.chain(Prim::Or, t, env).await
            }
            Node::If(g, a, b) => {
                // The formula of a name is kept whole, as for `&&` below, and a claimed call's
                // parts are added ([`Walk::claimed`]).
                let mut named = [g, a, b].map(|t| self.whole(t, env));
                let g = self.formula(g, env).await?;
                let (fa, fb) = (self.formula(a, env).await?, self.formula(b, env).await?);
                for (i, f) in [&g, &fa, &fb].into_iter().enumerate() {
                    named[i] = named[i] && !self.claimed(f);
                }
                Some(Formula::or(vec![
                    Formula::and_keeping(vec![g.clone(), fa], |i| named[i]),
                    Formula::and_keeping(vec![Formula::negate(g), fb], |i| i == 1 && named[2]),
                ]))
            }
            Node::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => {
                let (a, b) = (
                    self.arg(args, 0),
                    (args.len() > 1).then(|| self.arg(args, 1)),
                );
                match p {
                    Not => Some(Formula::negate(self.formula(a, env).await?)),
                    And | Or => {
                        #[cfg(test)]
                        if presburger::TWO_AT_A_TIME.get() {
                            return self
                                .two_at_a_time(p, a, b.expect("two operands"), env)
                                .await;
                        }
                        self.chain(p, t, env).await
                    }
                    Lt | Le | Gt | Ge | Eq | Ne => {
                        let b = b.expect("two operands");
                        let mark = self.tr(|tr| tr.defs.len());
                        let logged = self.with(|tx| tx.run.memo.log.len());
                        let (la, lb) = (self.lin(a, env).await, self.lin(b, env).await);
                        if let (Some(la), Some(lb)) = (la, lb) {
                            let one = Lin::constant(1);
                            let c = match p {
                                Lt => Con::ge(&lb, &la.plus(&one)),
                                Le => Con::ge(&lb, &la),
                                Gt => Con::ge(&la, &lb.plus(&one)),
                                Ge => Con::ge(&la, &lb),
                                _ => Con::eq(&la, &lb),
                            };
                            let f = Formula::Con(c);
                            let f = match p {
                                Eq | Ne => self.exactly_equal(f, a, b, env).await?,
                                _ => f,
                            };
                            return Some(if p == Ne { Formula::negate(f) } else { f });
                        }
                        self.tr(|tr| tr.truncate(mark));
                        self.with(|tx| tx.forget(logged));
                        if !matches!(p, Eq | Ne) {
                            return None;
                        }
                        // Two tests are equal where both hold or neither does.
                        let (fa, fb) = (self.formula(a, env).await?, self.formula(b, env).await?);
                        let same = Formula::or(vec![
                            Formula::and(vec![fa.clone(), fb.clone()]),
                            Formula::and(vec![Formula::negate(fa), Formula::negate(fb)]),
                        ]);
                        let same = self.exactly_equal(same, a, b, env).await?;
                        Some(if p == Ne { Formula::negate(same) } else { same })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The condition of the chain of `&&` (`p` is `And`) or `||` that the `if` `head` heads,
    /// as the elaborator writes them ([`Walk::and_if`], [`Walk::or_if`]): its operands
    /// `o1, ..., ok` in order, each with its condition `Di` and its formula `Ci`. Unlike
    /// [`Walk::chain`], the walk also reads through a part the program shares (a prefix of the
    /// chain bound to a name, or a body cloned while its function stays bound): a condition
    /// is a fact about the values, the same wherever the part is written, and a part left
    /// whole would bring back the negation of its whole conjunction. The walk keeps a visited
    /// set, so a part met twice is read once, at its first place: a `&&` or `||` of an operand
    /// with itself adds no condition. A `&&` reads `o(i+1)` only where `oi` is `true`,
    /// so its condition is `D1 ∧ ((C1 ∧ (D2 ∧ ((C2 ∧ ...) ∨ ¬C2))) ∨ ¬C1)`, made from the last
    /// operand back, and a `||` reads it only where `oi` is `false`, with `Ci` and `¬Ci`
    /// swapped. Each `Di` past the first is `true` where the divisors of the operands before it
    /// and the parts of their guards show its divisors are not 0 ([`Shown::arm`]), as
    /// [`Defined::arm`] makes it at one `if`. The condition is O(k) nodes, each `Ci` shared.
    /// Read as nested `if`s, the condition of a chain of k `&&` written from the left held the
    /// negation of each prefix's conjunction, Θ(k²) constraints once the negations were pushed
    /// in, and the solver's time grew as k³ (PRES-mod-conjuncts); read as nested `if`s from the
    /// right, it was already this one.
    // Complexity tradeoff: an operand whose divisors are not all among those of the operands
    // before it costs a question for each of its divisors, O(m log n), so a chain whose
    // operands each read a large shared part with a new divisor costs the part's divisors at
    // each. No point is given up. Trigger: a named term of many quotients read in each operand
    // beside a divisor of its own. Test
    // `l01_38_presburger::ladder::a_chain_of_remainders_by_terms_scales`. COMPLEXITY.md row
    // PRES-mod-conjuncts. A complete solution keeps the divisors not yet shown as a set
    // difference, met once each.
    async fn defined_chain(&'m self, p: Prim, head: Tid, env: Eid) -> Option<Defined> {
        let inner = |u: Tid| match p {
            Prim::And => self.and_if(u).map(|(g, a, _)| [g, a]),
            _ => self.or_if(u).map(|(g, _, b)| [g, b]),
        };
        let mut ops = Vec::new();
        let mut todo = vec![head];
        let mut seen = HashSet::new();
        while let Some(u) = todo.pop() {
            if !seen.insert(u) {
                continue;
            }
            if let Some([l, r]) = inner(u)
                && (u == head || self.constant(u, env).await.is_none())
            {
                todo.extend([r, l]);
                continue;
            }
            ops.push(u);
        }
        let mut ds = Vec::with_capacity(ops.len());
        let mut cs = Vec::with_capacity(ops.len());
        for &u in &ops {
            ds.push(self.defined(u, env).await?);
            cs.push(self.formula(u, env).await?);
        }
        // Where each operand past the first is read, as the guard of its `if` shows it.
        let guard = |i: usize| match p {
            Prim::And => cs[i].clone(),
            _ => Formula::negate(cs[i].clone()),
        };
        let mut shown = Shown::default();
        let mut known = ds[0].divisors;
        let mut arms = Vec::with_capacity(ops.len());
        for i in 1..ops.len() {
            let parts = p != Prim::And || !self.whole(ops[i - 1], env);
            shown.add_guard(&guard(i - 1), parts);
            arms.push(self.tr(|tr| shown.arm(&ds[i], known, &mut tr.sets)));
            known = self.tr(|tr| tr.sets.union(known, ds[i].divisors));
        }
        let mut tail = Formula::top();
        for i in (0..ops.len() - 1).rev() {
            let next = match (arms.pop().expect("an arm"), is_true(&tail)) {
                (a, true) => a,
                (a, false) if is_true(&a) => tail,
                (a, false) => keep_all(vec![a, tail]),
            };
            if is_true(&next) {
                tail = next;
                continue;
            }
            let (c, not_c) = (cs[i].clone(), Formula::negate(cs[i].clone()));
            tail = match p {
                Prim::And => Formula::or(vec![keep_all(vec![c, next]), not_c]),
                _ => Formula::or(vec![c, keep_all(vec![not_c, next])]),
            };
        }
        let d0 = ds.swap_remove(0);
        if is_true(&tail) {
            return Some(d0);
        }
        let rest = Defined {
            rest: tail,
            ..Defined::top()
        };
        Some(self.tr(|tr| d0.meet(rest, &mut tr.sets)))
    }

    /// The formula of a `&&` (`p` is `And`) or a `||` whose term is `head`: the operands of
    /// the chain of `p` it heads, each operand that is itself a `p` with no constant value
    /// read through, joined as [`Formula::and_keeping`] or [`Formula::or_keeping`] would join
    /// them two at a time, but in one [`Joining`], so a chain of k operands costs O(k log k)
    /// and not O(k²) (ST-formula-k2). A `&&` is the primitive or, as the elaborator writes
    /// `a && b`, `if a { b } else { false }` ([`Walk::and_if`]), whose formula made apart is
    /// the disjunction of the conjunction of `a` and `b` with `false`, which is that
    /// conjunction: `false` is dropped, and a disjunction that [`Joining::finish`] made, as
    /// every one the translator meets is, is itself when its disjuncts are joined again (one
    /// level deep, [`Formula::into_parts`]). Before the `if` was read through, a chain of k
    /// `&&` made the conjunction of each prefix in turn, O(k²) (PREIMAGE-and-chain). A `||` is
    /// the primitive or, as the elaborator writes `a || b`, `if a { true } else { b }`
    /// ([`Walk::or_if`]), whose formula is that of `a || b` in both translations. Read as an
    /// `if`, its formula was `a || (!a && b)`, which holds at the same points but cannot be
    /// made in one pass: at each level of a chain of k `||` it is a new disjunction of the
    /// disjuncts of `a` and of `!a && b`, and `!a` holds `a` whole, so the formula of each
    /// prefix is a node of its own and the formula has O(k²) parts however they are shared
    /// (PREIMAGE-or-chain). The `true` is read for its memo entry, as the `false` of a `&&`
    /// is. The formula of a name is kept whole, so a named part used at many places is one node
    /// and not copied into each (COMPLEXITY.md S31b). The operands are read in order, as the
    /// two-at-a-time translation reads them, and the first that has no formula gives none for
    /// the whole. An operand of a primitive is held in its parent alone
    /// ([`Terms::ids`]), but one of an `if` may be shared ([`Terms::shared`]): an inner `p` that
    /// is shared is read as an operand, by its remembered formula, as the translation two at a
    /// time reads it, so that the chain read through is a tree, each of whose nodes is met once
    /// without a visited set. Read through at each place, a chain that shares its halves would
    /// take time of its size written out.
    async fn chain(&'m self, p: Prim, head: Tid, env: Eid) -> Option<Formula> {
        /// An operand to read, a term read for its memo entry alone (the `false` of an `if`
        /// that is a `&&` or the `true` of one that is a `||`, which the translation two at a
        /// time reads), or the end of an inner `p`, with where the joining was before its
        /// operands ([`Joining::close`]).
        enum Step {
            Operand(Tid),
            Read(Tid),
            Close(Mark),
        }
        // The steps of `u`'s operands, last first, where `u` is a `p` of the chain.
        let inner = |u: Tid| -> Option<Vec<Step>> {
            match self.node(u) {
                Node::Prim(q, args) if q == p && q.arity().is_none_or(|n| n == args.len()) => {
                    Some(vec![
                        Step::Operand(self.arg(args, 1)),
                        Step::Operand(self.arg(args, 0)),
                    ])
                }
                _ if p == Prim::And => self
                    .and_if(u)
                    .map(|(g, a, b)| vec![Step::Read(b), Step::Operand(a), Step::Operand(g)]),
                _ if p == Prim::Or && !or_if_as_if() => self
                    .or_if(u)
                    .map(|(g, a, b)| vec![Step::Operand(b), Step::Read(a), Step::Operand(g)]),
                _ => None,
            }
        };
        let mut j = Joining::new(p == Prim::And);
        let mut todo = inner(head).expect("a chain's head");
        while let Some(step) = todo.pop() {
            let u = match step {
                Step::Close(mark) => {
                    j.close(mark);
                    continue;
                }
                Step::Read(u) => {
                    self.formula(u, env).await?;
                    continue;
                }
                Step::Operand(u) => u,
            };
            if let Some(steps) = inner(u)
                && self.constant(u, env).await.is_none()
                && !self.with(|tx| tx.terms.shared.contains(&u))
            {
                todo.push(Step::Close(j.mark()));
                todo.extend(steps);
                continue;
            }
            let f = self.formula(u, env).await?;
            let keep = self.whole(u, env) && !self.claimed(&f);
            j.operand(f, keep);
        }
        Some(j.finish())
    }

    /// The guard, the then arm and the `false` of `u` where `u` is `if g { a } else { false }`,
    /// as the elaborator writes `g && a`.
    // Complexity tradeoff: naive version, each `if g { a } else { false }` of a chain read as an
    // `if`, `(g && a) || (!g && false)`, copying the whole prefix conjunction into a new one at
    // each level, O(k²) for a chain of k (3.57 times per doubling). Used: `Walk::chain` reads
    // such an `if` as a `&&`, its guard and then arm operands of one `Joining`, linear (2.00
    // times per doubling). Tradeoffs: the children of an `if` may be shared, so `Terms::shared`
    // records each subterm reached twice and a shared inner chain is read once by its memo
    // entry; the answers are the same. Tests
    // `l01_25_preimage_catalog::scaling::a_chain_of_and_written_as_ifs_is_joined_in_one_pass`
    // and `a_chain_of_or_written_as_ifs_is_joined_in_one_pass`; COMPLEXITY.md row S31c.
    fn and_if(&self, u: Tid) -> Option<(Tid, Tid, Tid)> {
        match self.node(u) {
            Node::If(g, a, b) if matches!(self.node(b), Node::Bool(false)) => Some((g, a, b)),
            _ => None,
        }
    }

    /// The guard, the `true` and the else arm of `u` where `u` is `if g { true } else { b }`,
    /// as the elaborator writes `g || b`, and `b` is not `false`: `if g { true } else { false }`
    /// is read as `g && true` ([`Walk::and_if`]), whose formula is that of `g` too.
    fn or_if(&self, u: Tid) -> Option<(Tid, Tid, Tid)> {
        match self.node(u) {
            Node::If(g, a, b)
                if matches!(self.node(a), Node::Bool(true))
                    && !matches!(self.node(b), Node::Bool(false)) =>
            {
                Some((g, a, b))
            }
            _ => None,
        }
    }

    /// The formula of a `&&` or `||` as the translator made it before [`Walk::chain`]
    /// (64781908): each operand by [`Walk::formula`], an inner `&&` with its own memo entry,
    /// and the two joined at once; for the tests that compare the two (ST-formula-k2).
    #[cfg(test)]
    async fn two_at_a_time(&'m self, p: Prim, a: Tid, b: Tid, env: Eid) -> Option<Formula> {
        let named = [a, b].map(|t| self.whole(t, env));
        let (a, b) = (self.formula(a, env).await?, self.formula(b, env).await?);
        Some(if p == Prim::And {
            Formula::and_keeping(vec![a, b], |i| named[i])
        } else {
            Formula::or_keeping(vec![a, b], |i| named[i])
        })
    }
}

/// Whether the tests have chosen the translation of `&&` and `||` two at a time
/// (`presburger::TWO_AT_A_TIME`), which they compare with [`Walk::chain`].
fn two_at_a_time() -> bool {
    #[cfg(test)]
    return presburger::TWO_AT_A_TIME.get();
    #[cfg(not(test))]
    false
}

#[cfg(test)]
thread_local! {
    /// Whether the tests have chosen the translation of `if g { true } else { b }` as any other
    /// `if`, `g || (!g && b)`, as it was before [`Walk::or_if`], to compare the points at which
    /// the two formulas hold (PREIMAGE-or-chain).
    static OR_IF_AS_IF: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether the tests have chosen the translation of `if g { true } else { b }` as any other
/// `if` (`OR_IF_AS_IF`).
fn or_if_as_if() -> bool {
    #[cfg(test)]
    return OR_IF_AS_IF.get();
    #[cfg(not(test))]
    false
}

/// An integer term as a function of one input `var` (R1_GEMINI Thm 3.1: the value of a term
/// built from one input by `if`s on that input, constants, negation, adding a constant and
/// multiplying by one, and adding two such terms each affine over the whole domain, is affine
/// on each of finitely many intervals of the input, cut at the domain's and the guards'
/// ends). The coefficients, constants and values are unbounded ([`Int`], one machine word
/// while they fit in `i128`), so no affine step is given up at any size: a chain of `d`
/// doublings is summarized at every `d`, with coefficients of `d` bits. Kernel integers are
/// unbounded, so a value outside `i64` is a value of the term, and the summary reads it as
/// one: `i64::MIN - (u + 3)` is summarized, although its constant `i64::MIN - 3` lies outside
/// `i64`, and so is `u + 1` at `u = i64::MAX`. At an infinite end of the domain a piece takes
/// the infinity its line tends to ([`value_at`]), never the value at an end of `i64`.
// Complexity tradeoff: naive version, the backward transfer asks a term shared by both arms
// of k `if`s, one arm adding a constant, for `t >= -d` at each `d` up to `k - j`, O(k²) (58.7
// times from 256 to 2,048). Used: a term of one input built from `if`, `+ c`, `- c`, `0 - x`,
// `c * x` and negation is summarized once as a persistent treap of affine pieces, and a
// demand is inverted by descending only into subtrees whose values meet it, each integer
// demand first met with the hull of the term's values: O(k log k) (7.4 times). Tradeoffs:
// one input only; a term outside that grammar falls back to the transfer; the hull may
// narrow a box the old `map2` piece cap widened, a sound subset
// (`meeting_a_demand_with_the_hull_may_narrow_a_box_the_map2_cap_widened`). Tests
// `l01_25_preimage_catalog::s22` (compared with the transfer before on 22,628 cases) and
// `long_shared_values_preimage`; COMPLEXITY.md row S22.
#[derive(Clone)]
enum Pa {
    /// The constant `c` everywhere.
    Const(Int),
    /// `a * var + b` over the whole domain of `var`.
    Linear { var: Arc<str>, a: Int, b: Int },
    /// Disjoint intervals of `var`, on each of which the value is affine; a gap is a part of
    /// the domain where the term has no integer value.
    Piecewise { var: Arc<str>, root: Tree },
}

impl PartialEq for Pa {
    /// The same input and the same pieces with the same lines ([`pa_pieces`]): at once for
    /// two copies of one tree, else `O(p)` for `p` pieces.
    fn eq(&self, other: &Pa) -> bool {
        match (self, other) {
            (Pa::Piecewise { var: v, root: r }, Pa::Piecewise { var: w, root: s }) => {
                v == w
                    && (match (r, s) {
                        (Some(r), Some(s)) => Arc::ptr_eq(r, s),
                        _ => r.is_none() && s.is_none(),
                    } || pa_pieces(self) == pa_pieces(other))
            }
            (Pa::Piecewise { .. }, _) | (_, Pa::Piecewise { .. }) => false,
            _ => self.var() == other.var() && pa_pieces(self) == pa_pieces(other),
        }
    }
}

impl Pa {
    fn var(&self) -> Option<&Arc<str>> {
        match self {
            Pa::Const(_) => None,
            Pa::Linear { var, .. } | Pa::Piecewise { var, .. } => Some(var),
        }
    }

    /// `mul * self + add`.
    fn affine(&self, mul: impl Into<Int>, add: impl Into<Int>) -> Pa {
        let (mul, add) = (mul.into(), add.into());
        match self {
            Pa::Const(c) => Pa::Const(&(c * &mul) + &add),
            Pa::Linear { var, a, b } => Pa::Linear {
                var: var.clone(),
                a: a * &mul,
                b: &(b * &mul) + &add,
            },
            Pa::Piecewise { var, root } => Pa::Piecewise {
                var: var.clone(),
                root: root.as_ref().map(|r| apply_tag(r, &Tag::affine(mul, add))),
            },
        }
    }

    /// `self + sign * other`, for `sign` 1 or -1, exact for every pair of summaries of at
    /// most one input (`n + n`, `n - 2 * n`, `n + (if n > 0 { n } else { 0 })`): with a
    /// constant, the other mapped ([`Pa::affine`]); two lines, a line, `O(1)`; a line and a
    /// [`Pa::Piecewise`], the line added to every piece by one tag at the root ([`Tag`]),
    /// `O(1)`, the pieces lying within the input's domain, where the line is defined; two
    /// piecewise summaries, [`add_treaps`], `O(m log(n / m + 1))` for `m <= n` pieces.
    /// `None` when the two read different inputs.
    fn plus(&self, other: &Pa, sign: i128) -> Option<Pa> {
        let sign = Int::from(sign);
        let piecewise = |var: &Arc<str>, root: &Tree, f: Tag| Pa::Piecewise {
            var: var.clone(),
            root: root.as_ref().map(|r| apply_tag(r, &f)),
        };
        Some(match (self, other) {
            (Pa::Const(c), o) => o.affine(sign, c.clone()),
            (s, Pa::Const(c)) => s.affine(1, &sign * c),
            _ if self.var() != other.var() => return None,
            (Pa::Linear { var, a, b }, Pa::Linear { a: c, b: e, .. }) => Pa::Linear {
                var: var.clone(),
                a: a + &(c * &sign),
                b: b + &(e * &sign),
            },
            (Pa::Linear { a, b, .. }, Pa::Piecewise { var, root }) => piecewise(
                var,
                root,
                Tag {
                    mul: sign,
                    slope: a.clone(),
                    add: b.clone(),
                },
            ),
            (Pa::Piecewise { var, root }, Pa::Linear { a, b, .. }) => piecewise(
                var,
                root,
                Tag {
                    mul: Int::ONE,
                    slope: a * &sign,
                    add: b * &sign,
                },
            ),
            (Pa::Piecewise { var, root: p }, Pa::Piecewise { root: q, .. }) => Pa::Piecewise {
                var: var.clone(),
                root: add_treaps(p, q, &sign),
            },
        })
    }

    /// The treap over the hull of `dom`, the domain of the input, or `None` when an end of
    /// `dom` lies outside [`in_range`]. A hole of `dom` is no cut: the values there are read by
    /// no one, since each reader meets what it finds with `dom` ([`Tx::invert_pa`]) or slices
    /// it to a part of `dom` ([`Walk::pa_select`]), and cut at the holes, the summary of each
    /// class of a split carried every hole another class made, `O(k^2)` pieces for a chain of
    /// `k` guards (COMPLEXITY.md S22-hole-summaries).
    // Complexity tradeoff: naive version, the summary cut at every hole of the domain, O(k²)
    // pieces for k guards (953 cases, 8.3 s at k = 32; 77 GB at 128). Used: the summary over the
    // hull, with `Walk::pa_select` giving a hole to the stretch before it (`no_input_between`,
    // O(log P)), `2k + 1 + 3T` cases (729 at k = 256). Tradeoffs: the summary claims values at
    // the holes, which is sound only because every reader meets its result with the domain or
    // slices it to a part of the domain; a new reader must do the same. Test
    // `l01_25_preimage_catalog::s22::class_ranges_read_the_holes_once`, deferred to plan row
    // S22-scaling-10_5 in wt/scratch/deferred-tests/S22-scaling-10_5.rs; COMPLEXITY.md row
    // S22-hole-summaries.
    fn to_treap(&self, dom: &IntervalSet) -> Option<Tree> {
        let (a, b) = match self {
            Pa::Piecewise { root, .. } => return Some(root.clone()),
            Pa::Const(c) => (Int::ZERO, c.clone()),
            Pa::Linear { a, b, .. } => (a.clone(), b.clone()),
        };
        if !in_range(dom) {
            return None;
        }
        let mut root = None;
        for (lo, hi) in dom.hull().pieces() {
            root = join_treap(
                root,
                Some(make_node(
                    lo.clone(),
                    hi.clone(),
                    a.clone(),
                    b.clone(),
                    None,
                    None,
                )),
            );
        }
        Some(root)
    }

    /// `min(self, c)`, or `max(self, c)` where not `min`, over `dom`, the domain of the input
    /// ([`clamp_treap`]).
    fn clamp(&self, min: bool, c: i64, dom: &IntervalSet) -> Option<Pa> {
        let c = Int::from(c);
        let var = match self {
            Pa::Const(v) => {
                return Some(Pa::Const(if min {
                    v.clone().min(c)
                } else {
                    v.clone().max(c)
                }));
            }
            Pa::Linear { var, .. } | Pa::Piecewise { var, .. } => var.clone(),
        };
        let root = clamp_treap(&self.to_treap(dom)?, min, &c);
        Some(Pa::Piecewise { var, root })
    }

    /// Over the hull of `dom`, the domain of `var`: the line `neg` where the line `d` is
    /// negative and the line `pos` where it is not, each piece made from its own line
    /// ([`make_node`]), so the bounds every node keeps are exact. `abs(u)` and `min` and `max`
    /// of two lines take this form; made as a clamp plus a line ([`Pa::plus`]) their bounds
    /// are those of [`Tag::vals`], infinite where the line and a piece slope in opposite
    /// directions over an unbounded piece, so a test of `abs(x) + y` read no bound on `y`.
    /// `None` when an end lies outside [`in_range`].
    fn by_sign(
        var: &Arc<str>,
        d: (&Int, &Int),
        dom: &IntervalSet,
        neg: (Int, Int),
        pos: (Int, Int),
    ) -> Option<Pa> {
        let (a, b) = d;
        let hull = dom.hull();
        let below = |c: Int| hull.meet(&IntervalSet::range(NegInf, Fin(Num::from(&c))));
        let from = |c: Int| hull.meet(&IntervalSet::range(Fin(Num::from(&c)), PosInf));
        // `a * x + b >= 0` holds for `x >= -floor(b / a)` when `a > 0`, and for
        // `x <= floor(b / -a)` when `a < 0`; the part below comes first.
        let ((lo_set, lo), (hi_set, hi)) = if a.is_zero() {
            let all = if b.is_negative() { neg } else { pos };
            ((hull, all), (IntervalSet::empty(), (Int::ZERO, Int::ZERO)))
        } else if a.is_positive() {
            let cut = -&b.div_floor(a);
            ((below(&cut - &Int::ONE), neg), (from(cut), pos))
        } else {
            let cut = b.div_floor(&-a);
            ((below(cut.clone()), pos), (from(&cut + &Int::ONE), neg))
        };
        let part = |set: &IntervalSet, (a, b): (Int, Int)| {
            Pa::Linear {
                var: var.clone(),
                a,
                b,
            }
            .to_treap(set)
        };
        let root = join_treap(part(&lo_set, lo)?, part(&hi_set, hi)?);
        Some(Pa::Piecewise {
            var: var.clone(),
            root,
        })
    }
}

/// The names bound by `let`s around a term that the transfer reads through their summaries,
/// each with the integers its product holds where the term is read ([`let_preimage`]).
pub type Lets = HashMap<Arc<str>, LetIn>;

/// A name of [`Lets`]: its summary and the integers its product holds.
#[derive(Clone, Debug)]
pub struct LetIn {
    /// The summary of the value bound.
    pub summary: LetPa,
    /// The integers the name's product holds.
    pub ints: IntervalSet,
    /// The summary's inputs read through a tree of its terms' bounds, which are then not among
    /// the inputs of the transfer ([`let_narrowing`]); `None` when they are.
    pub read: Option<Arc<dyn SummaryRead>>,
}

/// The value of a `let` over the inputs it reads, as the sum of one piecewise-affine summary
/// ([`Pa`]) of each input and a constant: `n + 2 * k - 1` is `n`, `2 * k` and `-1`. The value
/// at a point is the sum of each input's summary at it, defined where every one is.
///
/// Each term `(pa, at, b)` stands for `pa * (scale / at)`: `scale` is the product of the
/// factors the sum was multiplied by since the term was put in, so multiplying the sum by a
/// nonzero factor costs `O(1)` however many inputs it reads ([`Sep::scaled`]), and the
/// division is exact. The map is persistent, so a sum of two copies the smaller one into the
/// larger ([`Sep::add`]).
///
/// A sum formed over the domains of its inputs ([`LetPa::form`]) keeps `b`, the bounds of
/// `pa` over its input's domain, and in `tot` their sum ([`Tot`]), each put in as its term
/// is: so the bounds of the sum, with some inputs over other domains, cost those inputs
/// ([`LetPa::image_shifted`]) and not all of them.
///
/// Complexity tradeoff: naive version, the bounds of the value computed from every term's
/// bounds over its input's integers at each read (`Sep::bounds`, `pa_bounds` once per input),
/// O(k) a read for `k` inputs, so a chain of `d` bindings each reading the one before cost
/// Θ(d²) term bounds (COMPLEXITY.md rows PA-let-multi and PA-let-narrow-many: 2,275 at
/// d = 64, 132,867 at d = 512). Used: `tot` keeps the sum of the terms' bounds over the
/// domains formed over, and an input read over other integers adds its `Shift`, O(log k)
/// each, so a read costs the inputs that changed, not all `k`, and the chain O(d log d)
/// (323 and 2,563 at the same sizes). Tradeoffs: one `Tb` and the total kept per term;
/// `tot` is `None` when the sum was not formed over domains, and then `LetPa::image_shifted`
/// gives no image, so the checker binds the name with no narrowing from it (a loss of
/// precision, not of time); a sum scaled since its terms were put in makes every shift differ
/// (`LetPa::changed_since` returns `None`), and the read is made afresh, O(h log h) for the
/// `h` inputs the scope has.
#[derive(Clone)]
struct Sep {
    scale: Int,
    terms: imbl::OrdMap<Arc<str>, (Pa, Int, Tb)>,
    constant: Int,
    /// The sum of the terms' bounds `b`, when every term has them.
    tot: Option<Tot>,
}

/// What some inputs read over other integers than those a summary was formed over add to the
/// bounds of its value ([`LetPa::shift`]): a group under [`Shift::plus`], so that a sum of
/// shifts over many inputs is kept in a tree and one input's is changed in `O(log k)`.
#[derive(Clone)]
pub struct Shift(Tot);

impl Shift {
    /// Nothing added.
    pub const ZERO: Shift = Shift(Tot::ZERO);

    /// Both added.
    pub fn plus(&self, o: &Shift) -> Shift {
        Shift(self.0.plus(&o.0))
    }
}

/// The domain of an input, as a sum is formed over it ([`LetPa::form`]).
type Dom<'f, 'd> = &'f dyn Fn(&Arc<str>) -> Option<&'d IntervalSet>;

/// The bounds of one term of a sum ([`Sep`]) over the domain of its input ([`pa_bounds`]).
#[derive(Clone, PartialEq)]
enum Tb {
    /// Not taken: the sum was not formed over domains.
    Unset,
    /// The input has no domain.
    NoDom,
    /// The term has no value over the domain.
    NoVal,
    Of(Val, Val),
}

impl Tb {
    fn of(pa: &Pa, dom: Option<&IntervalSet>) -> Tb {
        match dom.map(|d| pa_bounds(pa, d)) {
            None => Tb::NoDom,
            Some(None) => Tb::NoVal,
            Some(Some((l, h))) => Tb::Of(l, h),
        }
    }
}

/// The sum of the bounds of a sum's terms ([`Tb`]), the infinite ends and the terms with no
/// value or no domain counted, so that one term's bounds are taken out and put back in `O(1)`.
#[derive(Clone)]
struct Tot {
    lo: Int,
    hi: Int,
    /// The terms whose least value is `Neg`, and `Pos`.
    lo_inf: [i64; 2],
    /// The terms whose greatest value is `Neg`, and `Pos`.
    hi_inf: [i64; 2],
    no_val: i64,
    no_dom: i64,
}

impl Tot {
    const ZERO: Tot = Tot {
        lo: Int::ZERO,
        hi: Int::ZERO,
        lo_inf: [0; 2],
        hi_inf: [0; 2],
        no_val: 0,
        no_dom: 0,
    };

    /// Puts in (`k` = 1) or takes out (`k` = -1) the bounds `b` times the nonzero factor `f`.
    fn put(&mut self, b: &Tb, f: &Int, k: i64) {
        let times = |v: &Val| match v {
            Val::Fin(x) => Val::Fin(x * f),
            Val::Neg if f.is_negative() => Val::Pos,
            Val::Pos if f.is_negative() => Val::Neg,
            inf => inf.clone(),
        };
        let add = |sum: &mut Int, inf: &mut [i64; 2], v: Val| match v {
            Val::Fin(x) => *sum = &*sum + &(&x * &Int::from(k)),
            Val::Neg => inf[0] += k,
            Val::Pos => inf[1] += k,
        };
        match b {
            Tb::Unset => unreachable!("a sum keeps a total only of terms with bounds"),
            Tb::NoDom => self.no_dom += k,
            Tb::NoVal => self.no_val += k,
            Tb::Of(l, h) => {
                let (l, h) = if f.is_negative() {
                    (times(h), times(l))
                } else {
                    (times(l), times(h))
                };
                add(&mut self.lo, &mut self.lo_inf, l);
                add(&mut self.hi, &mut self.hi_inf, h);
            }
        }
    }

    /// The sum of two totals.
    fn plus(&self, o: &Tot) -> Tot {
        let add = |[a, b]: [i64; 2], [c, d]: [i64; 2]| [a + c, b + d];
        Tot {
            lo: &self.lo + &o.lo,
            hi: &self.hi + &o.hi,
            lo_inf: add(self.lo_inf, o.lo_inf),
            hi_inf: add(self.hi_inf, o.hi_inf),
            no_val: self.no_val + o.no_val,
            no_dom: self.no_dom + o.no_dom,
        }
    }

    /// The total of the terms times the nonzero factor `w`.
    fn scaled(&self, w: &Int) -> Tot {
        let (lo, hi, lo_inf, hi_inf) = if w.is_negative() {
            let swap = |[n, p]: [i64; 2]| [p, n];
            (
                &self.hi * w,
                &self.lo * w,
                swap(self.hi_inf),
                swap(self.lo_inf),
            )
        } else {
            (&self.lo * w, &self.hi * w, self.lo_inf, self.hi_inf)
        };
        Tot {
            lo,
            hi,
            lo_inf,
            hi_inf,
            ..*self
        }
    }

    /// The bounds of the sum with the constant `c`, as [`Sep::bounds`] gives them; an infinity
    /// absorbs a value and the one that moves a bound outward wins, as in [`Val::plus`].
    fn bounds(&self, c: &Int) -> Option<Option<(Val, Val)>> {
        if self.no_val > 0 {
            return Some(None);
        }
        if self.no_dom > 0 {
            return None;
        }
        let lo = match self.lo_inf {
            [n, _] if n > 0 => Val::Neg,
            [_, p] if p > 0 => Val::Pos,
            _ => Val::Fin(c + &self.lo),
        };
        let hi = match self.hi_inf {
            [_, p] if p > 0 => Val::Pos,
            [n, _] if n > 0 => Val::Neg,
            _ => Val::Fin(c + &self.hi),
        };
        Some(Some((lo, hi)))
    }
}

impl Sep {
    /// The constant `c`.
    fn constant(c: Int) -> Sep {
        Sep {
            scale: Int::ONE,
            terms: imbl::OrdMap::new(),
            constant: c,
            tot: Some(Tot::ZERO),
        }
    }

    /// The term of `t` as it stands: its summary times the factors the sum took since.
    fn term(&self, (pa, at, _): &(Pa, Int, Tb)) -> Pa {
        if *at == self.scale {
            pa.clone()
        } else {
            pa.affine(self.scale.div_floor(at), 0)
        }
    }

    /// `w * self`. At 0 a line goes into the constant, at 0, and a [`Pa::Piecewise`] is kept at
    /// 0, since where it has no value the sum has none: `O(p)` for the `p` piecewise terms,
    /// which only an `if` of the term gives; their bounds are taken again when the sum is
    /// added to one formed over domains ([`Sep::add`]).
    fn scaled(&self, w: &Int) -> Sep {
        if w.is_zero() {
            let terms = self
                .terms
                .iter()
                .filter(|(_, (pa, _, _))| matches!(pa, Pa::Piecewise { .. }))
                .map(|(v, t)| (v.clone(), (self.term(t).affine(0, 0), Int::ONE, Tb::Unset)))
                .collect::<imbl::OrdMap<_, _>>();
            let tot = terms.is_empty().then_some(Tot::ZERO);
            return Sep {
                scale: Int::ONE,
                terms,
                constant: Int::ZERO,
                tot,
            };
        }
        Sep {
            scale: &self.scale * w,
            terms: self.terms.clone(),
            constant: &self.constant * w,
            tot: self.tot.as_ref().map(|t| t.scaled(w)),
        }
    }

    /// `self + pa`, for a `pa` over one input or none; the term's bounds taken over `dom`
    /// when the sum keeps them, and the sum's dropped without `dom`.
    fn add_pa(&mut self, pa: Pa, dom: Option<Dom<'_, '_>>) {
        let Some(v) = pa.var().cloned() else {
            if let Pa::Const(c) = pa {
                self.constant = &self.constant + &c;
            }
            return;
        };
        let old = self.terms.get(&v);
        let sum = match old {
            Some(t) => self
                .term(t)
                .plus(&pa, 1)
                .expect("two summaries of one input"),
            None => pa,
        };
        let b = match (dom, &mut self.tot) {
            (Some(dom), Some(tot)) => {
                if let Some((_, at, b)) = old {
                    tot.put(b, &self.scale.div_floor(at), -1);
                }
                let b = Tb::of(&sum, dom(&v));
                tot.put(&b, &Int::ONE, 1);
                b
            }
            _ => {
                self.tot = None;
                Tb::Unset
            }
        };
        self.terms.insert(v, (sum, self.scale.clone(), b));
    }

    /// Takes the bounds of every term over `dom` and their sum, `O(n log n)` for `n` inputs.
    fn take_bounds(&mut self, dom: Dom<'_, '_>) {
        let mut tot = Tot::ZERO;
        let terms = (self.terms.iter())
            .map(|(v, (pa, at, _))| {
                let b = Tb::of(pa, dom(v));
                tot.put(&b, &self.scale.div_floor(at), 1);
                (v.clone(), (pa.clone(), at.clone(), b))
            })
            .collect();
        self.terms = terms;
        self.tot = Some(tot);
    }

    /// `self + other`: the terms of the one with fewer put into the other, `O(m log n)` for
    /// `m <= n` inputs and the sums of the summaries of the inputs both read. Over `dom`, the
    /// sum keeps its terms' bounds, taken for the larger first when it has none, which only
    /// a sum not formed has (a `let`'s own term) or one of piecewise terms scaled by 0.
    fn add(self, other: Sep, dom: Option<Dom<'_, '_>>) -> Sep {
        let (mut big, small) = if self.terms.len() >= other.terms.len() {
            (self, other)
        } else {
            (other, self)
        };
        if let Some(dom) = dom
            && big.tot.is_none()
        {
            big.take_bounds(dom);
        }
        big.constant = &big.constant + &small.constant;
        for t in small.terms.values() {
            big.add_pa(small.term(t), dom);
        }
        big
    }

    /// The sum as one [`Pa`], when it reads one input or none.
    fn single(&self) -> Option<Pa> {
        let mut it = self.terms.values();
        match (it.next(), it.next()) {
            (None, _) => Some(Pa::Const(self.constant.clone())),
            (Some(t), None) => Some(self.term(t).affine(1, self.constant.clone())),
            _ => None,
        }
    }

    /// The least and the greatest value of the sum where each input lies in `dom` of it,
    /// `Some(None)` when it has no value there, and `None` when an input has no domain.
    /// Exact for lines over intervals; the bounds of a [`Pa::Piecewise`] may be wider
    /// ([`Tag::vals`]). `O(k)` for `k` inputs.
    fn bounds<'d>(
        &self,
        dom: impl Fn(&Arc<str>) -> Option<&'d IntervalSet>,
    ) -> Option<Option<(Val, Val)>> {
        let c = Val::Fin(self.constant.clone());
        let (mut lo, mut hi) = (c.clone(), c);
        for (v, t) in &self.terms {
            let Some((l, h)) = pa_bounds(&self.term(t), dom(v)?) else {
                return Some(None);
            };
            lo = lo.plus(&l, Val::Neg);
            hi = hi.plus(&h, Val::Pos);
        }
        Some(Some((lo, hi)))
    }

    /// What the input `v` over `ints`, in place of the domain the sum was formed over, adds
    /// to `tot`: its term's bounds there less those it keeps; nothing when `v` has no term or
    /// the sum keeps no total. `O(log k)` for `k` inputs.
    fn shift(&self, v: &Arc<str>, ints: &IntervalSet) -> Tot {
        let mut d = Tot::ZERO;
        if self.tot.is_some()
            && let Some(t) = self.terms.get(v)
        {
            d.put(&t.2, &self.scale.div_floor(&t.1), -1);
            d.put(&Tb::of(&self.term(t), Some(ints)), &Int::ONE, 1);
        }
        d
    }
}

/// The least and the greatest value of `pa` over `dom`, the domain of its input, or `None`
/// when it has no value there.
fn pa_bounds(pa: &Pa, dom: &IntervalSet) -> Option<(Val, Val)> {
    #[cfg(feature = "counts")]
    counts::TERM_BOUNDS.set(counts::TERM_BOUNDS.get() + 1);
    let (lo, hi) = dom.bounds()?;
    match pa {
        Pa::Const(c) => Some((Val::Fin(c.clone()), Val::Fin(c.clone()))),
        Pa::Linear { a, b, .. } => {
            let (u, v) = (value_at(lo, a, b), value_at(hi, a, b));
            Some(if u <= v { (u, v) } else { (v, u) })
        }
        Pa::Piecewise { root, .. } => {
            let root = if in_range(dom) {
                slice_treap(root.clone(), lo, hi)
            } else {
                root.clone()
            };
            root.map(|n| n.vals.clone())
        }
    }
}

/// The bounds of a sum of terms ([`Tx::invert_sep`]): the sums of the terms' finite least and
/// greatest values with the constant, and the numbers of infinite ones.
struct Sums {
    lo: Int,
    hi: Int,
    lo_inf: usize,
    hi_inf: usize,
}

impl Sums {
    /// Which terms of a sum of these bounds [`Tx::invert_read`] inverts for the demand `z`.
    /// A term of values `l..=h` keeps its input's domain when `l..=h` lies within one piece
    /// `[zl - (hi - h), zh - (lo - l)]` of what [`Tx::invert_term`] lets it take, an end
    /// infinite where the others' sum is or `z`'s is: for a term of finite bounds, when its
    /// width `h - l` is at most `min(hi - zl, zh - lo)` for some piece `zl..=zh` of `z`,
    /// the slack. A term with an infinite bound keeps it when the piece's end on that side
    /// is infinite too.
    fn wants(&self, z: &IntervalSet) -> Wants {
        let (lo, hi) = (Num::from(&self.lo), Num::from(&self.hi));
        let mut slack = NegInf;
        let (mut lo_only, mut hi_only, mut both) = (true, true, true);
        for (zl, zh) in z.pieces() {
            // The piece's ends are infinite for a term of an infinite bound on that side.
            let down = self.hi_inf > 0 || *zl == NegInf;
            let up = self.lo_inf > 0 || *zh == PosInf;
            let a = match zl {
                _ if down => PosInf,
                Fin(v) => Fin(&hi - v),
                _ => NegInf,
            };
            let b = match zh {
                _ if up => PosInf,
                Fin(v) => Fin(v - &lo),
                _ => NegInf,
            };
            slack = slack.max(a.min(b));
            // A term infinite below is one of the `lo_inf`, so the others' least sum is
            // infinite when `lo_inf >= 2`, and likewise above.
            lo_only &= !(down && (self.lo_inf >= 2 || *zh == PosInf));
            hi_only &= !(up && (self.hi_inf >= 2 || *zl == NegInf));
            both &= !((self.hi_inf >= 2 || *zl == NegInf) && (self.lo_inf >= 2 || *zh == PosInf));
        }
        Wants {
            slack,
            lo_only,
            hi_only,
            both,
        }
    }
}

/// Which terms [`Tx::invert_read`] inverts ([`Sums::wants`]): those of finite bounds wider
/// than `slack`, those of each kind of infinite bound when the flag of that kind is set, and
/// those it cannot tell ([`TermBounds::odd`]).
struct Wants {
    slack: End,
    lo_only: bool,
    hi_only: bool,
    both: bool,
}

impl Wants {
    /// Whether a term among those `b` sums is inverted: when `b` is one term's, whether that
    /// term is. It holds of a sum when it holds of one of its terms.
    fn takes(&self, b: &TermBounds) -> bool {
        b.odd > 0
            || (b.wide.as_ref()).is_some_and(|w| Fin(Num::from(w)) > self.slack)
            || (self.lo_only && b.lo_only > 0)
            || (self.hi_only && b.hi_only > 0)
            || (self.both && b.both > 0)
    }
}

/// The bounds of a summary's term of one input over its domain, or their sum over several
/// inputs ([`LetPa::term_bounds`]), kept in a tree of the inputs so that a test reads the
/// bounds of a summary of `k` inputs in `O(1)` and finds the terms it narrows in `O(log k)`
/// each ([`SummaryRead`]).
#[derive(Clone, Debug, PartialEq)]
pub struct TermBounds {
    /// The sum of the terms' finite least values.
    lo: Int,
    /// The sum of the terms' finite greatest values.
    hi: Int,
    /// The terms whose least value is infinite.
    lo_inf: usize,
    /// The terms whose greatest value is infinite.
    hi_inf: usize,
    /// The terms with no value, over an empty domain.
    no_val: usize,
    /// The inputs whose domain is empty.
    void: usize,
    /// The greatest width `h - l` of a term of finite bounds whose inversion keeps its
    /// domain when its values lie in one piece of the demand.
    wide: Option<Int>,
    /// The terms whose inversion may not keep its domain so: a line over an input whose
    /// domain has an end past `i128`, a summary with a gap, or bounds infinite the same way.
    odd: usize,
    /// The terms of values unbounded below and bounded above.
    lo_only: usize,
    /// The terms of values bounded below and unbounded above.
    hi_only: usize,
    /// The terms of values unbounded both ways.
    both: usize,
}

impl TermBounds {
    /// The bounds of no term.
    pub fn zero() -> TermBounds {
        TermBounds {
            lo: Int::ZERO,
            hi: Int::ZERO,
            lo_inf: 0,
            hi_inf: 0,
            no_val: 0,
            void: 0,
            wide: None,
            odd: 0,
            lo_only: 0,
            hi_only: 0,
            both: 0,
        }
    }

    /// The bounds of the terms of `self` and of `o`.
    pub fn plus(&self, o: &TermBounds) -> TermBounds {
        TermBounds {
            lo: &self.lo + &o.lo,
            hi: &self.hi + &o.hi,
            lo_inf: self.lo_inf + o.lo_inf,
            hi_inf: self.hi_inf + o.hi_inf,
            no_val: self.no_val + o.no_val,
            void: self.void + o.void,
            wide: match (&self.wide, &o.wide) {
                (Some(a), Some(b)) => Some(a.max(b).clone()),
                (w, None) | (None, w) => w.clone(),
            },
            odd: self.odd + o.odd,
            lo_only: self.lo_only + o.lo_only,
            hi_only: self.hi_only + o.hi_only,
            both: self.both + o.both,
        }
    }
}

/// The inputs of a summary of [`Lets`] as a test reads them ([`LetIn::read`]): each one's
/// domain, and the bounds of the summary's terms over them kept in a tree with the sum of each
/// subtree's, so that a test costs the inputs it narrows and not all of them
/// (`images::TermRead`).
pub trait SummaryRead: fmt::Debug {
    /// The inputs.
    fn vars(&self) -> &imbl::OrdSet<Arc<str>>;
    /// The domain of the input `v`, `None` when it is not one.
    fn ints(&self, v: &str) -> Option<&IntervalSet>;
    /// The domain of `v` in the scope the read was made in, `None` when the scope has no `v`:
    /// that of [`SummaryRead::ints`] for an input. The reads of one transfer are made in one
    /// scope ([`let_narrowing`]).
    fn scope_ints(&self, v: &str) -> Option<&IntervalSet>;
    /// The sum of the bounds of every term ([`LetPa::term_bounds`]).
    fn total(&self) -> TermBounds;
    /// Calls `f` on the inputs in order, skipping each subtree whose sum `want` refuses,
    /// until `f` gives `false`.
    fn visit(&self, want: &dyn Fn(&TermBounds) -> bool, f: &mut dyn FnMut(&Arc<str>) -> bool);
}

/// The piecewise-affine summary of the value a `let` binds, over the inputs it reads (`Sep`),
/// kept as the sum `Σ c_i * s_i + rest` of the summaries `s_i` of the bound names it adds and
/// the summary of the rest of its term ([`let_summary`]). Each binding is summarized once, in
/// its own term's size, when it is bound, and the sum is formed when a test reads the name
/// (`LetPa::force`), so that a block of bindings each adding the one before
/// (`x_k = x_(k-1) + y_k`) costs no more than the summaries a test reads.
///
/// The summaries form a graph without cycles: a binding's parts were bound before it. Two
/// summaries are equal when they are one binding's.
#[derive(Clone)]
pub struct LetPa(Arc<LetNode>);

struct LetNode {
    /// A number no other summary has, for the visited set of [`LetPa::sum`].
    id: u64,
    /// The inputs the summary reads, a persistent set shared with the parts' sets.
    vars: imbl::OrdSet<Arc<str>>,
    parts: Vec<(Int, LetPa)>,
    rest: Sep,
    /// The sum, once a test has read it.
    forced: OnceLock<Sep>,
}

static LET_IDS: AtomicU64 = AtomicU64::new(0);

impl LetPa {
    /// The summary of `parts` and `rest`: its inputs are those of the part that reads the most,
    /// with the others' put in, `O(m log n)` for the `m` inputs of the others.
    fn new(parts: Vec<(Int, LetPa)>, rest: Sep) -> LetPa {
        let widest = parts.iter().max_by_key(|(_, p)| p.0.vars.len());
        let mut vars = widest.map_or_else(imbl::OrdSet::new, |(_, p)| p.0.vars.clone());
        for (_, p) in &parts {
            if widest.is_some_and(|(_, w)| w == p) {
                continue;
            }
            vars.extend(p.0.vars.iter().cloned());
        }
        vars.extend(rest.terms.keys().cloned());
        LetPa(Arc::new(LetNode {
            id: LET_IDS.fetch_add(1, Ordering::Relaxed),
            vars,
            parts,
            rest,
            forced: OnceLock::new(),
        }))
    }

    /// The bounds of the summary's term of the input `v` over `ints` ([`TermBounds`]), with
    /// whether `ints` is empty: the leaf of `v` in the tree a test reads the summary's inputs
    /// through ([`SummaryRead`]). Forms the summary (`LetPa::formed`) the first time.
    pub fn term_bounds(&self, v: &str, ints: &IntervalSet) -> TermBounds {
        let mut b = TermBounds::zero();
        b.void = usize::from(ints.is_empty());
        let sep = self.formed();
        let Some(t) = sep.terms.get(v) else {
            return b;
        };
        let pa = sep.term(t);
        let Some((l, h)) = pa_bounds(&pa, ints) else {
            b.no_val = 1;
            return b;
        };
        match &l {
            Val::Fin(x) => b.lo = x.clone(),
            _ => b.lo_inf = 1,
        }
        match &h {
            Val::Fin(x) => b.hi = x.clone(),
            _ => b.hi_inf = 1,
        }
        // Whether inverting the term keeps every input whose value lies in the demand: a
        // line over a domain whose ends `Pa::to_treap` takes, or pieces covering the domain's
        // hull with no gap.
        let whole = match &pa {
            Pa::Const(_) => true,
            Pa::Linear { .. } => in_range(ints),
            Pa::Piecewise { root, .. } => root.as_ref().is_some_and(|n| {
                n.dense
                    && (ints.bounds()).is_some_and(|(lo, hi)| n.span.0 <= *lo && *hi <= n.span.1)
            }),
        };
        match (whole, &l, &h) {
            (true, Val::Fin(x), Val::Fin(y)) => b.wide = Some(y - x),
            (true, Val::Neg, Val::Fin(_)) => b.lo_only = 1,
            (true, Val::Fin(_), Val::Pos) => b.hi_only = 1,
            (true, Val::Neg, Val::Pos) => b.both = 1,
            _ => b.odd = 1,
        }
        b
    }

    /// The inputs the summary reads.
    pub fn vars(&self) -> &imbl::OrdSet<Arc<str>> {
        &self.0.vars
    }

    /// The summary formed ([`LetPa::sum`]) the first time it is read, and kept.
    fn formed(&self) -> &Sep {
        self.0.forced.get_or_init(|| self.sum(None))
    }

    /// The summary as one [`Pa`], when it reads one input or none ([`LetPa::formed`]).
    fn force(&self) -> Option<Pa> {
        self.formed().single()
    }

    /// Forms the summary now (`LetPa::sum`). A caller that makes the summaries of a block of
    /// bindings children first and forms each as it is made adds to each the formed sums of
    /// its parts, `O(1)` merges a binding, so that the names are then read in any order at
    /// no cost but their own.
    ///
    /// Formed over `dom`, the domains of its inputs, the sum keeps the bounds of each term over
    /// its input's domain and their total, each taken as its term is put in, so that the
    /// bounds of the value cost the inputs read over other domains ([`LetPa::image_shifted`]).
    /// A summary formed before keeps the sum it has.
    pub fn form<'d>(&self, dom: impl Fn(&Arc<str>) -> Option<&'d IntervalSet>) {
        self.0.forced.get_or_init(|| self.sum(Some(&dom)));
    }

    /// Bounds on the value where each input `v` lies in `ints(v)`, as one interval; the empty
    /// set where it has no value; `None` when an input has no integers given. `O(k)` for `k`
    /// inputs, the summary formed (`LetPa::formed`).
    pub fn image<'d>(
        &self,
        ints: impl Fn(&Arc<str>) -> Option<&'d IntervalSet>,
    ) -> Option<IntervalSet> {
        let end = |v: Val| match v {
            Val::Neg => NegInf,
            Val::Fin(x) => Fin(Num::from(&x)),
            Val::Pos => PosInf,
        };
        Some(match self.formed().bounds(ints)? {
            Some((lo, hi)) => IntervalSet::range(end(lo), end(hi)),
            None => IntervalSet::empty(),
        })
    }

    /// What the input `v` read over `ints`, and not over the domain the summary was formed
    /// over ([`LetPa::form`]), adds to the bounds of its value: nothing when it has no term or
    /// the summary was not formed over domains. `O(log k)` for `k` inputs.
    pub fn shift(&self, v: &Arc<str>, ints: &IntervalSet) -> Shift {
        Shift(self.formed().shift(v, ints))
    }

    /// [`LetPa::image`] with the inputs whose shifts `s` sums ([`LetPa::shift`]) over the
    /// integers they were taken at and every other over the domain the summary was formed
    /// over: `None` when it was not formed over domains or an input has none. `O(1)` whatever
    /// the number of inputs, so a caller that keeps the sum of the inputs' shifts in a tree,
    /// and changes it where an input changes, pays for those inputs alone (item
    /// PA-let-narrow-many).
    pub fn image_shifted(&self, s: &Shift) -> Option<IntervalSet> {
        let end = |v: Val| match v {
            Val::Neg => NegInf,
            Val::Fin(x) => Fin(Num::from(&x)),
            Val::Pos => PosInf,
        };
        let formed = self.formed();
        Some(
            match formed.tot.as_ref()?.plus(&s.0).bounds(&formed.constant)? {
                Some((lo, hi)) => IntervalSet::range(end(lo), end(hi)),
                None => IntervalSet::empty(),
            },
        )
    }

    /// The inputs whose shift may differ from that of the same input in `base`
    /// ([`LetPa::shift`]), each once or more, and those one of the two reads and the other
    /// does not: `None` when either was not formed over domains or one was scaled since the
    /// terms they share were put in, so that every shift may differ. Found from the
    /// differences of the persistent maps, which skip the parts the two share: a summary
    /// formed from `base` and a few more terms costs those terms (`O(m log k)`).
    pub fn changed_since<'a>(
        &'a self,
        base: &'a LetPa,
    ) -> Option<impl Iterator<Item = &'a Arc<str>> + 'a> {
        let (now, then) = (self.formed(), base.formed());
        if now.tot.is_none() || then.tot.is_none() || now.scale != then.scale {
            return None;
        }
        let vars = (base.0.vars.diff(&self.0.vars)).map(|d| match d {
            imbl::ordset::DiffItem::Add(v) | imbl::ordset::DiffItem::Remove(v) => v,
        });
        let terms = (then.terms.diff(&now.terms)).map(|d| match d {
            imbl::ordmap::DiffItem::Add(v, _) | imbl::ordmap::DiffItem::Remove(v, _) => v,
            imbl::ordmap::DiffItem::Update { new: (v, _), .. } => v,
        });
        Some(vars.chain(terms))
    }

    /// The summary's parts summed. Each node of the graph below it gets the sum of the
    /// coefficients of its paths from this one, in topological order (a node after every node
    /// that adds it), and the sum adds each node's rest times its coefficient: so a node shared
    /// by many paths is added once. A node already formed by an earlier test is added as its
    /// sum and not entered. A rest whose coefficient comes to 0 is still added, at 0, since
    /// where it has no value the sum has none.
    ///
    /// Cost: the nodes and edges reached, and one [`Sep::add`] per node, which puts the terms
    /// of the smaller sum into the larger and adds the summaries of an input both read by
    /// [`Pa::plus`], each `O(m log(n / m + 1))` for `m` pieces added to `n` ([`add_treaps`]):
    /// `O(d log d)` for a chain of `d` bindings that each add a summary of one test.
    ///
    /// Complexity tradeoff: a test reading the name forms its whole summary, as many pieces as
    /// it has, so a block of `d` bindings `x_k = x_(k-1) + y_k`, `y_k = y_(k-1) + ramp_k`, with
    /// a test of every `x_k`, forms `d` summaries of up to `d + 1` pieces, `Θ(d²)`. The cost is
    /// the size of these summaries, not work done again: `x_k` has `k + 1` pieces (measured at
    /// `d` = 32, 64, 128, 256: `x_1` 2, `x_(d/2)` `d/2 + 1`, `x_d` `d + 1`, all `x_k` together
    /// 561, 2,145, 8,385, 33,153 pieces, formed in 2.7, 15, 55, 245 ms), and no two of them
    /// can share a piece, since `y_k` is not 0 on any piece of `x_(k-1)` with `n > 0`, so every
    /// piece of `x_k` there has a slope or offset that `x_(k-1)` lacks. Why: each summary is
    /// inverted piece by piece ([`invert_treap`]), and the sum of two summaries of `k` pieces
    /// each is a summary of `O(k)` pieces that shares no node with either. Trigger:
    /// tests of many names of a chain of sums of piecewise summaries. Test:
    /// `l01_39_reduced_product::follow::a_block_of_sums_of_ramps_scales`. COMPLEXITY.md row
    /// PA-let-block. A complete solution would invert a sum without forming it, from bounds of
    /// the parts on each range of the input.
    ///
    /// Over `dom` the sum keeps its terms' bounds ([`LetPa::form`]), each taken as its term is
    /// put in by [`Sep::add`], at no cost but the terms added.
    fn sum(&self, dom: Option<Dom<'_, '_>>) -> Sep {
        // Postorder of the graph, on an explicit stack: a node is entered once (`entered`)
        // and listed after every node it adds.
        let mut order: Vec<&LetNode> = Vec::new();
        let mut entered: HashSet<u64> = HashSet::new();
        let mut stack: Vec<(&LetNode, bool)> = vec![(&*self.0, false)];
        while let Some((n, done)) = stack.pop() {
            if done {
                order.push(n);
                continue;
            }
            if !entered.insert(n.id) {
                continue;
            }
            #[cfg(feature = "counts")]
            counts::SUM_NODES.set(counts::SUM_NODES.get() + 1);
            stack.push((n, true));
            if n.id == self.0.id || n.forced.get().is_none() {
                for (_, p) in &n.parts {
                    if !entered.contains(&p.0.id) {
                        stack.push((&*p.0, false));
                    }
                }
            }
        }
        let mut weight: HashMap<u64, Int> = HashMap::from([(self.0.id, Int::ONE)]);
        let mut sum = Sep::constant(Int::ZERO);
        for n in order.into_iter().rev() {
            let w = weight.remove(&n.id).unwrap_or(Int::ZERO);
            if n.id != self.0.id
                && let Some(formed) = n.forced.get()
            {
                sum = sum.add(formed.scaled(&w), dom);
                continue;
            }
            sum = sum.add(n.rest.scaled(&w), dom);
            for (c, p) in &n.parts {
                let e = weight.entry(p.0.id).or_insert(Int::ZERO);
                *e = &*e + &(&w * c);
            }
        }
        sum
    }
}

/// Work counted on a thread (feature `counts`), measures the load does not change: the nodes
/// `LetPa::sum` enters (PA-let-narrow), its own and those it reads but not those below a node
/// already formed, the bounds of terms of sums taken (PA-let-multi), and the inputs given a
/// test's transfer (PA-letpre-linear), and the bindings read through their terms
/// (PA-let-unsummarized-narrow). A test holds each
/// count of a block of bindings to linear growth.
#[cfg(feature = "counts")]
pub mod counts {
    use std::cell::Cell;

    thread_local! {
        pub(crate) static SUM_NODES: Cell<u64> = const { Cell::new(0) };
        pub(crate) static TERM_BOUNDS: Cell<u64> = const { Cell::new(0) };
        pub(crate) static IMAGE_SETS: Cell<u64> = const { Cell::new(0) };
        pub(crate) static INPUTS: Cell<u64> = const { Cell::new(0) };
        pub(crate) static TERM_READS: Cell<u64> = const { Cell::new(0) };
        pub(crate) static EVALUATIONS: Cell<u64> = const { Cell::new(0) };
    }

    /// The nodes `LetPa::sum` has entered on this thread since it started.
    pub fn sum_nodes() -> u64 {
        SUM_NODES.get()
    }

    /// The bounds of a term of a sum over a domain taken on this thread since it started
    /// (`pa_bounds`, item PA-let-multi): a summary read with none of its inputs narrowed
    /// takes none, where reading it took one for each of its inputs.
    pub fn term_bounds() -> u64 {
        TERM_BOUNDS.get()
    }

    /// The leaves set in the trees of what summaries read (`images`, items PA-let-narrow-many
    /// and PA-walk-multi) on this thread since it started: a read from the last read of the
    /// same or a wider summary sets the inputs changed since, where a read made afresh sets
    /// every input.
    pub fn image_sets() -> u64 {
        IMAGE_SETS.get()
    }

    /// The inputs given the transfers of tests through summaries (`let_narrowing`) on this
    /// thread since it started (item PA-letpre-linear): a test of a summary over one input
    /// is given that input, not the names in scope.
    pub fn inputs() -> u64 {
        INPUTS.get()
    }

    /// The bindings with no summary read backward through their terms after a test narrowed
    /// them (`Scope::through_terms`, item PA-let-unsummarized-narrow) on this thread since it
    /// started: each once a test, and only those whose integers the test changed.
    pub fn term_reads() -> u64 {
        TERM_READS.get()
    }

    /// The written constraints evaluated at one member of a listed name (`Scope::enumerate_on`)
    /// on this thread since it started: a constraint on a name whose members are the integer
    /// roots of an obligation's equation is evaluated once at each root (ROOTS-listed).
    pub fn evaluations() -> u64 {
        EVALUATIONS.get()
    }
}

/// Dropped on an explicit stack: a chain of `d` bindings is a chain of `d` nodes.
impl Drop for LetNode {
    fn drop(&mut self) {
        let mut stack: Vec<LetPa> = std::mem::take(&mut self.parts)
            .into_iter()
            .map(|(_, p)| p)
            .collect();
        while let Some(p) = stack.pop() {
            if let Ok(mut n) = Arc::try_unwrap(p.0) {
                stack.extend(std::mem::take(&mut n.parts).into_iter().map(|(_, p)| p));
            }
        }
    }
}

impl PartialEq for LetPa {
    fn eq(&self, other: &LetPa) -> bool {
        self.0.id == other.0.id
    }
}

impl fmt::Debug for LetPa {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LetPa({:?}, {} parts)", self.0.vars, self.0.parts.len())
    }
}

/// The summaries ([`Pa`]) of one term in each of the `n` classes of remainders of a split
/// ([`Walk::by_class`]), as a persistent tree over the class numbers `0..n`: a node covers a
/// range of classes, halved at its middle, and either holds one summary for all of them or
/// splits into two halves with an affine map still to be applied to both. A change of every
/// summary by an affine map and a reading of one class take `O(log n)`, and taking a range
/// of classes from another such tree `O(log n)` new nodes.
///
/// A leaf may stand for the tree's `base`, one summary for every class, mapped by the maps
/// on its path ([`Leaf::Base`]); a constant added to every class is kept in `shift`, outside
/// the tree. When every leaf is the base and every map only adds (`adds`), the summary in
/// class `i` is `base + d_i` for a constant `d_i`, so that an `if` on a test that reads no
/// remainder, whose arms add constants to one such tree, is the same tree over a new base
/// ([`Walk::by_class_if`]).
#[derive(Clone)]
struct ByClass {
    root: Rc<Cls>,
    n: usize,
    /// The input the summaries read, if any.
    var: Option<Arc<str>>,
    bound: Bound,
    /// The summary the leaves [`Leaf::Base`] stand for.
    base: Option<Pa>,
    /// Added to the summary of every class, after the tree's maps.
    shift: i128,
    /// Whether every leaf is [`Leaf::Base`] and every map in the tree has multiplier 1.
    adds: bool,
}

enum Cls {
    Same(Leaf),
    Split {
        left: Rc<Cls>,
        right: Rc<Cls>,
        tag: (i128, i128),
    },
}

/// The summary a leaf of a [`ByClass`] holds for its classes.
enum Leaf {
    /// This summary.
    Own(Pa),
    /// The tree's base, mapped by `(mul, add)`.
    Base((i128, i128)),
}

/// Bounds over every class on the magnitudes of the summaries' leaves, `a * var + b` with
/// `|var| <= x`, after the affine maps whose multipliers multiply to at most `mul`. While
/// the values `a * x + b` and the maps lie in `i64`, no step in any class leaves `i64`, so
/// that each class's summary is the one its own run computes ([`Walk::pa`]).
#[derive(Clone, Copy)]
struct Bound {
    a: u128,
    b: u128,
    x: u128,
    mul: u128,
}

impl Bound {
    fn holds(self) -> bool {
        let limit = i64::MAX as u128;
        let vals = self.a.saturating_mul(self.x).saturating_add(self.b);
        vals <= limit && self.mul <= limit
    }

    fn max(self, o: Bound) -> Bound {
        Bound {
            a: self.a.max(o.a),
            b: self.b.max(o.b),
            x: self.x.max(o.x),
            mul: self.mul.max(o.mul),
        }
    }

    /// A bound on the values of `pa`, whose input lies within `x` in magnitude.
    fn of(pa: &Pa, x: u128) -> Bound {
        // A magnitude past `i128`, and an infinity, as `u128::MAX`, which no bound holds.
        let mag = |v: &Int| v.to_i128().map_or(u128::MAX, i128::unsigned_abs);
        let val = |v: &Val| match v {
            Val::Fin(x) => mag(x),
            _ => u128::MAX,
        };
        let (a, b) = match pa {
            Pa::Const(c) => (0, mag(c)),
            Pa::Linear { a, b, .. } => (mag(a), mag(b)),
            Pa::Piecewise { root: None, .. } => (0, 0),
            Pa::Piecewise { root: Some(r), .. } => (0, val(&r.vals.0).max(val(&r.vals.1))),
        };
        Bound { a, b, x, mul: 1 }
    }
}

impl ByClass {
    fn same(pa: Pa, var: Option<Arc<str>>, bound: Bound, n: usize) -> Option<ByClass> {
        bound.holds().then(|| ByClass {
            root: Rc::new(Cls::Same(Leaf::Own(pa))),
            n,
            var,
            bound,
            base: None,
            shift: 0,
            adds: false,
        })
    }

    /// `pa`, which is the same in every class, as the base of every leaf.
    fn based(pa: Pa, var: Option<Arc<str>>, bound: Bound, n: usize) -> Option<ByClass> {
        bound.holds().then(|| ByClass {
            root: Rc::new(Cls::Same(Leaf::Base((1, 0)))),
            n,
            var,
            bound,
            base: Some(pa),
            shift: 0,
            adds: true,
        })
    }

    fn constant(c: i64, n: usize) -> Option<ByClass> {
        let bound = Bound {
            a: 0,
            b: c.unsigned_abs().into(),
            x: 0,
            mul: 1,
        };
        ByClass::same(Pa::Const(c.into()), None, bound, n)
    }

    /// `mul * self + add` in every class.
    fn affine(&self, (mul, add): (i128, i128)) -> Option<ByClass> {
        let m = mul.unsigned_abs();
        let bound = Bound {
            a: self.bound.a.saturating_mul(m),
            b: (self.bound.b.saturating_mul(m)).saturating_add(add.unsigned_abs()),
            x: self.bound.x,
            mul: self.bound.mul.saturating_mul(m),
        };
        if !bound.holds() {
            return None;
        }
        let mut out = self.clone();
        out.bound = bound;
        if mul == 1 {
            // The tree is kept, so that `t` and `t + c` share it ([`Tx::by_class_if`]).
            out.shift = self.shift.checked_add(add)?;
        } else {
            let f = compose((1, self.shift), (mul, add))?;
            out.root = cls_affine(&self.root, f)?;
            out.shift = 0;
            out.adds = false;
        }
        Some(out)
    }

    /// The tree with `shift` applied to its root.
    fn shifted(&self) -> Option<Rc<Cls>> {
        cls_affine(&self.root, (1, self.shift))
    }

    /// The summary of every class when it is one summary, its leaf made its own.
    fn uniform(&self) -> Option<Pa> {
        match &*self.root {
            Cls::Same(_) => self.get(0),
            Cls::Split { .. } => None,
        }
    }

    /// `yes` in the classes of the ranges `i..=j` of `ranges`, and `no` in the others.
    fn choose(yes: &ByClass, no: &ByClass, ranges: &[(usize, usize)]) -> Option<ByClass> {
        let var = match (&yes.var, &no.var) {
            (Some(u), Some(v)) if u != v => return None,
            (Some(v), _) | (_, Some(v)) => Some(v.clone()),
            (None, None) => None,
        };
        // Two bases are one tree's only when they are the same; an arm that is one summary
        // in every class holds it as its own.
        let own = |c: &ByClass| -> Option<ByClass> {
            let pa = c.uniform()?;
            ByClass::same(pa, c.var.clone(), c.bound, c.n)
        };
        let (yes, no) = match (&yes.base, &no.base) {
            (Some(u), Some(v)) if !same_pa(u, v) => match (own(yes), own(no)) {
                (Some(y), _) => (y, no.clone()),
                (None, Some(n)) => (yes.clone(), n),
                (None, None) => return None,
            },
            _ => (yes.clone(), no.clone()),
        };
        let mut root = no.shifted()?;
        let taken = yes.shifted()?;
        for &(i, j) in ranges {
            root = cls_splice(&taken, &root, (0, no.n), (i, j + 1))?;
        }
        Some(ByClass {
            root,
            n: no.n,
            var,
            bound: yes.bound.max(no.bound),
            base: yes.base.or(no.base),
            shift: 0,
            adds: yes.adds && no.adds,
        })
    }

    /// `min(self, c)`, or `max` where not `min`, in every class ([`Pa::clamp`]), each leaf
    /// clamped once for the classes it covers: `O(L (m + 1) log P)` for `L` leaves, at most
    /// the `G` classes, and `m` crossings of `c` among `P` pieces. With `on`, only the leaves
    /// that meet those ranges of classes are clamped, and each node that meets none is one
    /// placeholder leaf ([`Walk::by_class_on`]): `O((r + L_r) log n)` for `r` ranges and the
    /// `L_r` leaves that meet them.
    ///
    /// Complexity tradeoff: each leaf is clamped by itself, not the tree's base once, so the
    /// classes share no step here, `O(L)` clamps for a tree of `L` leaves, at most `G`. Why: a
    /// leaf is the base under its own affine map, and a clamp does not commute with a map
    /// that is not the identity, so the leaves' clamps differ. Trigger: `min` or `max` with a
    /// constant of a term whose values lie on both sides of it, below an `if` on the split's
    /// remainder. Test: `store::preimage::tests::a_chain_with_clamps_is_read_in_time_near_its_length`.
    /// COMPLEXITY.md rows S22e-quad and S22-order-chain. A complete solution is the one named
    /// at [`Walk::by_class`]: the congruence facet in the transfer's sets.
    fn clamp(
        &self,
        min: bool,
        c: i64,
        dom: &IntervalSet,
        on: Option<&[(usize, usize)]>,
    ) -> Option<ByClass> {
        let at = (self.base.as_ref(), (0, self.n), on);
        let root = cls_clamp(&self.root, (1, self.shift), at, min, c, dom)?;
        let bound = Bound {
            b: self.bound.b.max(c.unsigned_abs().into()),
            ..self.bound
        };
        bound.holds().then(|| ByClass {
            root,
            n: self.n,
            var: self.var.clone(),
            bound,
            base: None,
            shift: 0,
            adds: false,
        })
    }

    /// Each range `lo..hi` of classes that the tree holds one summary for, with that summary,
    /// in the order of the classes: `O(L)` maps for a tree of `L` leaves.
    fn leaves(&self) -> Option<Vec<((usize, usize), Pa)>> {
        let mut out = Vec::new();
        // Each node with the maps above it, the deepest first, as one map.
        let mut todo = vec![(&self.root, (0, self.n), (1, self.shift))];
        while let Some((node, (lo, hi), f)) = todo.pop() {
            match &**node {
                Cls::Same(Leaf::Own(pa)) => out.push(((lo, hi), pa.affine(f.0, f.1))),
                Cls::Same(Leaf::Base(g)) => {
                    let f = compose(*g, f)?;
                    out.push(((lo, hi), self.base.as_ref()?.affine(f.0, f.1)));
                }
                Cls::Split { left, right, tag } => {
                    let f = compose(*tag, f)?;
                    let mid = lo + (hi - lo) / 2;
                    todo.push((right, (mid, hi), f));
                    todo.push((left, (lo, mid), f));
                }
            }
        }
        Some(out)
    }

    /// The summary in class `index`.
    fn get(&self, index: usize) -> Option<Pa> {
        let (mut node, (mut lo, mut hi)) = (&self.root, (0, self.n));
        let mut tags = Vec::new();
        let leaf = loop {
            match &**node {
                Cls::Same(leaf) => break leaf,
                Cls::Split { left, right, tag } => {
                    tags.push(*tag);
                    let mid = lo + (hi - lo) / 2;
                    (node, lo, hi) = if index < mid {
                        (left, lo, mid)
                    } else {
                        (right, mid, hi)
                    };
                }
            }
        };
        // The deepest map applies first.
        let mut f = (1, 0);
        for &tag in tags.iter().rev() {
            f = compose(f, tag)?;
        }
        f = compose(f, (1, self.shift))?;
        match leaf {
            Leaf::Own(pa) => Some(pa.affine(f.0, f.1)),
            Leaf::Base(g) => {
                let f = compose(*g, f)?;
                Some(self.base.as_ref()?.affine(f.0, f.1))
            }
        }
    }
}

/// The summary a leaf holds, `base` standing for [`Leaf::Base`].
fn leaf_pa(leaf: &Leaf, base: Option<&Pa>) -> Option<Pa> {
    match leaf {
        Leaf::Own(pa) => Some(pa.clone()),
        Leaf::Base((mul, add)) => Some(base?.affine(*mul, *add)),
    }
}

/// A range of classes [`cls_zip`] finds, with the summaries of its two trees there, or with
/// none when the range meets none of the ranges read.
type Zipped = ((usize, usize), Option<(Pa, Pa)>);

/// Appends to `out`, in the order of the classes, each range of classes `span` in which both
/// `a` and `b`, trees over `span` with no map above them, are one summary, with those two
/// summaries; `bases` are the summaries of their [`Leaf::Base`] leaves. A range is a node of
/// either tree, so there are at most as many as the two trees have leaves together. With
/// `on`, a range that meets none of those ranges comes without summaries, as one node of the
/// halving ([`Walk::by_class_on`]).
fn cls_zip(
    a: &Rc<Cls>,
    b: &Rc<Cls>,
    bases: (Option<&Pa>, Option<&Pa>),
    (lo, hi): (usize, usize),
    on: Option<&[(usize, usize)]>,
    out: &mut Vec<Zipped>,
) -> Option<()> {
    if on.is_some_and(|r| !ranges_meet(r, (lo, hi))) {
        out.push(((lo, hi), None));
        return Some(());
    }
    if let (Cls::Same(u), Cls::Same(v)) = (&**a, &**b) {
        out.push(((lo, hi), Some((leaf_pa(u, bases.0)?, leaf_pa(v, bases.1)?))));
        return Some(());
    }
    let mid = lo + (hi - lo) / 2;
    let (al, ar) = cls_halves(a)?;
    let (bl, br) = cls_halves(b)?;
    cls_zip(&al, &bl, bases, (lo, mid), on, out)?;
    cls_zip(&ar, &br, bases, (mid, hi), on, out)
}

/// The tree over the classes `span` whose leaves are `leaves`, in order, each a range of
/// classes that is a node of the halving of `span` ([`cls_zip`]).
fn cls_build(
    leaves: &mut std::iter::Peekable<impl Iterator<Item = ((usize, usize), Pa)>>,
    (lo, hi): (usize, usize),
) -> Rc<Cls> {
    if let Some((_, pa)) = leaves.next_if(|(span, _)| *span == (lo, hi)) {
        return Rc::new(Cls::Same(Leaf::Own(pa)));
    }
    let mid = lo + (hi - lo) / 2;
    Rc::new(Cls::Split {
        left: cls_build(leaves, (lo, mid)),
        right: cls_build(leaves, (mid, hi)),
        tag: (1, 0),
    })
}

/// Where [`cls_clamp`] works: the summary of the leaves [`Leaf::Base`], the range of classes
/// of the node, and the ranges of classes read, if not all.
type ClampAt<'a> = (Option<&'a Pa>, (usize, usize), Option<&'a [(usize, usize)]>);

/// The tree `node` over the classes `span` with the map `f` applied above it and every leaf's
/// summary clamped ([`ByClass::clamp`]); `base` is the summary of the leaves [`Leaf::Base`].
/// With `on`, a node that meets none of those ranges is a placeholder ([`Walk::by_class_on`]).
fn cls_clamp(
    node: &Rc<Cls>,
    f: (i128, i128),
    (base, (lo, hi), on): ClampAt<'_>,
    min: bool,
    c: i64,
    dom: &IntervalSet,
) -> Option<Rc<Cls>> {
    if on.is_some_and(|r| !ranges_meet(r, (lo, hi))) {
        return Some(cls_unread());
    }
    let mid = lo + (hi - lo) / 2;
    Some(Rc::new(match &**node {
        Cls::Same(leaf) => {
            let pa = match leaf {
                Leaf::Own(pa) => pa.affine(f.0, f.1),
                Leaf::Base(g) => {
                    let g = compose(*g, f)?;
                    base?.affine(g.0, g.1)
                }
            };
            Cls::Same(Leaf::Own(pa.clamp(min, c, dom)?))
        }
        Cls::Split { left, right, tag } => {
            let f = compose(*tag, f)?;
            Cls::Split {
                left: cls_clamp(left, f, (base, (lo, mid), on), min, c, dom)?,
                right: cls_clamp(right, f, (base, (mid, hi), on), min, c, dom)?,
                tag: (1, 0),
            }
        }
    }))
}

/// The leaf that stands for classes no case reads ([`Walk::by_class_on`]).
fn cls_unread() -> Rc<Cls> {
    Rc::new(Cls::Same(Leaf::Own(Pa::Const(Int::ZERO))))
}

/// Whether one of `ranges`, ranges `i..=j` of class numbers, sorted and disjoint, meets the
/// classes `lo..hi`: `O(log r)` for `r` ranges.
fn ranges_meet(ranges: &[(usize, usize)], (lo, hi): (usize, usize)) -> bool {
    let k = ranges.partition_point(|&(_, j)| j < lo);
    ranges.get(k).is_some_and(|&(i, _)| i < hi)
}

/// The classes `0..n` outside `ranges`, ranges `i..=j` sorted and disjoint, in the same form.
fn ranges_complement(ranges: &[(usize, usize)], n: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::with_capacity(ranges.len() + 1);
    let mut next = 0;
    for &(i, j) in ranges {
        if next < i {
            out.push((next, i - 1));
        }
        next = j + 1;
    }
    if next < n {
        out.push((next, n - 1));
    }
    out
}

/// Whether `u` and `v` are one summary: equal coefficients, or one shared treap.
fn same_pa(u: &Pa, v: &Pa) -> bool {
    match (u, v) {
        (Pa::Const(a), Pa::Const(b)) => a == b,
        (Pa::Linear { var, a, b }, Pa::Linear { var: w, a: c, b: d }) => {
            var == w && a == c && b == d
        }
        (Pa::Piecewise { var, root }, Pa::Piecewise { var: w, root: r }) => {
            var == w
                && match (root, r) {
                    (Some(x), Some(y)) => Arc::ptr_eq(x, y),
                    (None, None) => true,
                    _ => false,
                }
        }
        _ => false,
    }
}

/// `node` mapped by `f`, in `O(1)`.
fn cls_affine(node: &Rc<Cls>, f: (i128, i128)) -> Option<Rc<Cls>> {
    if f == (1, 0) {
        return Some(node.clone());
    }
    Some(Rc::new(match &**node {
        Cls::Same(Leaf::Own(pa)) => Cls::Same(Leaf::Own(pa.affine(f.0, f.1))),
        Cls::Same(Leaf::Base(g)) => Cls::Same(Leaf::Base(compose(*g, f)?)),
        Cls::Split { left, right, tag } => Cls::Split {
            left: left.clone(),
            right: right.clone(),
            tag: compose(*tag, f)?,
        },
    }))
}

/// The two halves of `node`, with its map applied.
fn cls_halves(node: &Rc<Cls>) -> Option<(Rc<Cls>, Rc<Cls>)> {
    match &**node {
        Cls::Same(_) => Some((node.clone(), node.clone())),
        Cls::Split { left, right, tag } => {
            Some((cls_affine(left, *tag)?, cls_affine(right, *tag)?))
        }
    }
}

/// The tree over the classes `span` that is `yes` in the classes `take` and `no` in the
/// others; the nodes off the paths to the ends of `take` are shared with `yes` and `no`.
fn cls_splice(
    yes: &Rc<Cls>,
    no: &Rc<Cls>,
    (lo, hi): (usize, usize),
    take: (usize, usize),
) -> Option<Rc<Cls>> {
    if take.0 <= lo && hi <= take.1 {
        return Some(yes.clone());
    }
    if hi <= take.0 || take.1 <= lo {
        return Some(no.clone());
    }
    let mid = lo + (hi - lo) / 2;
    let (yl, yr) = cls_halves(yes)?;
    let (nl, nr) = cls_halves(no)?;
    Some(Rc::new(Cls::Split {
        left: cls_splice(&yl, &nl, (lo, mid), take)?,
        right: cls_splice(&yr, &nr, (mid, hi), take)?,
        tag: (1, 0),
    }))
}

/// A persistent treap of the pieces of a [`Pa`], in the order of the input, each node
/// shared by every summary built from it. Splitting, joining and adding a line to every
/// value, or scaling every value ([`Tag`]), each take `O(log n)` expected time.
type Tree = Option<Arc<PaNode>>;

/// One piece of a [`Pa`] and the subtree it roots.
#[derive(Clone)]
struct PaNode {
    /// The piece: the inputs `lo..=hi`, on which the value is `a * x + b`.
    lo: End,
    hi: End,
    a: Int,
    b: Int,
    /// The least and the greatest input in the subtree.
    span: (End, End),
    /// Bounds on the values in the subtree, so that inverting skips a subtree whose values
    /// miss the demand: the least and the greatest value where no line was added to the
    /// subtree as a whole, and otherwise those bounds moved by the line's least and greatest
    /// value over `span` ([`Tag::vals`]), which hold the values and may be wider.
    vals: (Val, Val),
    /// Whether the subtree's pieces cover `span` with no gap, so that a subtree whose values
    /// lie in one piece of the demand is taken whole.
    dense: bool,
    /// The number of pieces in the subtree, so that a sum of two summaries walks the smaller
    /// ([`add_treaps`]).
    len: usize,
    /// A heap priority, fixed by the piece's ends, so the shape does not depend on the order
    /// of the operations that built it.
    prio: u64,
    /// The map still to be applied to both children: `a`, `b` and `vals` of this node
    /// already include it.
    tag: Tag,
    left: Tree,
    right: Tree,
}

/// A value of a summary, or the infinity a piece's line tends to at an infinite end of its
/// inputs ([`value_at`]); the derived order puts `Neg` below and `Pos` above every value.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Val {
    Neg,
    Fin(Int),
    Pos,
}

impl Val {
    /// `self + o`, where an infinity absorbs a value and `first`, an infinity, wins over the
    /// other: a lower bound is moved down first, an upper bound up.
    fn plus(&self, o: &Val, first: Val) -> Val {
        match (self, o) {
            (Val::Fin(x), Val::Fin(y)) => Val::Fin(x + y),
            _ if *self == first || *o == first => first,
            (Val::Fin(_), inf) | (inf, _) => inf.clone(),
        }
    }
}

/// An end of a demand as a [`Val`], the infinities as the infinities.
fn end_val(e: &End) -> Val {
    match e {
        NegInf => Val::Neg,
        Fin(v) => Val::Fin(Int::from(v)),
        PosInf => Val::Pos,
    }
}

/// The map of a summary's values `v` at the input `x` to `mul * v + slope * x + add`: a
/// scaling and a line added. A tag on a treap node applies it to every piece below, so that
/// adding a line to every piece of a summary ([`Pa::plus`]) costs one new node. The numbers
/// are unbounded ([`Int`]), one machine word while they fit in `i128`, so a map never fails:
/// a chain of `d` doublings has a coefficient of `d` bits.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Tag {
    mul: Int,
    slope: Int,
    add: Int,
}

impl Tag {
    /// The map that changes nothing.
    const ID: Tag = Tag {
        mul: Int::ONE,
        slope: Int::ZERO,
        add: Int::ZERO,
    };

    /// `x -> mul * x + add` on the values, with no line added.
    fn affine(mul: Int, add: Int) -> Tag {
        Tag {
            mul,
            slope: Int::ZERO,
            add,
        }
    }

    /// `self` followed by `outer`.
    fn then(&self, outer: &Tag) -> Tag {
        Tag {
            mul: &self.mul * &outer.mul,
            slope: &(&self.slope * &outer.mul) + &outer.slope,
            add: &(&self.add * &outer.mul) + &outer.add,
        }
    }

    /// The line `a * x + b` mapped.
    fn line(&self, a: &Int, b: &Int) -> (Int, Int) {
        (&(a * &self.mul) + &self.slope, &(b * &self.mul) + &self.add)
    }

    /// Bounds on the mapped values of a subtree whose values lie in `vals` and whose inputs
    /// lie in `span`: `vals` scaled ([`map_vals`]), then moved by the least and the greatest
    /// value of `slope * x` over `span`, an infinity where `span` is unbounded on the side the
    /// line grows toward. Exact when `slope` is 0; with a line added they hold the values
    /// and may be wider, as where the line and the subtree slope in opposite directions.
    fn vals(&self, vals: &(Val, Val), span: &(End, End)) -> (Val, Val) {
        let (lo, hi) = map_vals(vals, &self.mul, &self.add);
        if self.slope.is_zero() {
            return (lo, hi);
        }
        let at = |e: &End| match e {
            Fin(v) => Val::Fin(&self.slope * &Int::from(small(v))),
            NegInf if self.slope.is_positive() => Val::Neg,
            PosInf if self.slope.is_negative() => Val::Neg,
            _ => Val::Pos,
        };
        let (u, v) = (at(&span.0), at(&span.1));
        let (least, greatest) = if u <= v { (u, v) } else { (v, u) };
        (lo.plus(&least, Val::Neg), hi.plus(&greatest, Val::Pos))
    }
}

/// The value `a * x + b` at the end `x` of a piece: at an infinite end, the infinity the line
/// tends to there, or `b` when `a` is 0.
fn value_at(x: &End, a: &Int, b: &Int) -> Val {
    match x {
        Fin(v) => Val::Fin(&(a * &Int::from(small(v))) + b),
        _ if a.is_zero() => Val::Fin(b.clone()),
        NegInf if a.is_positive() => Val::Neg,
        PosInf if a.is_negative() => Val::Neg,
        _ => Val::Pos,
    }
}

/// Whether every finite end of `s` lies strictly between the ends of `i128`, as a piece's
/// ends must: they are compared as `i128` with the ends of `i128` as the infinities ([`key`]).
// Complexity tradeoff: the piecewise-affine summary of an `if` chain is given up when a
// domain or an arm's set it reads has a finite end past `i128`, and the `if` is read as
// before S22a (each arm by the catalog): exact, at the cost of the per-arm transfer, about
// `k^2.8` on a chain of `k` levels over a shared term. Why: the pieces' ends are `i128`, which
// keeps each split and join O(1) per node; ends of any size would cost time in their bits at
// every node. The ends of a summary are those of the domain and the guards' sets, which do not
// grow with the chain, unlike its coefficients and values, which are unbounded ([`Tag`]).
// Trigger: an input domain or an arm's set with a finite end of magnitude about `2^127` or
// more. Test: `l01_25_preimage_catalog::wide_ends::ends_past_i128_take_the_transfer_before`.
// COMPLEXITY.md S33. A complete solution would hold the pieces' ends as `Num`.
fn in_range(s: &IntervalSet) -> bool {
    // The pieces are in order, so every finite end lies between the least and the greatest
    // finite end, which are ends of the first or the last piece: `O(1)`, not `O(P)` for the
    // `P` pieces, which each summary of a split read (COMPLEXITY.md S22-hole-summaries).
    (s.first().into_iter().chain(s.last())).all(|(lo, hi)| {
        [lo, hi].into_iter().all(|e| {
            !matches!(e, Fin(v) if v.to_i128().is_none_or(|w| w == i128::MIN || w == i128::MAX))
        })
    })
}

/// A finite end that [`in_range`] admitted.
fn small(v: &Num) -> i128 {
    v.to_i128()
        .expect("the summary's ends lie in i128, checked by in_range")
}

/// An end as a number: the infinities lie past every finite end [`in_range`] admits.
fn key(e: &End) -> i128 {
    match e {
        NegInf => i128::MIN,
        Fin(v) => small(v),
        PosInf => i128::MAX,
    }
}

/// The summary of the input `var`, of domain `dom`, that is each taken arm's summary on the
/// inputs of its set ([`Walk::pa_select`], [`order_if`]): the arms' treaps sliced to the
/// stretches of their sets and joined in order; `None` when a set or the domain has an end
/// outside [`in_range`].
fn select(var: &Arc<str>, dom: &IntervalSet, arms: [Option<(&IntervalSet, &Pa)>; 2]) -> Option<Pa> {
    // Each arm's treap, and the stretches of inputs that take each arm, in order.
    let mut trees = Vec::with_capacity(2);
    let mut spans: Vec<(&End, &End, usize)> = Vec::new();
    for (set, arm) in arms.into_iter().flatten() {
        if !in_range(set) {
            return None;
        }
        spans.extend(set.pieces().map(|(lo, hi)| (lo, hi, trees.len())));
        trees.push(arm.to_treap(dom)?);
    }
    spans.sort_by_key(|&(lo, ..)| key(lo));
    // A hole of the domain between two stretches, where no input lies, is given to the
    // stretch before it, and two stretches of one arm so joined are one slice, so that the
    // summary is cut where the arm changes and not at each hole of the domain
    // ([`Pa::to_treap`]): its values there are read by no one.
    let mut slices: Vec<(End, End, usize)> = Vec::with_capacity(spans.len());
    for (lo, hi, arm) in spans {
        if let Some(last) = slices.last_mut()
            && no_input_between(dom, &last.1, lo)
        {
            if last.2 == arm {
                last.1 = hi.clone();
                continue;
            }
            last.1 = lo.pred();
        }
        slices.push((lo.clone(), hi.clone(), arm));
    }
    let mut root = None;
    for (lo, hi, arm) in slices {
        if let Some(s) = slice_treap(trees[arm].clone(), &lo, &hi) {
            root = join_treap(root, Some(s));
        }
    }
    Some(Pa::Piecewise {
        var: var.clone(),
        root,
    })
}

/// Whether no member of `dom` lies strictly between `a` and `b`, for `a < b`: `O(log P)` for
/// the `P` pieces of `dom`.
fn no_input_between(dom: &IntervalSet, a: &End, b: &End) -> bool {
    dom.pieces_after(|(_, hi)| hi <= a)
        .next()
        .is_none_or(|(lo, _)| lo >= b)
}

/// Whether `a` and `b` share a member: `O(p log P)` for the `p` pieces of `a` and the `P` of `b`.
fn meets(a: &IntervalSet, b: &IntervalSet) -> bool {
    read_domain(a.len() * (b.len() + 1).ilog2() as usize);
    (a.pieces()).any(|(lo, hi)| b.piece_at_or_above(lo).is_some_and(|(l, _)| l <= hi))
}

/// An end of an input's domain as an input, for the bounds of [`ByClass`]: the infinities are
/// the ends of `i64`, and `None` for a finite end outside `i64`.
fn input(e: &End) -> Option<i128> {
    match e {
        NegInf => Some(i64::MIN.into()),
        Fin(v) => v.to_i64().map(i128::from),
        PosInf => Some(i64::MAX.into()),
    }
}

/// `(lo, hi)` mapped by `x -> mul * x + add`, in order: an infinity stays one of the same sign
/// when `mul > 0` and becomes the other when `mul < 0`, and every value, an infinity too,
/// becomes `add` when `mul` is 0 (the limit of a line of slope 0 is its constant, as at
/// [`value_at`]).
fn map_vals((lo, hi): &(Val, Val), mul: &Int, add: &Int) -> (Val, Val) {
    if mul.is_zero() {
        return (Val::Fin(add.clone()), Val::Fin(add.clone()));
    }
    let f = |v: &Val| match v {
        Val::Fin(x) => Val::Fin(&(x * mul) + add),
        _ if mul.is_positive() => v.clone(),
        Val::Neg => Val::Pos,
        Val::Pos => Val::Neg,
    };
    if mul.is_positive() {
        (f(lo), f(hi))
    } else {
        (f(hi), f(lo))
    }
}

/// A piece of a summary: the inputs `lo..=hi` it covers, none for the whole domain, and the
/// line `(a, b)` of its values `a * u + b` ([`pa_pieces`]).
type Piece = (Option<(End, End)>, Int, Int);

/// The pieces of the summary `pa` in the order of its input, each the inputs `lo..=hi` it
/// covers (none for a constant or a line, which hold on the whole domain) and the line
/// `(a, b)` of its values `a * u + b`: `O(p)` for `p` pieces, the coefficients unbounded
/// ([`Tag`]).
fn pa_pieces(pa: &Pa) -> Vec<Piece> {
    fn walk(node: &Tree, f: &Tag, out: &mut Vec<Piece>) {
        let Some(n) = node else {
            return;
        };
        let below = n.tag.then(f);
        walk(&n.left, &below, out);
        let (a, b) = f.line(&n.a, &n.b);
        out.push((Some((n.lo.clone(), n.hi.clone())), a, b));
        walk(&n.right, &below, out);
    }
    match pa {
        Pa::Const(c) => vec![(None, Int::ZERO, c.clone())],
        Pa::Linear { a, b, .. } => vec![(None, a.clone(), b.clone())],
        Pa::Piecewise { root, .. } => {
            let mut out = Vec::new();
            walk(root, &Tag::ID, &mut out);
            out
        }
    }
}

/// A finite end of a piece of a summary as an `i128`, none for an infinite one.
fn end_of(e: &End) -> Option<i128> {
    match e {
        Fin(v) => Some(small(v)),
        NegInf | PosInf => None,
    }
}

/// The inputs at which a piece of `pieces` (in the order of their input, [`pa_pieces`]) or a
/// gap between two pieces starts, after the first piece and before the end of the last, in
/// increasing order: `O(p)` for `p` pieces.
fn piece_starts(pieces: &[Piece]) -> Vec<i128> {
    let mut out = Vec::new();
    let ends = pieces.iter().filter_map(|(piece, ..)| piece.as_ref());
    for ((_, hi), (lo, _)) in ends.clone().zip(ends.skip(1)) {
        out.extend(end_of(hi).map(|hi| hi + 1));
        out.extend(end_of(lo));
    }
    out.dedup();
    out
}

/// For each range of classes `l` of [`Walk::lin_by_class`], the starts (`starts`, each in
/// increasing order, [`piece_starts`]) of the ranges next to it, `l - 1` and `l + 1` with the
/// last range next to the first, as `x mod m` runs from `m - 1` to 0 between `x` and `x + 1`;
/// merged into one increasing list: `O(S)` for `S` starts in all.
fn neighbor_cuts(starts: &[Vec<i128>]) -> Vec<Vec<i128>> {
    let n = starts.len();
    (0..n)
        .map(|l| {
            let (before, after) = ((l + n - 1) % n, (l + 1) % n);
            let (a, b): (&[i128], &[i128]) = match (before == l, before == after) {
                (true, _) => (&[], &[]),
                (false, true) => (&starts[before], &[]),
                (false, false) => (&starts[before], &starts[after]),
            };
            let mut out = Vec::with_capacity(a.len() + b.len());
            let (mut i, mut j) = (0, 0);
            while i < a.len() || j < b.len() {
                let c = match (a.get(i), b.get(j)) {
                    (Some(&x), Some(&y)) if x <= y => {
                        i += 1;
                        j += usize::from(x == y);
                        x
                    }
                    (_, Some(&y)) => {
                        j += 1;
                        y
                    }
                    (Some(&x), None) => {
                        i += 1;
                        x
                    }
                    (None, None) => unreachable!("the loop runs while one list has more"),
                };
                out.push(c);
            }
            out
        })
        .collect()
}

/// The map `inner` followed by `outer`, for the maps of a [`ByClass`], whose [`Bound`] keeps
/// them in `i64`.
fn compose(inner: (i128, i128), outer: (i128, i128)) -> Option<(i128, i128)> {
    let mul = inner.0.checked_mul(outer.0)?;
    let add = inner.1.checked_mul(outer.0)?.checked_add(outer.1)?;
    Some((mul, add))
}

/// A deterministic splitmix64 priority from the piece's ends.
fn prio_of(lo: &End, hi: &End) -> u64 {
    let code = |e: &End| -> u64 {
        match e {
            NegInf => 0,
            Fin(v) => {
                // The high word, 0 for every end in `i64`, so that those keep their codes.
                let w = small(v);
                let high = ((w >> 64) ^ (w >> 63)) as u64;
                (w as u64).wrapping_add(1) ^ 0x5555_5555_5555_5555 ^ high.rotate_left(17)
            }
            PosInf => u64::MAX,
        }
    };
    let mut z = code(lo).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ code(hi);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// `vals` widened to hold `o`.
fn widen(vals: &mut (Val, Val), o: &(Val, Val)) {
    if o.0 < vals.0 {
        vals.0 = o.0.clone();
    }
    if o.1 > vals.1 {
        vals.1 = o.1.clone();
    }
}

/// The node for the piece `lo..=hi` with value `a * x + b` over two subtrees with no tag
/// above them.
fn make_node(lo: End, hi: End, a: Int, b: Int, left: Tree, right: Tree) -> Arc<PaNode> {
    let (u, v) = (value_at(&lo, &a, &b), value_at(&hi, &a, &b));
    let mut vals = if u <= v { (u, v) } else { (v, u) };
    let mut span = (lo.clone(), hi.clone());
    let mut dense = true;
    let mut len = 1;
    let next = |x: &End, y: &End| matches!((x, y), (Fin(x), Fin(y)) if small(x) + 1 == small(y));
    if let Some(l) = &left {
        widen(&mut vals, &l.vals);
        span.0 = l.span.0.clone();
        dense &= l.dense && next(&l.span.1, &lo);
        len += l.len;
    }
    if let Some(r) = &right {
        widen(&mut vals, &r.vals);
        span.1 = r.span.1.clone();
        dense &= r.dense && next(&hi, &r.span.0);
        len += r.len;
    }
    let prio = prio_of(&lo, &hi);
    Arc::new(PaNode {
        lo,
        hi,
        a,
        b,
        span,
        vals,
        dense,
        len,
        prio,
        tag: Tag::ID,
        left,
        right,
    })
}

/// The subtree with every value mapped by `f`, in `O(1)` steps on its numbers.
fn apply_tag(node: &Arc<PaNode>, f: &Tag) -> Arc<PaNode> {
    if *f == Tag::ID {
        return node.clone();
    }
    let (a, b) = f.line(&node.a, &node.b);
    Arc::new(PaNode {
        lo: node.lo.clone(),
        hi: node.hi.clone(),
        a,
        b,
        span: node.span.clone(),
        vals: f.vals(&node.vals, &node.span),
        dense: node.dense,
        len: node.len,
        prio: node.prio,
        tag: node.tag.then(f),
        left: node.left.clone(),
        right: node.right.clone(),
    })
}

/// The two children with the node's tag applied.
fn push_down(node: &PaNode) -> (Tree, Tree) {
    let tagged = |c: &Tree| c.as_ref().map(|c| apply_tag(c, &node.tag));
    (tagged(&node.left), tagged(&node.right))
}

/// The pieces of `left`, then those of `right`, which all lie above them.
fn join_treap(left: Tree, right: Tree) -> Tree {
    match (left, right) {
        (None, r) => r,
        (l, None) => l,
        (Some(l), Some(r)) => {
            if l.prio >= r.prio {
                let (ll, lr) = push_down(&l);
                let nr = join_treap(lr, Some(r));
                Some(make_node(
                    l.lo.clone(),
                    l.hi.clone(),
                    l.a.clone(),
                    l.b.clone(),
                    ll,
                    nr,
                ))
            } else {
                let (rl, rr) = push_down(&r);
                let nl = join_treap(Some(l), rl);
                Some(make_node(
                    r.lo.clone(),
                    r.hi.clone(),
                    r.a.clone(),
                    r.b.clone(),
                    nl,
                    rr,
                ))
            }
        }
    }
}

/// The inputs below `cut`, and the rest. A piece that holds `cut - 1` and `cut` is cut in
/// two; both lie in `i128`, since `cut` is above the piece's lower end and at most its upper
/// end, which [`in_range`] admitted.
///
/// The two halves have priorities of their own ([`prio_of`]), which may exceed those of the
/// cut piece's ancestors, so they are joined to the two parts only after the split
/// ([`split_around`]): placed where the piece was, they broke the heap order, and the treaps
/// of a chain of `k` slices grew deeper than `O(log k)` (item SCALE-fix-preimage).
fn split_at(root: Tree, cut: i128) -> (Tree, Tree) {
    let (l, cut_piece, r) = split_around(root, cut);
    match cut_piece {
        None => (l, r),
        Some((lo, hi, a, b)) => {
            let (below, above) = (End::from(cut - 1), End::from(cut));
            let l = join_treap(
                l,
                Some(make_node(lo, below, a.clone(), b.clone(), None, None)),
            );
            (
                l,
                join_treap(Some(make_node(above, hi, a, b, None, None)), r),
            )
        }
    }
}

/// A piece of a treap taken out whole: its ends and its line `a * x + b`.
type CutPiece = (End, End, Int, Int);

/// The pieces below `cut`, the piece that holds `cut - 1` and `cut` if one does, with its
/// line, and the pieces above: a split that makes no node of its own, so both parts keep the
/// heap order.
fn split_around(root: Tree, cut: i128) -> (Tree, Option<CutPiece>, Tree) {
    let Some(node) = root else {
        return (None, None, None);
    };
    if cut <= key(&node.span.0) {
        return (None, None, Some(node));
    }
    if cut > key(&node.span.1) {
        return (Some(node), None, None);
    }
    let (left, right) = push_down(&node);
    let (lo, hi, a, b) = (
        node.lo.clone(),
        node.hi.clone(),
        node.a.clone(),
        node.b.clone(),
    );
    if cut <= key(&lo) {
        let (ll, piece, lr) = split_around(left, cut);
        (ll, piece, Some(make_node(lo, hi, a, b, lr, right)))
    } else if cut > key(&hi) {
        let (rl, piece, rr) = split_around(right, cut);
        (Some(make_node(lo, hi, a, b, left, rl)), piece, rr)
    } else {
        (left, Some((lo, hi, a, b)), right)
    }
}

/// The pieces of `node`'s subtree with each value `v` made `min(v, c)` where `min`, and
/// `max(v, c)` otherwise. A subtree whose values all lie on the kept side of `c` is kept, and
/// one whose values all lie on the other side is mapped to `c` by a tag ([`map_vals`] with
/// multiplier 0), so only the nodes whose subtree's values lie on both sides of `c` are
/// visited: those on the paths to the `m` pieces whose line crosses `c`, `O((m + 1) log n)`
/// nodes, each joined in `O(log n)`.
fn clamp_treap(node: &Tree, min: bool, c: &Int) -> Tree {
    let n = node.as_ref()?;
    let (lo, hi) = &n.vals;
    let cv = Val::Fin(c.clone());
    let (kept, at_c) = if min {
        (*hi <= cv, *lo >= cv)
    } else {
        (*lo >= cv, *hi <= cv)
    };
    if kept {
        return Some(n.clone());
    }
    if at_c {
        return Some(apply_tag(n, &Tag::affine(Int::ZERO, c.clone())));
    }
    let (left, right) = push_down(n);
    let mut out = clamp_treap(&left, min, c);
    // The inputs of the node's own piece whose value lies on the kept side of `c`: one stretch
    // at an end of the piece, or none, since the line is monotone; the rest take `c`.
    let side = if min {
        IntervalSet::range(NegInf, Fin(Num::from(c)))
    } else {
        IntervalSet::range(Fin(Num::from(c)), PosInf)
    };
    let mut own = Vec::with_capacity(1);
    invert_piece(&n.lo, &n.hi, &n.a, &n.b, &side, &mut own);
    let mut pieces = Vec::with_capacity(3);
    match own.first() {
        None => pieces.push((n.lo.clone(), n.hi.clone(), Int::ZERO, c.clone())),
        Some((xl, xh)) => {
            if *xl > n.lo {
                pieces.push((n.lo.clone(), xl.pred(), Int::ZERO, c.clone()));
            }
            pieces.push((xl.clone(), xh.clone(), n.a.clone(), n.b.clone()));
            if *xh < n.hi {
                pieces.push((xh.succ(), n.hi.clone(), Int::ZERO, c.clone()));
            }
        }
    }
    for (plo, phi, a, b) in pieces {
        out = join_treap(out, Some(make_node(plo, phi, a, b, None, None)));
    }
    join_treap(out, clamp_treap(&right, min, c))
}

/// The pieces of `root` within `lo..=hi`, whose finite ends lie strictly between the
/// infinities ([`in_range`]), so that a cut is never confused with an infinity.
fn slice_treap(root: Tree, lo: &End, hi: &End) -> Tree {
    let root = match lo {
        Fin(v) => split_at(root, small(v)).1,
        _ => root,
    };
    match hi {
        Fin(v) => split_at(root, small(v) + 1).0,
        _ => root,
    }
}

/// The summary `p + sign * q` of two summaries of one input, defined where both are: on
/// the inputs of a piece of `p` and a piece of `q` the value is the sum of their lines.
///
/// The smaller treap, of `m` pieces, is walked, and the larger, of `n`, is cut at its
/// pieces' ends ([`add_into`]): each piece of the smaller adds its line to the stretch of
/// the larger it covers by one tag. Splitting the larger by the `m` sorted cuts of a treap
/// costs `O(m log(n / m + 1))` expected time, as for the union of two treaps by splitting
/// and joining (Blelloch, Ferizovic and Sun, "Just join for parallel ordered sets", 2016):
/// a cut at a node splits only the part of the larger between its ancestors' cuts. So a
/// chain of `d` sums, each with an operand of `O(1)` pieces, costs `O(d log d)` steps on
/// numbers.
fn add_treaps(p: &Tree, q: &Tree, sign: &Int) -> Tree {
    let len = |t: &Tree| t.as_ref().map_or(0, |n| n.len);
    if len(p) >= len(q) {
        add_into(p.clone(), q, &Tag::affine(sign.clone(), Int::ZERO))
    } else {
        let p_scaled = q
            .as_ref()
            .map(|r| apply_tag(r, &Tag::affine(sign.clone(), Int::ZERO)));
        add_into(p_scaled, p, &Tag::ID)
    }
}

/// `big + f(walk)`, where `f` (the tags above `walk`, and the sign) maps the pieces of
/// `walk`, on the inputs where both are defined: `big` is split at the ends of `walk`'s
/// piece, the part below goes with the left subtree, the part above with the right, and the
/// part within takes the piece's line by a tag.
fn add_into(big: Tree, walk: &Tree, f: &Tag) -> Tree {
    let (Some(n), Some(_)) = (walk, &big) else {
        return None;
    };
    let below = n.tag.then(f);
    let (a, b) = f.line(&n.a, &n.b);
    let (lower, rest) = match &n.lo {
        Fin(v) => split_at(big, small(v)),
        _ => (None, big),
    };
    let (within, upper) = match &n.hi {
        Fin(v) => split_at(rest, small(v) + 1),
        _ => (rest, None),
    };
    let left = add_into(lower, &n.left, &below);
    let right = add_into(upper, &n.right, &below);
    let within = within.map(|w| {
        apply_tag(
            &w,
            &Tag {
                mul: Int::ONE,
                slope: a,
                add: b,
            },
        )
    });
    join_treap(join_treap(left, within), right)
}

/// Appends to `out` the inputs of `node`'s subtree whose value, mapped by `f` (the tags
/// above it), lies in `z`. A subtree whose bounds on the values ([`PaNode::vals`]) miss `z`
/// is skipped, and one whose bounds lie in one piece of `z` and whose pieces leave no gap is
/// taken whole, so the time is `O((m + 1) log n)` for `m` pieces met, counting with them
/// the pieces of a subtree whose bounds meet `z` where its values do not (bounds widened by
/// an added line, [`Tag::vals`]). The ends of `z` may have any size.
///
/// Complexity tradeoff: after a line is added to a summary whose values slope the other way
/// (`n + (if n > 0 { -n } else { 0 })` is 0 for every `n > 0`), a subtree's bounds may be
/// wider than its values, so inverting may visit every piece of a subtree whose values miss
/// `z`: up to `O(p)` for `p` pieces, where it was `O((m + 1) log p)` for `m` pieces met. What
/// is given up: that bound after such a sum; the preimage stays exact. Why: the least and the
/// greatest value of `v + slope * x` over a subtree for any `slope` is a query on the convex
/// hull of its pieces' ends, which a tag cannot keep in `O(1)`. Trigger: a sum of a line and
/// a summary sloping the other way, inverted. Test:
/// `tests::a_sum_of_summaries_is_the_sum_at_every_point` (exactness). A complete solution
/// would keep each subtree's upper and lower hull of its pieces' ends, merged on join,
/// queried in `O(log p)` for the slope.
fn invert_treap(node: &Tree, f: &Tag, z: &IntervalSet, out: &mut Vec<(End, End)>) {
    let Some(n) = node else {
        return;
    };
    let (lo, hi) = f.vals(&n.vals, &n.span);
    let Some((zlo, zhi)) = z.pieces_after(|(_, zhi)| end_val(zhi) < lo).next() else {
        return;
    };
    let zl = end_val(zlo);
    if zl > hi {
        return;
    }
    if n.dense && zl <= lo && hi <= end_val(zhi) {
        out.push(n.span.clone());
        return;
    }
    let below = n.tag.then(f);
    invert_treap(&n.left, &below, z, out);
    let (a, b) = f.line(&n.a, &n.b);
    invert_piece(&n.lo, &n.hi, &a, &b, z, out);
    invert_treap(&n.right, &below, z, out);
}

/// Appends to `out` the inputs `x` in `lo..=hi` with `a * x + b` in `z`. Exact, so no end is
/// rounded: an infinite end of the piece is a limit of the line, never an input, and an input
/// found may lie outside `i64`.
fn invert_piece(lo: &End, hi: &End, a: &Int, b: &Int, z: &IntervalSet, out: &mut Vec<(End, End)>) {
    let (u, v) = (value_at(lo, a, b), value_at(hi, a, b));
    let (vlo, vhi) = if u <= v { (u, v) } else { (v, u) };
    for (zlo, zhi) in z.pieces_after(|(_, zhi)| end_val(zhi) < vlo) {
        if end_val(zlo) > vhi {
            break;
        }
        if a.is_zero() {
            // The one value, `b`, lies in this piece of `z`.
            out.push((lo.clone(), hi.clone()));
            break;
        }
        // The inputs whose value lies in `zlo..=zhi`, where an infinite end of `z` bounds
        // none.
        let (xl, xh) = if a.is_positive() {
            (
                solve(zlo, |zl| ceil_div(&(zl - b), a), NegInf),
                solve(zhi, |zh| (zh - b).div_floor(a), PosInf),
            )
        } else {
            let d = -a;
            (
                solve(zhi, |zh| ceil_div(&(b - zh), &d), NegInf),
                solve(zlo, |zl| (b - zl).div_floor(&d), PosInf),
            )
        };
        let (xl, xh) = (xl.max(lo.clone()), xh.min(hi.clone()));
        if xl <= xh {
            out.push((xl, xh));
        }
    }
}

/// `f` of the finite end `e`, as an end, or `inf` when `e` is infinite.
fn solve(e: &End, f: impl FnOnce(&Int) -> Int, inf: End) -> End {
    match e {
        Fin(v) => Fin(Num::from(&f(&Int::from(v)))),
        _ => inf,
    }
}

/// `n / d` rounded up, for `d > 0`.
fn ceil_div(n: &Int, d: &Int) -> Int {
    -&(-n).div_floor(d)
}

/// The number of a set of names bound within a term being closed ([`Locals`]).
type Lid = u32;

/// The set that binds no name.
const NO_LOCAL: Lid = 0;

/// The sets of names bound within the terms being closed ([`Walk::close`]), each name with the
/// name it is closed to, numbered so that a closed part is remembered by its set: a set and a
/// binding give one set, as a scope and a binding give one scope ([`Tx::bind`]). Each name is
/// renamed by its binder's number past any name a program writes, so that a closed term put
/// under the binder (the term a name of the scope is bound to) keeps its own names.
struct Locals {
    sets: Vec<imbl::HashMap<Name, Arc<str>>>,
    ids: HashMap<(Lid, Name, Tid), (Lid, Arc<str>)>,
}

impl Locals {
    fn new() -> Self {
        Locals {
            sets: vec![imbl::HashMap::new()],
            ids: HashMap::new(),
        }
    }

    /// The name `x` is closed to in `local`, if bound within.
    fn get(&self, local: Lid, x: Name) -> Option<Arc<str>> {
        self.sets[local as usize].get(&x).cloned()
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
fn compare(p: Prim, a: &Ints, b: &Ints) -> Fwd {
    let (Some((alo, ahi)), Some((blo, bhi))) = (a.bounds(), b.bounds()) else {
        return Fwd::bools(false, false);
    };
    fn one(x: &Ints) -> Option<(&End, &End)> {
        x.bounds().filter(|(l, h)| l == h)
    }
    let (t, f) = match p {
        Prim::Lt => (alo < bhi, ahi >= blo),
        Prim::Le => (alo <= bhi, ahi > blo),
        Prim::Gt => (ahi > blo, alo <= bhi),
        Prim::Ge => (ahi >= blo, alo < bhi),
        _ => {
            let eq = !a.set().meet(b.set()).is_empty();
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
    let c = Num::from(c);
    let fin = |d: i64| Fin(&c + &Num::from(d));
    match p {
        Prim::Lt => IntervalSet::range(NegInf, fin(-1)),
        Prim::Le => IntervalSet::range(NegInf, fin(0)),
        Prim::Gt => IntervalSet::range(fin(1), PosInf),
        Prim::Ge => IntervalSet::range(fin(0), PosInf),
        Prim::Eq => IntervalSet::range(fin(0), fin(0)),
        _ => IntervalSet::from_pieces(vec![(NegInf, fin(-1)), (fin(1), PosInf)]),
    }
}

/// Each piece of `z` moved up by `c`, exact.
fn shift(z: &IntervalSet, c: i128) -> IntervalSet {
    let c = Num::from(c);
    let m = |e: &End| match e {
        Fin(v) => Fin(v + &c),
        e => e.clone(),
    };
    IntervalSet::from_pieces(z.pieces().map(|(lo, hi)| (m(lo), m(hi))).collect())
}

/// The integers `c - v` for each member `v` of `z`: the integers `x` with `c - x` in `z`, each
/// piece reflected and moved by `c`, exact at any magnitude. The pieces stay apart and the
/// result is exact; the forward image of `{c} - z` would cap the pieces of each sign region
/// (`revision::map2`) and merge the pieces it moves across zero (plan item S22b). The clip
/// reads `c - x` by it too (plan item S22b-rest).
fn reflect(z: &IntervalSet, c: i128) -> IntervalSet {
    let c = Num::from(c);
    let m = |e: &End| match e {
        Fin(v) => Fin(&c - v),
        NegInf => PosInf,
        PosInf => NegInf,
    };
    IntervalSet::from_pieces(z.pieces().rev().map(|(lo, hi)| (m(hi), m(lo))).collect())
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
    let d = Num::from(c);
    // ceil and floor of v / c, at an endpoint.
    let q = |e: &End, up: bool| match e {
        Fin(v) => {
            let f = v.div_floor(&d);
            Fin(if up && !v.mod_floor(&d).is_zero() {
                &f + &Num::ONE
            } else {
                f
            })
        }
        e if c < 0 => -e,
        e => e.clone(),
    };
    IntervalSet::from_pieces(
        z.pieces()
            .map(|(lo, hi)| {
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
    let (d, top) = (Num::from(c), Num::from(c.unsigned_abs() as i128 - 1));
    let lower = |e: &End| match e {
        Fin(q) => Fin(q * &d),
        e if c < 0 => -e,
        e => e.clone(),
    };
    let upper = |e: &End| match e {
        Fin(q) => Fin(&(q * &d) + &top),
        e if c < 0 => -e,
        e => e.clone(),
    };
    IntervalSet::from_pieces(
        z.pieces()
            .map(|(lo, hi)| {
                if c > 0 {
                    (lower(lo), upper(hi))
                } else {
                    (lower(hi), upper(lo))
                }
            })
            .collect(),
    )
}

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
    let m = Num::from(c.unsigned_abs() as i128);
    let all = IntervalSet::range(End::of(0), Fin(&m - &Num::ONE));
    let rem = z.meet(&all);
    if rem.is_empty() {
        return (IntervalSet::empty(), true);
    }
    if rem == all {
        return (within.clone(), true);
    }
    let Some((Fin(lo), Fin(hi))) = within.bounds() else {
        return (within.clone(), false);
    };
    let (k0, k1) = (lo.div_floor(&m), hi.div_floor(&m));
    let period = |k: &Num| {
        let base = k * &m;
        rem.pieces()
            .filter_map(|(a, b)| match (a, b) {
                (Fin(a), Fin(b)) => Some((Fin(&base + a), Fin(&base + b))),
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    let mut pieces = period(&k0);
    let next = &k0 + &Num::ONE;
    if k1 > next {
        let Some((Fin(a), Fin(b))) = rem.bounds() else {
            unreachable!("the remainders lie in 0..m")
        };
        let last = &k1 - &Num::ONE;
        pieces.push((Fin(&(&next * &m) + a), Fin(&(&last * &m) + b)));
    }
    if k1 > k0 {
        pieces.extend(period(&k1));
    }
    let s = IntervalSet::from_pieces(pieces).meet(within);
    (s, k1 <= next)
}

/// The integers `x` with `min(x, c)` (or `max`) in `z`.
fn minmax_pre(p: Prim, z: &IntervalSet, c: i64) -> IntervalSet {
    let at_c = if p == Prim::Min {
        IntervalSet::range(End::of(c), PosInf)
    } else {
        IntervalSet::range(NegInf, End::of(c))
    };
    let below = if p == Prim::Min {
        IntervalSet::range(NegInf, End::of(c))
    } else {
        IntervalSet::range(End::of(c), PosInf)
    };
    let own = z.meet(&below);
    if z.contains(c) { own.join(&at_c) } else { own }
}

/// The projection of the points of a listed box at which the term meets the demand: every
/// input's set is empty or one the source lists member by member (`listed`,
/// [`preimage_listed`]), and at most one input has more than one member, so the points
/// number no more than the members the source lists (docs/thresholds.md, replacement 8). The
/// term's form must show that it ends ([`stage::ends`]). A range is left to the catalog and the
/// linear relation, whatever its width: `int[0..=1]`, `int[0..=2]` and `int[0..=3]` are read
/// by the same steps, and `{0, 1, 2}` is enumerated (DESIGN.md L1.25, author's answer to Q11).
///
/// Complexity tradeoff: a box with an input the source gives as a range, with two or more
/// inputs of several members, or with a term whose ending is not shown is not enumerated; it
/// gets the catalog's and the linear relation's answer, which may be wider. Why: the points
/// of a box are the product of its axes, exponential in the inputs and in the bits of each
/// range, and a term not shown to end may not end. Trigger: those three properties of the
/// box and the term, each read from what is written, never from a width or a constant. Tests:
/// `l01_25_preimage_catalog::entries::a_listed_box_is_enumerated_and_a_range_is_not`,
/// `l01_25_preimage_catalog::entries::ranges_of_every_width_are_read_by_one_method`.
/// COMPLEXITY.md row C18 (thresholds.md replacement 8). A complete solution is `@exact`
/// ([`exact_preimage`]), branch and prune over the box, at a cost in its points.
fn enumerate(term: &Term, dom: &Domains, listed: &Listed, demand: &Demand) -> Option<Whole> {
    let mut axes: Vec<(Arc<str>, Vec<Num>)> = Vec::new();
    for (k, s) in dom {
        if !s.is_empty() && !listed.contains(k) {
            return None;
        }
        // Each member of a listed set is one the source lists, so this costs the list.
        let mut vs = Vec::new();
        for (lo, hi) in s.pieces() {
            let (Fin(lo), Fin(hi)) = (lo, hi) else {
                return None;
            };
            let mut v = lo.clone();
            while v <= *hi {
                vs.push(v.clone());
                v = &v + &Num::ONE;
            }
        }
        axes.push((k.clone(), vs));
    }
    if axes.iter().filter(|(_, vs)| vs.len() > 1).count() > 1 {
        return None;
    }
    // The box is read first: `ends` walks the term as a tree, so it costs the term unshared
    // (ledger ENDS-dag), and a box that cannot be listed needs no answer from it. An empty box
    // holds no point to run, so it is exact whether or not the term ends; the transfer leaves
    // one inexact when it rounded, as `3 * t - 1` repeated 37 times on `i <= -21` does, and
    // asking `ends` first cost `2^37` steps there.
    if axes.iter().any(|(_, vs)| vs.is_empty()) {
        return Some(Whole {
            dom: dom.clone(),
            exact: true,
        });
    }
    if !stage::ends(term) {
        return None;
    }
    enumerate_on(term, &axes, demand)
}

/// The congruence class of each input that has one, under `@exact`; an input not listed may be
/// any integer.
pub type Classes = BTreeMap<Arc<str>, Congruence>;

/// Whether [`Walk::cached`] remembers nothing a call stopped below, as before ST-formula-k2-rec,
/// for the tests that compare the memo with the one before; never outside the tests.
fn none_held() -> bool {
    #[cfg(test)]
    return tests::NONE_HELD.get();
    #[cfg(not(test))]
    false
}

thread_local! {
    /// The boxes the searches of `@exact` preimages and witnesses took on this thread since
    /// [`exact_steps`] last read it.
    static EXACT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// The boxes the searches of `@exact` preimages and witnesses took on this thread since the
/// last call, which resets the count. Only a scope declared `@exact` searches (step L1.39b).
pub fn exact_steps() -> u64 {
    EXACT.replace(0)
}

thread_local! {
    /// The pieces of an input's domain that [`Walk::back_by_class`] read on this thread since
    /// [`class_domain_reads`] last read it, a binary search counted by its steps.
    static CLASS_READS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// The pieces of an input's domain that the reading of a test on a remainder by its classes
/// read on this thread since the last call, which resets the count (COMPLEXITY.md
/// S22-hole-summaries).
pub fn class_domain_reads() -> u64 {
    CLASS_READS.replace(0)
}

fn read_domain(n: usize) {
    CLASS_READS.with(|c| c.set(c.get() + n as u64));
}

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
    let mut p = preimage_of(term, inputs, NONE_LISTED, demand);
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
}

/// A point of the inputs, each input within its class, at which the term meets the demand.
pub type Point = BTreeMap<Arc<str>, Num>;

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
                Some((Fin(lo), _)) => (k.clone(), lo.clone()),
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
        let r = preimage_of(term, &dom, NONE_LISTED, demand);
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
    let mut first = First(None, lowest);
    let (read, unread) = split_read(term, dom);
    branch(term, read, classes, demand, &mut first)?;
    Some(first.0.map(|mut p| {
        p.extend(lowest(&unread));
        p
    }))
}

/// `dom` split in two: the inputs `term` reads, which a search narrows and halves, and the
/// others, whose values change no point's value.
// Complexity tradeoff: the naive search kept every input in each box, so each box copied,
// narrowed and compared all `m` inputs, `O(m)` per box for a term that reads a few, and
// halved the widest input even when the term does not read it, which multiplies the boxes by
// the points of the unread inputs. Used: the search holds only the inputs the term reads
// ([`stage::free`], `O(s log s)` for `s` distinct parts, once per search), so a box costs the
// inputs it touches and is halved on one of them, and the others keep their whole sets.
// Tests: `l01_25_preimage_catalog::scaling::an_exact_search_reads_only_the_inputs_it_touches`,
// `l01_25_preimage_catalog::exact::inputs_the_term_does_not_read_keep_their_sets`;
// COMPLEXITY.md row S21.
fn split_read(term: &Term, dom: Domains) -> (Domains, Domains) {
    let read = stage::free(term);
    dom.into_iter().partition(|(k, _)| read.contains(k))
}

/// The projection of the points of `dom` in `classes` meeting `demand`, and whether their box
/// holds no point that fails it; `None` when an input is unbounded or a point cannot be run.
fn exact_search(
    term: &Term,
    dom: &Domains,
    classes: &Classes,
    demand: &Demand,
) -> Option<(Domains, bool)> {
    let empty = || {
        dom.keys()
            .map(|k| (k.clone(), IntervalSet::empty()))
            .collect()
    };
    let Some(dom) = within_classes(dom, classes) else {
        return Some((empty(), true));
    };
    if dom
        .values()
        .any(|s| !matches!(s.bounds(), Some((Fin(_), Fin(_)))))
    {
        return None;
    }
    /// The search for every point: whether a box met the demand, and the projections of the
    /// boxes met so far, each input's the join of its parts; a box within them adds nothing.
    struct Met(bool, Domains);
    impl Search for Met {
        fn skip(&self, b: &Domains) -> bool {
            self.0 && b.iter().all(|(k, s)| s.is_subset(&self.1[k]))
        }
        fn all(&mut self, b: &Domains) -> bool {
            self.0 = true;
            for (k, s) in b {
                let joined = self.1[k].join(s);
                self.1.insert(k.clone(), joined);
            }
            false
        }
    }
    let (read, unread) = split_read(term, dom);
    let mut met = Met(
        false,
        read.keys()
            .map(|k| (k.clone(), IntervalSet::empty()))
            .collect(),
    );
    branch(term, read, classes, demand, &mut met)?;
    let Met(found, mut met) = met;
    if !found {
        return Some((empty(), true));
    }
    // The projections' product is exact when at most one read input has several values; the
    // unread inputs keep their sets, which change no point's value.
    let several = met.values().filter(|s| !is_point(s)).count();
    let exact = several <= 1 || {
        // The second search looks for a point of `met` that fails the demand: one whose value
        // is outside it, or whose run fails (DESIGN.md sec:failure). A search for the
        // complement demand misses the second kind, as the diagonal of `1 div (y - x)`
        // (SOUND-exact-oracle).
        !fails_in(term, met.clone(), classes, demand)?
    };
    met.extend(unread);
    Some((met, exact))
}

/// Whether some point of `root` with each input in its class fails `demand`: its value is
/// outside the demand, or its run fails. Branch and prune as in [`branch`]: a box is found to
/// hold such a point when [`preimage_in`] drops a value of an input's class from it (the
/// preimage keeps every point that meets the demand), dropped when the preimage is exact and
/// keeps all of it, and otherwise halved on its widest input; a single point is evaluated.
/// `None` when a point cannot be run.
fn fails_in(term: &Term, root: Domains, classes: &Classes, demand: &Demand) -> Option<bool> {
    match classes_decide(term, classes, demand) {
        Some(true) => return Some(false),
        Some(false) => return Some(true),
        None => {}
    }
    let mut tx = Tx::new();
    let top = tx.terms.add(term);
    let mut boxes = vec![root];
    while let Some(b) = boxes.pop() {
        EXACT.with(|c| c.set(c.get() + 1));
        if b.values().all(is_point) {
            if !demand.holds(&run_point(term, &b)?) {
                return Some(true);
            }
            continue;
        }
        let r = preimage_in(&mut tx, top, term, &b, NONE_LISTED, demand);
        let dropped = b.iter().any(|(k, s)| {
            let out = r.domains[k].complement_in(s);
            match classes.get(k) {
                Some(c) => !reduce_congruence(&out, c).0.is_empty(),
                None => !out.is_empty(),
            }
        });
        if dropped {
            return Some(true);
        }
        if !r.exact {
            halve(&b, classes, &mut boxes);
        }
    }
    Some(false)
}

/// The value of `term` at the point `b`, each input one value; `None` when it cannot be run.
fn run_point(term: &Term, b: &Domains) -> Option<Value> {
    let mut t = term.clone();
    for (k, s) in b.iter().rev() {
        let Some((Fin(v), _)) = s.bounds() else {
            unreachable!("a point is finite")
        };
        t = Term::Let(
            k.clone(),
            Shared::new(Term::Lit(Value::from(v))),
            Shared::new(t),
        );
    }
    Evaluator::new(World::new()).run(&t).ok()
}

/// Pushes onto `boxes` the two halves of `b` split at the middle of its widest input, each
/// within `classes` and dropped when it holds no point of them.
fn halve(b: &Domains, classes: &Classes, boxes: &mut Vec<Domains>) {
    let (k, lo, hi) = b
        .iter()
        .filter_map(|(k, s)| match s.bounds() {
            Some((Fin(lo), Fin(hi))) if lo < hi => Some((k, lo, hi)),
            _ => None,
        })
        .max_by_key(|(_, lo, hi)| *hi - *lo)
        .expect("a box of more than one point has an input of more than one value");
    let mid = lo + &(hi - lo).div_floor(&Num::from(2i64));
    for half in [
        IntervalSet::range(Fin(&mid + &Num::ONE), PosInf),
        IntervalSet::range(NegInf, Fin(mid.clone())),
    ] {
        let mut h = b.clone();
        h.insert(k.clone(), b[k].meet(&half));
        if let Some(h) = within_classes(&h, classes) {
            boxes.push(h);
        }
    }
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
        EXACT.with(|c| c.set(c.get() + 1));
        if search.skip(&b) {
            continue;
        }
        let b = if b.values().all(is_point) {
            b
        } else {
            let r = preimage_in(&mut tx, top, term, &b, NONE_LISTED, demand);
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
            if demand.holds(&run_point(term, &b)?) && search.all(&b) {
                return Some(true);
            }
            continue;
        }
        halve(&b, classes, &mut boxes);
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
            Congruence::Class { modulus, residue } if modulus.is_zero() => {
                Some(z.contains_end(&End::Fin(residue)))
            }
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
            let eq = match (&x, &y) {
                (
                    Congruence::Class {
                        modulus: m,
                        residue: u,
                    },
                    Congruence::Class {
                        modulus: n,
                        residue: v,
                    },
                ) if m.is_zero() && n.is_zero() => u == v,
                _ if x.meet(&y) == Congruence::Bottom => false,
                _ => return None,
            };
            Some(eq == (*p == Prim::Eq))
        }
        _ => None,
    }
}

/// The class of the integer `term` at every point with each input in its class, by Granger's
/// arithmetic of congruences, exact at every size; `None` for a form it does not cover.
fn class_of(term: &Term, classes: &Classes) -> Option<Congruence> {
    let parts = |c: Congruence| match c {
        Congruence::Bottom => None,
        Congruence::Class { modulus, residue } => Some((modulus, residue)),
    };
    match term {
        Term::Lit(Value::Int(v)) => Some(Congruence::single(*v)),
        Term::Lit(Value::Big(v)) => Some(Congruence::single(Num::from(&**v))),
        Term::Var(x) => Some(classes.get(x).cloned().unwrap_or(Congruence::top())),
        Term::Let(x, _, body) => class_of(body, &unbound(classes, x)),
        Term::Prim(p, xs) => match (p, xs.as_slice()) {
            (Prim::Neg, [a]) => {
                let (m, r) = parts(class_of(a, classes)?)?;
                Some(Congruence::new(m, -&r))
            }
            (Prim::Add | Prim::Sub, [a, b]) => {
                let ((m, r), (n, s)) =
                    (parts(class_of(a, classes)?)?, parts(class_of(b, classes)?)?);
                let v = if *p == Prim::Add { &r + &s } else { &r - &s };
                Some(Congruence::new(m.gcd(&n), v))
            }
            (Prim::Mul, [a, b]) => {
                // (r mod m)(s mod n) is rs mod gcd(mn, rn, sm).
                let ((m, r), (n, s)) =
                    (parts(class_of(a, classes)?)?, parts(class_of(b, classes)?)?);
                let g = (&m * &n).gcd(&(&r * &n)).gcd(&(&s * &m));
                Some(Congruence::new(g, &r * &s))
            }
            (Prim::Mod, [a, Term::Lit(k)]) => {
                // `x mod k` is Euclidean, so in 0..k; when k divides the modulus it is one value,
                // and otherwise it is x's residue modulo gcd(m, k).
                let k = match k {
                    Value::Int(k) => Num::from(*k),
                    Value::Big(k) => Num::from(&**k),
                    _ => return None,
                };
                if k.signum() <= 0 {
                    return None;
                }
                let (m, r) = parts(class_of(a, classes)?)?;
                if m.rem_euclid(&k).is_zero() {
                    Some(Congruence::single(r.rem_euclid(&k)))
                } else {
                    Some(Congruence::new(m.gcd(&k), r))
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
fn enumerate_on(term: &Term, axes: &[(Arc<str>, Vec<Num>)], demand: &Demand) -> Option<Whole> {
    let mut met: Vec<Vec<&Num>> = vec![Vec::new(); axes.len()];
    let mut count: u64 = 0;
    let mut point = vec![0usize; axes.len()];
    loop {
        let mut t = term.clone();
        for ((k, vs), &i) in axes.iter().zip(&point).rev() {
            t = Term::Let(
                k.clone(),
                Shared::new(Term::Lit(Value::from(&vs[i]))),
                Shared::new(t),
            );
        }
        let v = Evaluator::new(World::new()).run(&t).ok()?;
        if demand.holds(&v) {
            count += 1;
            for (j, &i) in point.iter().enumerate() {
                met[j].push(&axes[j].1[i]);
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
                                vs.iter()
                                    .map(|&v| (Fin(v.clone()), Fin(v.clone())))
                                    .collect(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::collections::BTreeSet;
    use zedc_presburger::presburger::TWO_AT_A_TIME;

    thread_local! {
        /// Whether [`Walk::cached`] remembers nothing a call stopped below ([`none_held`]).
        pub(super) static NONE_HELD: Cell<bool> = const { Cell::new(false) };
        /// Each entry made below a stop, by its table and key: the lambdas being read when it
        /// began, by their places, and the inputs of its context.
        static MADE: RefCell<HashMap<u64, (Vec<Tid>, Sets)>> = RefCell::new(HashMap::new());
        /// Of the reads of entries made below a stop: all, those on a stack higher than where
        /// the entry began, and those in a context with other inputs (within another summary).
        static READS: Cell<[u64; 3]> = const { Cell::new([0; 3]) };
        /// Whether [`Walk::cached`] reads the term again at each hit, an entry made below a stop
        /// on the stack it began on and any other entry on an empty stack, and checks the two
        /// agree ([`rechecked`]).
        pub(super) static RECHECK: Cell<bool> = const { Cell::new(false) };
        /// Whether [`Walk::cached`] passes over entries made below a stop, while it reads a
        /// term again for [`RECHECK`].
        pub(super) static BYPASS: Cell<bool> = const { Cell::new(false) };
        /// Of the entries [`RECHECK`] read again: those compared, those of kinds not compared,
        /// those read on a stack higher than where they began, those read with other inputs, and
        /// the entries that hold everywhere compared.
        static CHECKED: Cell<[u64; 5]> = const { Cell::new([0; 5]) };
        /// Of the entries [`RECHECK`] compared: the summaries ([`Pa`]) made below a stop and
        /// those that hold everywhere, then the same for the summaries over every class of
        /// remainders ([`ByClass`]).
        static SUMMARIES: Cell<[u64; 4]> = const { Cell::new([0; 4]) };
    }

    fn made_key<K: Hash, V>(table: Table<K, V>, k: &K) -> u64 {
        use std::hash::Hasher;
        let mut h = std::hash::DefaultHasher::new();
        (table as usize).hash(&mut h);
        k.hash(&mut h);
        h.finish()
    }

    /// The bodies of the lambdas being read, by their places.
    fn stack(tx: &Tx<'_>) -> Vec<Tid> {
        let mut s = vec![0; tx.run.active.len()];
        for (&body, &at) in &tx.run.active {
            s[at] = body;
        }
        s
    }

    /// Records an entry [`Walk::cached`] makes below a stop, which began on a stack `base` high.
    pub(super) fn held_made<K: Hash, V>(tx: &Tx<'_>, table: Table<K, V>, k: &K, base: usize) {
        let s = stack(tx);
        assert_eq!(
            s.len(),
            base,
            "the stack is as high as where the entry began"
        );
        let made = (s, tx.cx.inputs.clone());
        MADE.with_borrow_mut(|m| m.insert(made_key(table, k), made));
    }

    /// Counts a read of an entry made below a stop, if `k` holds one, and checks that the
    /// lambdas being read where it began are still being read at the same places, but for
    /// a read [`BYPASS`] passes over.
    pub(super) fn held_read<K: Hash + Eq, V>(tx: &mut Tx<'_>, table: Table<K, V>, k: &K) {
        // Reading again for [`RECHECK`] sets aside lambdas, and passes over these entries.
        if BYPASS.get()
            || !table(&mut tx.run.memo)
                .get(k)
                .is_some_and(|e| e.1 != usize::MAX)
        {
            return;
        }
        let (below, inputs) = MADE.with_borrow(|m| m[&made_key(table, k)].clone());
        let now = stack(tx);
        assert!(
            now.starts_with(&below),
            "an entry made on the stack {below:?} is read on {now:?}"
        );
        let mut r = READS.get();
        r[0] += 1;
        r[1] += u64::from(now.len() > below.len());
        r[2] += u64::from(tx.cx.inputs != inputs);
        READS.set(r);
    }

    /// Checks the entry made below a stop that `k` holds, `v` with cut `cut`, against its term
    /// read again by `f` with no such entry ([`BYPASS`]), in the context of the read, on the
    /// stack the entry began on: the lambdas read since are set aside while `f` runs, and the
    /// entries below a stop it makes are removed after, so that the memo holds no entry that
    /// began on that stack once they are back.
    pub(super) async fn recheck<'m, 't, K: Hash, V: 'static, F: Future<Output = V>>(
        w: &Walk<'m, 't>,
        table: Table<K, V>,
        k: &K,
        v: &V,
        cut: usize,
        f: impl FnOnce() -> F,
    ) {
        let (above, inputs, held, outer) = w.with(|tx| {
            // An entry that holds wherever it is reached is read again with no lambda being read.
            let (base, inputs) = match cut {
                usize::MAX => (0, false),
                _ => MADE.with_borrow(|m| {
                    let (below, inputs) = &m[&made_key(table, k)];
                    (below.len(), *inputs != tx.cx.inputs)
                }),
            };
            let above: Vec<(Tid, usize)> = (tx.run.active.iter())
                .filter(|e| *e.1 >= base)
                .map(|(&b, &at)| (b, at))
                .collect();
            for (b, _) in &above {
                tx.run.active.remove(b);
            }
            // The entries made on the stack as it is are kept apart, out of reach of the lambdas
            // read again, which are not the ones being read.
            let held = std::mem::take(&mut tx.run.memo.held);
            BYPASS.set(true);
            let outer = std::mem::replace(&mut tx.cx.cut, usize::MAX);
            (above, inputs, held, outer)
        });
        let fresh = f().await;
        let again = w.with(|tx| {
            let again = std::mem::replace(&mut tx.cx.cut, outer);
            BYPASS.set(false);
            let m = &mut tx.run.memo;
            while let Some((_, unheld)) = m.held.pop() {
                unheld(m);
            }
            m.held = held;
            tx.run.active.extend(above.iter().copied());
            again
        });
        let mut c = CHECKED.get();
        if cut != usize::MAX {
            c[2] += u64::from(!above.is_empty());
            c[3] += u64::from(inputs);
        }
        CHECKED.set(c);
        rechecked(v, &fresh, cut, again);
    }

    /// Checks an entry made below a stop against its term read again: the same value and the
    /// same cut. Values of the kinds no test compares are counted apart.
    fn rechecked<V: 'static>(v: &V, fresh: &V, cut: usize, again: usize) {
        use std::any::Any;
        let (a, b): (&dyn Any, &dyn Any) = (v, fresh);
        let same = if let (Some(a), Some(b)) = (a.downcast_ref::<Fwd>(), b.downcast_ref()) {
            Some(fwd_same(a, b))
        } else if let (Some(a), Some(b)) = (a.downcast_ref::<Res>(), b.downcast_ref()) {
            Some(res_same(a, b))
        } else if let (Some(a), Some(b)) = (a.downcast_ref::<Option<bool>>(), b.downcast_ref()) {
            Some(a == b)
        } else if let (Some(a), Some(b)) = (a.downcast_ref::<bool>(), b.downcast_ref()) {
            Some(a == b)
        } else if let (Some(a), Some(b)) = (a.downcast_ref::<Option<Value>>(), b.downcast_ref()) {
            Some(a == b)
        } else if let (Some(a), Some(b)) =
            (a.downcast_ref::<Option<IntervalSet>>(), b.downcast_ref())
        {
            Some(a == b)
        } else if let (Some(a), Some(b)) = (a.downcast_ref::<Option<Shared>>(), b.downcast_ref()) {
            // A closed term ([`Walk::close`]): its names bound within are renamed by their
            // binders' numbers, which a term read again keeps.
            Some(a == b)
        } else if a.is::<Option<Lin>>() || a.is::<Option<Formula>>() {
            // A translation read again defines its own auxiliary atoms anew.
            Some(renamed(&shown_any(a), &shown_any(b)))
        } else if a.is::<Option<Pa>>() || a.is::<Option<ByClass>>() {
            // A summary read again builds its own treaps and trees, so the two are compared
            // by what they state: each piece, and each class's summary.
            Some(shown_any(a) == shown_any(b))
        } else {
            None
        };
        // An entry that holds wherever it is reached may stop where its own reading calls
        // itself, which its cut leaves out.
        let held = cut != usize::MAX;
        let summary = if a.is::<Option<Pa>>() {
            Some(0)
        } else if a.is::<Option<ByClass>>() {
            Some(2)
        } else {
            None
        };
        if let Some(i) = summary {
            let mut s = SUMMARIES.get();
            s[i + usize::from(!held)] += 1;
            SUMMARIES.set(s);
        }
        assert!(
            !held || cut == again,
            "an entry's cut {cut} where it began, {again} again"
        );
        let mut c = CHECKED.get();
        match same {
            Some(same) => {
                assert!(
                    same,
                    "an entry's value where it began, cut {cut}: {} read again {}, cut {again}",
                    shown_any(a),
                    shown_any(b)
                );
                c[if held { 0 } else { 4 }] += 1;
            }
            None => c[1] += 1,
        }
        CHECKED.set(c);
    }

    /// A value of a kind [`rechecked`] compares, shown.
    fn shown_any(v: &dyn std::any::Any) -> String {
        if let Some(f) = v.downcast_ref::<Fwd>() {
            format!(
                "ints {} bools {:?} fails {} other {}",
                f.ints, f.bools, f.fails, f.other
            )
        } else if let Some(r) = v.downcast_ref::<Res>() {
            let dom: Vec<String> = r.dom.iter().map(|(n, s)| format!("{n} {s}")).collect();
            format!("dom {dom:?} none {} exact {}", r.none, r.exact)
        } else if let Some(f) = v.downcast_ref::<Option<Formula>>() {
            format!("{:?}", f.as_ref().map(built))
        } else if let Some(x) = v.downcast_ref::<Option<bool>>() {
            format!("{x:?}")
        } else if let Some(x) = v.downcast_ref::<bool>() {
            format!("{x}")
        } else if let Some(x) = v.downcast_ref::<Option<Value>>() {
            format!("{x:?}")
        } else if let Some(x) = v.downcast_ref::<Option<IntervalSet>>() {
            format!("{x:?}")
        } else if let Some(x) = v.downcast_ref::<Option<Lin>>() {
            format!("{:?}", x.as_ref().map(Lin::to_string))
        } else if let Some(x) = v.downcast_ref::<Option<Pa>>() {
            x.as_ref().map_or_else(|| "none".into(), pa_shown)
        } else if let Some(x) = v.downcast_ref::<Option<ByClass>>() {
            x.as_ref().map_or_else(|| "none".into(), by_class_shown)
        } else {
            "a kind not shown".into()
        }
    }

    /// The function a summary states, as its input and its pieces `lo..=hi: a * x + b` in
    /// order, with each subtree's maps applied and neighboring pieces of one line joined, so
    /// that two summaries of one function are shown alike however their treaps were built.
    fn pa_shown(p: &Pa) -> String {
        let (var, pieces) = match p {
            Pa::Const(c) => (None, vec![(NegInf, PosInf, Int::ZERO, c.clone())]),
            Pa::Linear { var, a, b } => (Some(var), vec![(NegInf, PosInf, a.clone(), b.clone())]),
            Pa::Piecewise { var, root } => (Some(var), treap_pieces(root)),
        };
        let mut joined: Vec<(End, End, Int, Int)> = Vec::with_capacity(pieces.len());
        for (lo, hi, a, b) in pieces {
            match joined.last_mut() {
                Some(last) if (&last.2, &last.3) == (&a, &b) && last.1.succ() == lo => last.1 = hi,
                _ => joined.push((lo, hi, a, b)),
            }
        }
        // A function constant over every input reads none.
        let var = match joined.as_slice() {
            [(NegInf, PosInf, a, _)] if a.is_zero() => None,
            _ => var,
        };
        let shown: Vec<String> = (joined.iter())
            .map(|(lo, hi, a, b)| format!("{lo}..={hi}: {a} x + {b}"))
            .collect();
        format!("{}: {}", var.map_or("no input", |v| &**v), shown.join(", "))
    }

    /// The pieces of a treap in order, each `(lo, hi, a, b)` with the maps above it applied.
    /// The stack is explicit, so a deep treap does not overflow the thread's.
    fn treap_pieces(root: &Tree) -> Vec<(End, End, Int, Int)> {
        let mut out = Vec::new();
        let mut stack: Vec<(&PaNode, Tag, bool)> = Vec::new();
        if let Some(n) = root {
            stack.push((n, Tag::ID, false));
        }
        while let Some((n, f, left_done)) = stack.pop() {
            let below = n.tag.then(&f);
            if !left_done {
                stack.push((n, f, true));
                if let Some(l) = &n.left {
                    stack.push((l, below, false));
                }
                continue;
            }
            let (a, b) = f.line(&n.a, &n.b);
            out.push((n.lo.clone(), n.hi.clone(), a, b));
            if let Some(r) = &n.right {
                stack.push((r, below, false));
            }
        }
        out
    }

    /// The summaries over every class of remainders, shown as the number of classes and each
    /// class's summary ([`ByClass::get`]).
    fn by_class_shown(c: &ByClass) -> String {
        let classes: Vec<String> = (0..c.n)
            .map(|i| c.get(i).map_or_else(|| "none".into(), |p| pa_shown(&p)))
            .collect();
        format!("{} classes: {}", c.n, classes.join(" | "))
    }

    /// Whether `a` and `b` are the same text but for the numbers of auxiliary atoms (`q1`),
    /// each number in one standing for one in the other.
    fn renamed(a: &str, b: &str) -> bool {
        fn parts(s: &str) -> Vec<Result<&str, u64>> {
            let (mut out, mut from, bytes) = (Vec::new(), 0, s.as_bytes());
            let mut i = 0;
            while i < bytes.len() {
                let start = i == 0 || !bytes[i - 1].is_ascii_alphanumeric();
                let digits = bytes[i + 1..]
                    .iter()
                    .take_while(|c| c.is_ascii_digit())
                    .count();
                if start && bytes[i] == b'q' && digits > 0 {
                    out.push(Ok(&s[from..i]));
                    out.push(Err(s[i + 1..i + 1 + digits].parse().expect("a number")));
                    i += 1 + digits;
                    from = i;
                } else {
                    i += 1;
                }
            }
            out.push(Ok(&s[from..]));
            out
        }
        let (a, b) = (parts(a), parts(b));
        let (mut there, mut back) = (HashMap::new(), HashMap::new());
        a.len() == b.len()
            && a.iter().zip(&b).all(|(x, y)| match (x, y) {
                (Ok(x), Ok(y)) => x == y,
                (Err(m), Err(n)) => {
                    *there.entry(m).or_insert(n) == n && *back.entry(n).or_insert(m) == m
                }
                _ => false,
            })
    }

    fn fwd_same(a: &Fwd, b: &Fwd) -> bool {
        (&a.ints, a.bools, a.fails, a.other) == (&b.ints, b.bools, b.fails, b.other)
    }

    fn res_same(a: &Res, b: &Res) -> bool {
        (&a.dom, a.none, a.exact) == (&b.dom, b.none, b.exact)
    }

    /// A pseudo-random number generator (xorshift64), so the cases are the same on each run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }
    }

    /// What a name in scope stands for.
    #[derive(Clone, Copy, PartialEq)]
    enum Kind {
        Int,
        Test,
        /// The first parameter of a lambda that is called with itself as that argument.
        Itself,
        /// A parameter of a lambda of a group that calls itself ([`Gen::group`]), which only
        /// [`Gen::again`] reads.
        Fn,
    }

    /// A group of lambdas that call one another ([`Gen::group`]): the parameters that name
    /// them, and the parameter whose value falls at each call.
    struct Frame {
        fns: Vec<Arc<str>>,
        n: Arc<str>,
    }

    /// A random program over the inputs `x` and `y`: tests joined by `&&` and `||`, nested
    /// and mixed, with constants, named tests and integers, calls, lambdas that call
    /// themselves, and parts shared between places.
    struct Gen {
        rng: Rng,
        fresh: u32,
        /// The names in scope, innermost last.
        bound: Vec<(Arc<str>, Kind)>,
        /// Tests made at one place and read again at another: the names in scope where each
        /// was made, which must be in scope where it is read again.
        pool: Vec<(Vec<Arc<str>>, Shared)>,
        /// Whether a test may also be a group of lambdas that call one another, or a call of
        /// one of them; [`Gen::new`] makes it false, so the programs are as before.
        rec: bool,
        /// The groups whose lambdas may be called here: those whose step is being made.
        frames: Vec<Frame>,
        /// Whether a test may also compare a chain of `if`s over one input with a constant
        /// ([`Gen::chain`]); [`Gen::new`] makes it false, so the programs are as before.
        chains: bool,
        /// Whether a `&&` may also be written `if a { b } else { false }`, as the elaborator
        /// writes it ([`Walk::and_if`]); [`Gen::new`] makes it false, so the programs are as
        /// before.
        and_ifs: bool,
        /// Whether a `||` may also be written `if a { true } else { b }`, as the elaborator
        /// writes it ([`Walk::or_if`]); [`Gen::new`] makes it false, so the programs are as
        /// before.
        or_ifs: bool,
    }

    impl Gen {
        fn new(seed: u64, rec: bool) -> Self {
            Gen {
                rng: Rng(seed),
                fresh: 0,
                bound: Vec::new(),
                pool: Vec::new(),
                rec,
                frames: Vec::new(),
                chains: false,
                and_ifs: false,
                or_ifs: false,
            }
        }

        /// `a p b`, a `&&` written as the elaborator writes it half the time where `and_ifs`, and
        /// a `||` half the time where `or_ifs`.
        fn join(&mut self, p: Prim, a: Term, b: Term) -> Term {
            if p == Prim::And && self.and_ifs && self.rng.below(2) == 0 {
                let no = Term::Lit(Value::Bool(false));
                return Term::If(Shared::new(a), Shared::new(b), Shared::new(no));
            }
            if p == Prim::Or && self.or_ifs && self.rng.below(2) == 0 {
                let yes = Term::Lit(Value::Bool(true));
                return Term::If(Shared::new(a), Shared::new(yes), Shared::new(b));
            }
            Term::Prim(p, vec![a, b])
        }

        fn name(&mut self) -> Arc<str> {
            self.fresh += 1;
            format!("v{}", self.fresh).into()
        }

        fn some(&mut self, kind: Kind) -> Option<Arc<str>> {
            let of: Vec<Arc<str>> = (self.bound.iter())
                .filter(|(_, k)| *k == kind)
                .map(|(n, _)| n.clone())
                .collect();
            (!of.is_empty()).then(|| of[self.rng.below(of.len() as u64) as usize].clone())
        }

        fn int(&mut self, d: u32) -> Term {
            let lit = |n: i64| Term::Lit(Value::Int(n));
            match self.rng.below(if d == 0 { 3 } else { 7 }) {
                0 => Term::Var(if self.rng.below(2) == 0 { "x" } else { "y" }.into()),
                1 => lit(self.rng.below(7) as i64 - 3),
                2 => Term::Var(self.some(Kind::Int).unwrap_or_else(|| "x".into())),
                3 => Term::Prim(Prim::Add, vec![self.int(d - 1), self.int(d - 1)]),
                4 => Term::Prim(Prim::Sub, vec![self.int(d - 1), self.int(d - 1)]),
                5 => Term::Prim(
                    Prim::Mul,
                    vec![lit(self.rng.below(5) as i64 - 2), self.int(d - 1)],
                ),
                _ => {
                    let p = if self.rng.below(2) == 0 {
                        Prim::Min
                    } else {
                        Prim::Max
                    };
                    Term::Prim(p, vec![self.int(d - 1), self.int(d - 1)])
                }
            }
        }

        fn cmp(&mut self, d: u32) -> Term {
            let ps = [Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge, Prim::Eq, Prim::Ne];
            let p = ps[self.rng.below(6) as usize];
            Term::Prim(p, vec![self.int(d), self.int(d)])
        }

        fn shared(&mut self, d: u32) -> Shared {
            let here: Vec<Arc<str>> = self.bound.iter().map(|(n, _)| n.clone()).collect();
            let fits: Vec<usize> = (0..self.pool.len())
                .filter(|&i| here.starts_with(&self.pool[i].0))
                .collect();
            if !fits.is_empty() && self.rng.below(3) == 0 {
                let i = fits[self.rng.below(fits.len() as u64) as usize];
                return self.pool[i].1.clone();
            }
            let s = Shared::new(self.test(d));
            self.pool.push((here, s.clone()));
            s
        }

        fn within(&mut self, x: Arc<str>, kind: Kind, f: impl FnOnce(&mut Self) -> Term) -> Term {
            self.bound.push((x, kind));
            let t = f(self);
            self.bound.pop();
            t
        }

        fn test(&mut self, d: u32) -> Term {
            if d == 0 {
                return match self.rng.below(4) {
                    0 => Term::Lit(Value::Bool(self.rng.below(2) == 0)),
                    1 => match self.some(Kind::Test) {
                        Some(n) => Term::Var(n),
                        None => self.cmp(1),
                    },
                    _ => self.cmp(1),
                };
            }
            let d = d - 1;
            let lit = |n: i64| Term::Lit(Value::Int(n));
            if self.chains && self.rng.below(4) == 0 {
                return self.chain_test();
            }
            if self.rec {
                match self.rng.below(6) {
                    0 if !self.frames.is_empty() => return self.again(d),
                    1 if !self.frames.is_empty() => return self.named_again(d),
                    2 => return self.group(d),
                    _ => {}
                }
            }
            match self.rng.below(20) {
                0 | 1 => self.cmp(2),
                2 => Term::Lit(Value::Bool(self.rng.below(2) == 0)),
                // A test with a constant value that is no literal.
                3 => Term::Prim(
                    Prim::Lt,
                    vec![lit(self.rng.below(3) as i64), lit(self.rng.below(3) as i64)],
                ),
                4 => Term::Prim(Prim::Not, vec![self.test(d)]),
                5..=9 => {
                    let p = if self.rng.below(2) == 0 {
                        Prim::And
                    } else {
                        Prim::Or
                    };
                    let (a, b) = (self.test(d), self.test(d));
                    self.join(p, a, b)
                }
                10 | 18 | 19 => match self.some(Kind::Test) {
                    Some(n) => Term::Var(n),
                    None => self.cmp(2),
                },
                11 => {
                    let (x, e) = (self.name(), self.shared(d));
                    let b = self.within(x.clone(), Kind::Test, |g| g.test(d));
                    Term::Let(x, e, Shared::new(b))
                }
                12 => {
                    let (x, e) = (self.name(), Shared::new(self.int(2)));
                    let b = self.within(x.clone(), Kind::Int, |g| g.test(d));
                    Term::Let(x, e, Shared::new(b))
                }
                13 => Term::If(self.shared(d), self.shared(d), self.shared(d)),
                14 => {
                    let x = self.name();
                    let b = self.within(x.clone(), Kind::Int, |g| g.test(d));
                    let f = Term::Lam(vec![x], Shared::new(b));
                    Term::App(Shared::new(f), vec![self.int(2)])
                }
                15 => {
                    let p = if self.rng.below(2) == 0 {
                        Prim::And
                    } else {
                        Prim::Or
                    };
                    Term::App(
                        Shared::new(Term::PrimFn(p)),
                        vec![self.test(d), self.test(d)],
                    )
                }
                16 => match self.some(Kind::Itself) {
                    Some(g) => Term::App(
                        Shared::new(Term::Var(g.clone())),
                        vec![Term::Var(g), self.int(2)],
                    ),
                    None => Term::Prim(Prim::Eq, vec![self.test(d), self.test(d)]),
                },
                _ => self.itself(d),
            }
        }

        /// Named tests, each a chain of comparisons such as a limit or an exemption, and a
        /// chain over them: `l1 = a && (b && c); ...; l1 || (l2 && d)`.
        fn named(&mut self) -> Term {
            let k = 1 + self.rng.below(4) as usize;
            let mut lets = Vec::with_capacity(k);
            for _ in 0..k {
                let p = if self.rng.below(2) == 0 {
                    Prim::And
                } else {
                    Prim::Or
                };
                let (a, b) = (self.cmp(1), self.cmp(1));
                let inner = self.join(p, a, b);
                let a = self.cmp(1);
                let rhs = self.join(p, a, inner);
                let x = self.name();
                self.bound.push((x.clone(), Kind::Test));
                lets.push((x, Shared::new(rhs)));
            }
            let p = if self.rng.below(2) == 0 {
                Prim::And
            } else {
                Prim::Or
            };
            let (a, b) = (self.test(3), self.test(3));
            let mut t = self.join(p, a, b);
            for (x, rhs) in lets.into_iter().rev() {
                self.bound.pop();
                t = Term::Let(x, rhs, Shared::new(t));
            }
            t
        }

        /// `w(w, n)` with `w = (g, n) -> body`, the body a test that may call `g(g, ..)`.
        /// `chain op c`, for a chain of one to four levels ([`Gen::chain`]) and a constant `c`:
        /// the comparison a test asks true or false asks the chain for its values on a ray,
        /// which its summary ([`Pa`]) answers.
        fn chain_test(&mut self) -> Term {
            let ps = [Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge, Prim::Eq, Prim::Ne];
            let p = ps[self.rng.below(6) as usize];
            let k = 1 + self.rng.below(4) as usize;
            let c = self.rng.below(17) as i64 - 8;
            Term::Prim(p, vec![self.chain(k, true), Term::Lit(Value::Int(c))])
        }

        /// A chain of `k` `if`s over one input: `t0` is the input, the input moved or
        /// reflected, or a constant, and `tj = if guard { arm(t(j-1)) } else { arm(t(j-1)) }`,
        /// both arms reading the one term `t(j-1)`. The guards of a chain compare the input
        /// with constants, or take its remainder by one modulus, 2 or 3, which splits it by
        /// class ([`ByClass`]), or mix the two; within a group's step a guard may also call a
        /// lambda of the group ([`Gen::again`]). Each arm is the term, the term moved, reflected
        /// or negated, its `min` or `max` with a constant, or where `scale` a multiple of it,
        /// so that a chain of many levels keeps its values small.
        fn chain(&mut self, k: usize, scale: bool) -> Term {
            let lit = |n: i64| Term::Lit(Value::Int(n));
            let x: Term = match self.rng.below(5) {
                0 => Term::Var("y".into()),
                1 => Term::Var(self.some(Kind::Int).unwrap_or_else(|| "x".into())),
                _ => Term::Var("x".into()),
            };
            let mut t = match self.rng.below(6) {
                0 => Term::Prim(
                    Prim::Add,
                    vec![x.clone(), lit(self.rng.below(7) as i64 - 3)],
                ),
                1 => Term::Prim(
                    Prim::Sub,
                    vec![lit(self.rng.below(7) as i64 - 3), x.clone()],
                ),
                2 => lit(self.rng.below(7) as i64 - 3),
                _ => x.clone(),
            };
            let (guards, m) = (self.rng.below(3), 2 + self.rng.below(2) as i64);
            for _ in 0..k {
                let c = self.rng.below(13) as i64 - 6;
                let by_class = match guards {
                    0 => false,
                    1 => true,
                    _ => self.rng.below(2) == 0,
                };
                let g = if !self.frames.is_empty() && self.rng.below(4) == 0 {
                    // A call of a lambda being read, so that the summary is made below a stop.
                    self.again(0)
                } else if by_class {
                    let p = [Prim::Eq, Prim::Ne][self.rng.below(2) as usize];
                    let r = Term::Prim(Prim::Mod, vec![x.clone(), lit(m)]);
                    Term::Prim(p, vec![r, lit(c.rem_euclid(m))])
                } else {
                    let ps = [Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge, Prim::Eq, Prim::Ne];
                    Term::Prim(ps[self.rng.below(6) as usize], vec![x.clone(), lit(c)])
                };
                let shared = Shared::new(t);
                let arm = |g: &mut Self| {
                    let s = (*shared).clone();
                    let c = g.rng.below(13) as i64 - 6;
                    match g.rng.below(if scale { 9 } else { 8 }) {
                        0 | 1 => s,
                        2 => Term::Prim(Prim::Add, vec![s, lit(c)]),
                        3 => Term::Prim(Prim::Sub, vec![lit(c), s]),
                        4 => Term::Prim(Prim::Neg, vec![s]),
                        5 => Term::Prim(Prim::Min, vec![s, lit(c)]),
                        6 => Term::Prim(Prim::Max, vec![s, lit(c)]),
                        7 => Term::Prim(Prim::Sub, vec![s, lit(c)]),
                        _ => Term::Prim(Prim::Mul, vec![lit(c.clamp(-2, 2)), s]),
                    }
                };
                let (a, b) = (arm(self), arm(self));
                t = Term::If(Shared::new(g), Shared::new(a), Shared::new(b));
            }
            t
        }

        fn itself(&mut self, d: u32) -> Term {
            let (g, n) = (self.name(), self.name());
            let body = self.within(g.clone(), Kind::Itself, |s| {
                s.within(n.clone(), Kind::Int, |s| s.test(d))
            });
            let w = Term::Lam(vec![g, n], Shared::new(body));
            Term::App(Shared::new(w.clone()), vec![w, self.int(2)])
        }

        /// `f_j(f_1, .., f_k, e)` with `f_i = (f_1, .., f_k, n) -> if n <= 0 { base_i } else
        /// { step_i }` and k one or two, the lambdas bound by `let` or written in place:
        /// functions that call themselves or each other, each call with a lower `n`
        /// ([`Gen::again`]). A base calls none of its group, nor does anything inside it, so
        /// each run of the group ends, unless a shared test made in one lambda's step is
        /// read again in the other's base, where its names are bound alike.
        fn group(&mut self, d: u32) -> Term {
            let k = 1 + self.rng.below(2) as usize;
            let fns: Vec<Arc<str>> = (0..k).map(|_| self.name()).collect();
            let n = self.name();
            let mut lams = Vec::with_capacity(k);
            for _ in 0..k {
                let depth = self.bound.len();
                self.bound.extend(fns.iter().map(|f| (f.clone(), Kind::Fn)));
                self.bound.push((n.clone(), Kind::Int));
                let base = self.test(d);
                self.frames.push(Frame {
                    fns: fns.clone(),
                    n: n.clone(),
                });
                let step = self.test(d);
                self.frames.pop();
                self.bound.truncate(depth);
                let guard = Term::Prim(
                    Prim::Le,
                    vec![Term::Var(n.clone()), Term::Lit(Value::Int(0))],
                );
                let body = Term::If(Shared::new(guard), Shared::new(base), Shared::new(step));
                let mut ps = fns.clone();
                ps.push(n.clone());
                lams.push(Term::Lam(ps, Shared::new(body)));
            }
            let j = self.rng.below(k as u64) as usize;
            let arg = self.int(2);
            if self.rng.below(2) == 0 {
                let mut args = lams.clone();
                args.push(arg);
                return Term::App(Shared::new(lams[j].clone()), args);
            }
            let names: Vec<Arc<str>> = (0..k).map(|_| self.name()).collect();
            let mut args: Vec<Term> = names.iter().map(|m| Term::Var(m.clone())).collect();
            args.push(arg);
            let mut t = Term::App(Shared::new(Term::Var(names[j].clone())), args);
            for (m, l) in names.iter().zip(lams).rev() {
                t = Term::Let(m.clone(), Shared::new(l), Shared::new(t));
            }
            t
        }

        /// `let s = e in (s && t) || ((v) -> u && s)(e2)`, `||` and `&&` either way round: `e`
        /// a call of a lambda of the group ([`Gen::again`]) joined with a comparison, read
        /// here and again within a call whose argument `e2` may read the inputs, and `u` a test
        /// that may read `v`.
        fn named_again(&mut self, d: u32) -> Term {
            let p = if self.rng.below(2) == 0 {
                Prim::And
            } else {
                Prim::Or
            };
            let e = Term::Prim(p, vec![self.again(d), self.cmp(1)]);
            let s = self.name();
            let b = self.within(s.clone(), Kind::Test, |g| {
                let q = if g.rng.below(2) == 0 {
                    Prim::And
                } else {
                    Prim::Or
                };
                let here = Term::Prim(q, vec![Term::Var(s.clone()), g.test(d)]);
                let v = g.name();
                let u = g.within(v.clone(), Kind::Int, |g| {
                    Term::Prim(q, vec![g.test(d), Term::Var(s.clone())])
                });
                let call = Term::App(
                    Shared::new(Term::Lam(vec![v], Shared::new(u))),
                    vec![g.int(2)],
                );
                Term::Prim(p, vec![here, call])
            });
            Term::Let(s, Shared::new(e), Shared::new(b))
        }

        /// A call of a lambda of a group whose step is being made, any number of groups out,
        /// with its `n` lowered: `n - 1`, `n - 2` or `min(n - 1, e)`.
        fn again(&mut self, d: u32) -> Term {
            let i = self.rng.below(self.frames.len() as u64) as usize;
            let (fns, n) = (self.frames[i].fns.clone(), self.frames[i].n.clone());
            let f = fns[self.rng.below(fns.len() as u64) as usize].clone();
            let less = |c: i64| {
                Term::Prim(
                    Prim::Sub,
                    vec![Term::Var(n.clone()), Term::Lit(Value::Int(c))],
                )
            };
            let arg = match self.rng.below(3) {
                0 => less(1),
                1 => less(2),
                _ => Term::Prim(Prim::Min, vec![less(1), self.int(d.min(1))]),
            };
            let mut args: Vec<Term> = fns.iter().map(|g| Term::Var(g.clone())).collect();
            args.push(arg);
            Term::App(Shared::new(Term::Var(f)), args)
        }
    }

    /// The formula's tree as built, each node and its parts: compare, hash and show read a
    /// kept part as flattened, and this must not.
    fn built(f: &Formula) -> String {
        let parts = |gs: &[Formula]| gs.iter().map(built).collect::<Vec<_>>().join(", ");
        match f {
            Formula::Con(c) => format!("({c})"),
            Formula::Not(g) => format!("!{}", built(g)),
            Formula::And(gs) => format!("and[{}]", parts(gs)),
            Formula::Or(gs) => format!("or[{}]", parts(gs)),
        }
    }

    /// Whether `f` holds a conjunction as a part of a conjunction, or a disjunction of a
    /// disjunction.
    fn kept(f: &Formula) -> bool {
        match f {
            Formula::Con(_) => false,
            Formula::Not(g) => kept(g),
            Formula::And(gs) => gs.iter().any(|g| matches!(g, Formula::And(_)) || kept(g)),
            Formula::Or(gs) => gs.iter().any(|g| matches!(g, Formula::Or(_)) || kept(g)),
        }
    }

    /// What one translation of a term gives and leaves behind.
    #[derive(PartialEq, Debug)]
    struct Seen {
        formula: Option<String>,
        defs: Vec<String>,
        /// The formula memo, each entry's formula built.
        memo: BTreeMap<At, Option<String>>,
        /// The `&&` and `||` primitive nodes, and the `if`s that are one ([`Walk::and_if`],
        /// [`Walk::or_if`]).
        chains: BTreeSet<Tid>,
        /// Whether the formula holds a conjunction kept whole in a conjunction, or a disjunction
        /// in a disjunction.
        kept: bool,
        cut: usize,
        /// The entries made and not undone, other than those of the formula of a `&&` or `||`.
        log: usize,
        /// The `&&` and `||` nodes whose formula entry was made and not undone, kept or not:
        /// an entry made below a stop is dropped when the stack falls below where it began.
        chain_log: BTreeSet<At>,
        lin: usize,
        stops: usize,
    }

    fn domains() -> Domains {
        let r = || IntervalSet::range(End::of(-6), End::of(6));
        [("x".into(), r()), ("y".into(), r())].into()
    }

    /// The formula of `t` as the linear stage translates it, with `&&` and `||` joined two at
    /// a time where `old`.
    fn translate(t: &Term, old: bool) -> Seen {
        TWO_AT_A_TIME.set(old);
        let mut tx = Tx::new();
        let root = tx.terms.add(t);
        tx.start(&domains(), Marks::default());
        let mut tr = Tr::new(false);
        let f = tx.formula(&mut tr, root, ROOT);
        TWO_AT_A_TIME.set(false);
        let chains: BTreeSet<Tid> = (0..tx.terms.nodes.len() as Tid)
            .filter(|&u| match tx.node(u) {
                Node::Prim(Prim::And | Prim::Or, _) => true,
                Node::If(_, a, b) => {
                    matches!(tx.node(b), Node::Bool(false))
                        || matches!(tx.node(a), Node::Bool(true))
                }
                _ => false,
            })
            .collect();
        let chain = |e: &Logged| match e {
            Logged::Formula(k) if chains.contains(&k.0) => Some(*k),
            _ => None,
        };
        let log = tx
            .run
            .memo
            .log
            .iter()
            .filter(|e| chain(e).is_none())
            .count();
        let chain_log = tx.run.memo.log.iter().filter_map(chain).collect();
        Seen {
            formula: f.as_ref().map(built),
            kept: f.as_ref().is_some_and(kept),
            defs: (tr.defs.iter())
                .map(|(n, w, f)| format!("{n} {w} {}", built(f)))
                .collect(),
            memo: (tx.run.memo.formula.iter())
                .map(|(k, (v, _))| (*k, v.as_ref().map(built)))
                .collect(),
            chains,
            cut: tx.cx.cut,
            log,
            chain_log,
            lin: tx.run.memo.lin.len(),
            stops: tx.run.stops.len(),
        }
    }

    /// The number of tests the rounds of one seed are split into, so that each test takes
    /// under 30 s at a load average of 90 on 32 cores (four parts took up to 40 s there).
    const PARTS: usize = 8;

    /// The chain translator against the translation two at a time, on the rounds of part
    /// `part` ([`PARTS`]) of 4,000 random programs of one seed: an eighth of them in a row, as
    /// every fourth round also builds preimages, so that rounds taken by remainder would put
    /// all of those in two parts. Every round's program is generated, so that a round checks
    /// the same program whichever part it is in.
    fn joins_as_two_at_a_time(part: usize) {
        joins_as_two_at_a_time_from(Gen::new(0x9e37_79b9_7f4a_7c15, false), part);
    }

    /// [`joins_as_two_at_a_time`], with programs whose `&&` is written half the time as the
    /// elaborator writes it, `if a { b } else { false }` ([`Walk::and_if`];
    /// PREIMAGE-and-chain), and another seed.
    fn joins_ifs_as_two_at_a_time(part: usize) {
        let mut g = Gen::new(0xd1b5_4a32_d192_ed03, false);
        g.and_ifs = true;
        joins_as_two_at_a_time_from(g, part);
    }

    /// A program of a round of the comparison tests: a test that calls itself, named tests,
    /// or a `&&` or `||` of two tests.
    fn program(g: &mut Gen) -> Term {
        g.pool.clear();
        match g.rng.below(4) {
            0 => g.itself(4),
            1 => g.named(),
            _ => {
                let p = if g.rng.below(2) == 0 {
                    Prim::And
                } else {
                    Prim::Or
                };
                let (a, b) = (g.test(4), g.test(4));
                g.join(p, a, b)
            }
        }
    }

    fn joins_as_two_at_a_time_from(mut g: Gen, part: usize) {
        let (mut some, mut none, mut kept, mut stopped, mut fewer) = (0, 0, 0, 0, 0);
        let only = part * 4000 / PARTS..(part + 1) * 4000 / PARTS;
        for round in 0..only.end {
            let t = program(&mut g);
            if round < only.start {
                continue;
            }
            let (old, new) = (translate(&t, true), translate(&t, false));
            assert_eq!(new.formula, old.formula, "round {round}: {t:?}");
            assert_eq!(new.defs, old.defs, "round {round}: {t:?}");
            assert_eq!(new.cut, old.cut, "round {round}: {t:?}");
            assert_eq!(
                (new.lin, new.stops),
                (old.lin, old.stops),
                "round {round}: {t:?}"
            );
            // The old translation also remembered each inner `&&` of a chain; every other
            // entry is the same.
            for (k, v) in &new.memo {
                assert_eq!(
                    old.memo.get(k),
                    Some(v),
                    "round {round}, entry {k:?}: {t:?}"
                );
            }
            let extra: Vec<&At> = old
                .memo
                .keys()
                .filter(|k| !new.memo.contains_key(k))
                .collect();
            for k in &extra {
                assert!(
                    old.chains.contains(&k.0),
                    "round {round}, entry {k:?}: {t:?}"
                );
            }
            // Every other entry made is the same, and every entry the new translation made for
            // a chain the old one made too, as the formula of the chain's top.
            assert_eq!(old.log, new.log, "round {round}: {t:?}");
            assert!(
                new.chain_log.is_subset(&old.chain_log),
                "round {round}: {t:?}"
            );
            for k in &extra {
                assert!(
                    old.chain_log.contains(k),
                    "round {round}, entry {k:?}: {t:?}"
                );
            }
            fewer += usize::from(!extra.is_empty());
            // The whole preimage, with the relation's formula as built.
            let doms = domains();
            for w in [true, false].into_iter().filter(|_| round % 4 == 0) {
                TWO_AT_A_TIME.set(true);
                let po = preimage(&t, &doms, &Demand::Bool(w));
                TWO_AT_A_TIME.set(false);
                let pn = preimage(&t, &doms, &Demand::Bool(w));
                assert_eq!(pn, po, "round {round}, demand {w}: {t:?}");
                let rel = |p: &Preimage| p.relation.as_ref().map(|r| built(&r.body));
                assert_eq!(rel(&pn), rel(&po), "round {round}, demand {w}: {t:?}");
            }
            match &new.formula {
                Some(_) if new.kept => kept += 1,
                Some(_) => some += 1,
                None => none += 1,
            }
            stopped += usize::from(new.stops > 0 || new.cut != usize::MAX);
        }
        eprintln!("some {some}, kept {kept}, none {none}, stopped {stopped}, fewer {fewer}");
        // Formulas, kept parts, translations that fail, stops and dropped entries all occur.
        // Each part has more than its share, rounded down, of the counts the 4,000 rounds had
        // to have, so together the parts have more: some > 500, kept > 20, none > 100,
        // stopped > 50 and fewer > 500.
        let n = PARTS;
        assert!(some > 500 / n && kept > 20 / n && none > 100 / n);
        assert!(stopped > 50 / n && fewer > 500 / n);
    }

    #[test]
    fn the_translator_joins_a_chain_as_it_joined_it_two_at_a_time_1() {
        joins_as_two_at_a_time(0);
    }

    #[test]
    fn the_translator_joins_a_chain_as_it_joined_it_two_at_a_time_2() {
        joins_as_two_at_a_time(1);
    }

    #[test]
    fn the_translator_joins_a_chain_as_it_joined_it_two_at_a_time_3() {
        joins_as_two_at_a_time(2);
    }

    #[test]
    fn the_translator_joins_a_chain_as_it_joined_it_two_at_a_time_4() {
        joins_as_two_at_a_time(3);
    }

    #[test]
    fn the_translator_joins_a_chain_as_it_joined_it_two_at_a_time_5() {
        joins_as_two_at_a_time(4);
    }

    #[test]
    fn the_translator_joins_a_chain_as_it_joined_it_two_at_a_time_6() {
        joins_as_two_at_a_time(5);
    }

    #[test]
    fn the_translator_joins_a_chain_as_it_joined_it_two_at_a_time_7() {
        joins_as_two_at_a_time(6);
    }

    #[test]
    fn the_translator_joins_a_chain_as_it_joined_it_two_at_a_time_8() {
        joins_as_two_at_a_time(7);
    }

    #[test]
    fn the_translator_joins_a_chain_of_ifs_as_it_joined_it_two_at_a_time_1() {
        joins_ifs_as_two_at_a_time(0);
    }

    #[test]
    fn the_translator_joins_a_chain_of_ifs_as_it_joined_it_two_at_a_time_2() {
        joins_ifs_as_two_at_a_time(1);
    }

    #[test]
    fn the_translator_joins_a_chain_of_ifs_as_it_joined_it_two_at_a_time_3() {
        joins_ifs_as_two_at_a_time(2);
    }

    #[test]
    fn the_translator_joins_a_chain_of_ifs_as_it_joined_it_two_at_a_time_4() {
        joins_ifs_as_two_at_a_time(3);
    }

    #[test]
    fn the_translator_joins_a_chain_of_ifs_as_it_joined_it_two_at_a_time_5() {
        joins_ifs_as_two_at_a_time(4);
    }

    #[test]
    fn the_translator_joins_a_chain_of_ifs_as_it_joined_it_two_at_a_time_6() {
        joins_ifs_as_two_at_a_time(5);
    }

    #[test]
    fn the_translator_joins_a_chain_of_ifs_as_it_joined_it_two_at_a_time_7() {
        joins_ifs_as_two_at_a_time(6);
    }

    #[test]
    fn the_translator_joins_a_chain_of_ifs_as_it_joined_it_two_at_a_time_8() {
        joins_ifs_as_two_at_a_time(7);
    }

    /// Chains of `&&` written as `if`s that test one name again, hold one `if` in two places,
    /// mix `if`s with the primitive, hold a `||` or a constant, or end in a disjunction: the
    /// same formula, definitions, entries and preimages as two at a time (PREIMAGE-and-chain).
    #[test]
    fn chains_of_ifs_on_repeated_names_and_shared_parts_join_as_two_at_a_time() {
        use Prim::{And, Eq, Ge, Le, Ne};
        let n = |s: &str| Term::Var(s.into());
        let c = |p: Prim, s: &str, i: i64| Term::Prim(p, vec![n(s), Term::Lit(Value::Int(i))]);
        let and = |a: Term, b: Term| {
            let no = Shared::new(Term::Lit(Value::Bool(false)));
            Term::If(Shared::new(a), Shared::new(b), no)
        };
        let or = |a: Term, b: Term| Term::Prim(Prim::Or, vec![a, b]);
        let repeated = [c(Ge, "x", 1), c(Le, "y", 3), c(Ge, "x", 0), c(Ge, "x", 1)]
            .into_iter()
            .fold(c(Ge, "x", 0), and);
        let s = Shared::new(and(c(Ge, "x", 1), c(Ge, "y", 0)));
        let twice = Term::If(
            Shared::new(and(
                Term::If(s.clone(), Shared::new(c(Le, "x", 4)), s.clone()),
                c(Ne, "y", 2),
            )),
            s.clone(),
            Shared::new(Term::Lit(Value::Bool(false))),
        );
        let mixed = and(
            Term::Prim(
                And,
                vec![and(c(Ge, "x", -2), c(Le, "y", 5)), c(Ge, "x", -2)],
            ),
            and(or(c(Ge, "x", 3), c(Le, "y", -3)), c(Ne, "x", 4)),
        );
        let constant = and(and(c(Ge, "x", 7), c(Ge, "y", 1)), c(Le, "x", 2));
        let ends_in_or = and(
            and(
                Term::Lit(Value::Bool(true)),
                or(c(Eq, "x", 1), c(Eq, "y", 1)),
            ),
            or(c(Eq, "x", 2), c(Eq, "x", 1)),
        );
        for t in [repeated, twice, mixed, constant, ends_in_or] {
            let (old, new) = (translate(&t, true), translate(&t, false));
            assert_eq!(new.formula, old.formula, "{t:?}");
            assert!(new.formula.is_some(), "{t:?}");
            assert_eq!(new.defs, old.defs, "{t:?}");
            assert_eq!(new.log, old.log, "{t:?}");
            for (k, v) in &new.memo {
                assert_eq!(old.memo.get(k), Some(v), "entry {k:?}: {t:?}");
            }
            for w in [true, false] {
                TWO_AT_A_TIME.set(true);
                let po = preimage(&t, &domains(), &Demand::Bool(w));
                TWO_AT_A_TIME.set(false);
                assert_eq!(preimage(&t, &domains(), &Demand::Bool(w)), po, "{w}: {t:?}");
            }
        }
    }

    /// [`joins_as_two_at_a_time`], with programs whose `&&` and `||` are each written half the
    /// time as the elaborator writes them, `if a { b } else { false }` and
    /// `if a { true } else { b }` ([`Walk::or_if`]; PREIMAGE-or-chain), and another seed.
    fn joins_or_ifs_as_two_at_a_time(part: usize) {
        let mut g = Gen::new(0x2545_f491_4f6c_dd1d, false);
        g.and_ifs = true;
        g.or_ifs = true;
        joins_as_two_at_a_time_from(g, part);
    }

    #[test]
    fn the_translator_joins_a_chain_of_or_ifs_as_it_joined_it_two_at_a_time_1() {
        joins_or_ifs_as_two_at_a_time(0);
    }

    #[test]
    fn the_translator_joins_a_chain_of_or_ifs_as_it_joined_it_two_at_a_time_2() {
        joins_or_ifs_as_two_at_a_time(1);
    }

    #[test]
    fn the_translator_joins_a_chain_of_or_ifs_as_it_joined_it_two_at_a_time_3() {
        joins_or_ifs_as_two_at_a_time(2);
    }

    #[test]
    fn the_translator_joins_a_chain_of_or_ifs_as_it_joined_it_two_at_a_time_4() {
        joins_or_ifs_as_two_at_a_time(3);
    }

    #[test]
    fn the_translator_joins_a_chain_of_or_ifs_as_it_joined_it_two_at_a_time_5() {
        joins_or_ifs_as_two_at_a_time(4);
    }

    #[test]
    fn the_translator_joins_a_chain_of_or_ifs_as_it_joined_it_two_at_a_time_6() {
        joins_or_ifs_as_two_at_a_time(5);
    }

    #[test]
    fn the_translator_joins_a_chain_of_or_ifs_as_it_joined_it_two_at_a_time_7() {
        joins_or_ifs_as_two_at_a_time(6);
    }

    #[test]
    fn the_translator_joins_a_chain_of_or_ifs_as_it_joined_it_two_at_a_time_8() {
        joins_or_ifs_as_two_at_a_time(7);
    }

    /// The formula of `t` and the definitions of its auxiliary variables, with each
    /// `if g { true } else { b }` read as any other `if` where `as_if`, as before
    /// [`Walk::or_if`].
    fn formula_of(t: &Term, as_if: bool) -> (Option<Formula>, Vec<Formula>) {
        OR_IF_AS_IF.set(as_if);
        let mut tx = Tx::new();
        let root = tx.terms.add(t);
        tx.start(&domains(), Marks::default());
        let mut tr = Tr::new(false);
        let f = tx.formula(&mut tr, root, ROOT);
        OR_IF_AS_IF.set(false);
        (f, tr.defs.into_iter().map(|(_, _, f)| f).collect())
    }

    /// Whether `a` and `b` hold at the same points of [`domains`], each point read with every
    /// auxiliary variable at the one value its definition in `defs` gives it there, found by
    /// the solver; a point where the definitions do not hold is no point of either.
    fn same_points(a: &Formula, b: &Formula, defs: &[Formula]) -> Result<bool, Refusal> {
        let sym = |x: &str| presburger::Atom::Sym(x.into());
        for x in -6..=6i64 {
            for y in -6..=6i64 {
                let at = [(sym("x"), Int::from(x)), (sym("y"), Int::from(y))];
                let mut m: presburger::Model = at.iter().cloned().collect();
                if !defs.is_empty() {
                    let mut fixed: Vec<Formula> = defs.to_vec();
                    for (v, k) in &at {
                        let c = Con::eq(&Lin::atom(v.clone()), &Lin::constant(k.clone()));
                        fixed.push(Formula::Con(c));
                    }
                    match presburger::satisfiable(&Formula::and(fixed))? {
                        Some(found) => m.extend(found),
                        None => continue,
                    }
                    m.extend(at.iter().cloned());
                }
                if a.holds(&m) != b.holds(&m) {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// Formulas and preimages of `t` with `if g { true } else { b }` read as `g || b`
    /// ([`Walk::or_if`]) and as any other `if`, `g || (!g && b)`: the same definitions, and
    /// the formulas, and the preimages' relations where both have one with the same
    /// definitions, hold at the same points; each preimage holds every point of `x, y` in
    /// `-6..=6` at which the interpreter meets the demand, and only those where it is exact.
    /// The two preimages may still differ, since the hull of a relation and whether the solver
    /// decides it depend on its shape ([`presburger::decide`] does not undo the choice of a
    /// disjunct): gives whether the formulas differ as built, whether the solver decided the
    /// points of each pair compared, and how the preimages differ.
    fn holds_where_it_held_as_ifs(
        t: &Term,
        preimages: bool,
    ) -> (bool, Vec<bool>, Vec<&'static str>) {
        let mut decided = Vec::new();
        let mut same = |a: &Formula, b: &Formula, defs: &[Formula], what: &str| match same_points(
            a, b, defs,
        ) {
            Ok(s) => {
                assert!(s, "{what}: {} and {}: {t:?}", built(a), built(b));
                decided.push(true);
            }
            Err(_) => decided.push(false),
        };
        let (new, old) = (formula_of(t, false), formula_of(t, true));
        let built_all = |fs: &[Formula]| fs.iter().map(built).collect::<Vec<_>>();
        assert_eq!(built_all(&new.1), built_all(&old.1), "{t:?}");
        assert_eq!(new.0.is_some(), old.0.is_some(), "{t:?}");
        let mut changed = false;
        if let (Some(a), Some(b)) = (&new.0, &old.0) {
            changed = built(a) != built(b);
            same(a, b, &new.1, "formula");
        }
        let doms = domains();
        let mut differ = Vec::new();
        for w in [true, false].into_iter().filter(|_| preimages) {
            let d = Demand::Bool(w);
            OR_IF_AS_IF.set(true);
            let po = preimage(t, &doms, &d);
            OR_IF_AS_IF.set(false);
            let pn = preimage(t, &doms, &d);
            let inside = |p: &Preimage, x: i64, y: i64| {
                p.domains["x"].contains(x) && p.domains["y"].contains(y)
            };
            let (mut tighter, mut looser) = (false, false);
            'points: for x in -6..=6 {
                for y in -6..=6 {
                    let Some(v) = run_at(t, (x, y)) else {
                        break 'points;
                    };
                    let met = v.as_ref().is_some_and(|v| d.holds(v));
                    for p in [&pn, &po] {
                        if met {
                            assert!(inside(p, x, y), "demand {w} at {x}, {y}: {t:?}");
                        } else {
                            let fails = !(p.exact && inside(p, x, y));
                            assert!(fails, "demand {w} exact at {x}, {y}: {t:?}");
                        }
                    }
                    tighter |= inside(&po, x, y) && !inside(&pn, x, y);
                    looser |= inside(&pn, x, y) && !inside(&po, x, y);
                }
            }
            differ.extend(
                [
                    (tighter && !looser, "tighter"),
                    (looser && !tighter, "looser"),
                    (looser && tighter, "neither"),
                    (pn.exact && !po.exact, "now exact"),
                    (po.exact && !pn.exact, "no longer exact"),
                    (pn.enumerated != po.enumerated, "enumerated"),
                    (pn.stops != po.stops, "stops"),
                    (pn.refusal.is_some() && po.refusal.is_none(), "refused now"),
                    (
                        po.refusal.is_some() && pn.refusal.is_none(),
                        "no longer refused",
                    ),
                ]
                .into_iter()
                .filter_map(|(b, s)| b.then_some(s)),
            );
            match (&pn.relation, &po.relation) {
                (Some(a), Some(b)) if a.defs == b.defs => {
                    let defs: Vec<Formula> = a.defs.iter().map(|(_, _, f)| f.clone()).collect();
                    same(&a.body, &b.body, &defs, "relation");
                }
                (Some(_), Some(_)) => differ.push("relation definitions"),
                (a, b) if a.is_some() != b.is_some() => differ.push("relation"),
                _ => {}
            }
        }
        (changed, decided, differ)
    }

    /// The number of tests [`or_ifs_hold_where_they_held_as_ifs`] is split into, twice
    /// [`PARTS`]: its rounds cost several times those of the other families, most of it the
    /// comparison of formulas at 169 points ([`same_points`]), and in eight parts each took 28
    /// to 36 s at a load average of 16 to 40 on 32 cores (TEST-preimage-split, 2026-11-09).
    const OR_IF_PARTS: usize = 16;

    /// The formulas and preimages of part `part` ([`OR_IF_PARTS`]) of 4,000 random programs
    /// whose `&&` and `||` are each written half the time as the elaborator writes them, with
    /// `if g { true } else { b }` read as `g || b` and as before [`Walk::or_if`], when it was
    /// read as any other `if`: [`holds_where_it_held_as_ifs`].
    fn or_ifs_hold_where_they_held_as_ifs(part: usize) {
        let mut g = Gen::new(0x5851_f42d_4c95_7f2d, false);
        g.and_ifs = true;
        g.or_ifs = true;
        let (mut changed, mut decided, mut refused) = (0, 0, 0);
        let mut differ = std::collections::BTreeMap::<&str, usize>::new();
        let only = part * 4000 / OR_IF_PARTS..(part + 1) * 4000 / OR_IF_PARTS;
        for round in 0..only.end {
            let t = program(&mut g);
            if round < only.start {
                continue;
            }
            let (c, d, how) = holds_where_it_held_as_ifs(&t, round % 4 == 0);
            changed += usize::from(c);
            decided += d.iter().filter(|&&d| d).count();
            refused += d.iter().filter(|&&d| !d).count();
            assert!(!how.contains(&"no longer exact"), "{t:?}");
            for h in how {
                *differ.entry(h).or_default() += 1;
            }
        }
        eprintln!("changed {changed}, decided {decided}, refused {refused}, preimages {differ:?}");
        // Each part's 250 rounds have formulas that changed (one in ten at least, as when the
        // parts had 500 rounds and at least 50), and the solver decides nearly every
        // comparison. Over all parts, about 1,000 pairs of preimages, the new shape gave 3
        // tighter domains and 1 looser, 2 fewer refusals and 1 more, and 1 preimage exact that
        // was not.
        assert!(changed * 10 > only.len(), "changed {changed}");
        assert!(
            refused * 50 < decided,
            "decided {decided}, refused {refused}"
        );
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_1() {
        or_ifs_hold_where_they_held_as_ifs(0);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_2() {
        or_ifs_hold_where_they_held_as_ifs(1);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_3() {
        or_ifs_hold_where_they_held_as_ifs(2);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_4() {
        or_ifs_hold_where_they_held_as_ifs(3);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_5() {
        or_ifs_hold_where_they_held_as_ifs(4);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_6() {
        or_ifs_hold_where_they_held_as_ifs(5);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_7() {
        or_ifs_hold_where_they_held_as_ifs(6);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_8() {
        or_ifs_hold_where_they_held_as_ifs(7);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_9() {
        or_ifs_hold_where_they_held_as_ifs(8);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_10() {
        or_ifs_hold_where_they_held_as_ifs(9);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_11() {
        or_ifs_hold_where_they_held_as_ifs(10);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_12() {
        or_ifs_hold_where_they_held_as_ifs(11);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_13() {
        or_ifs_hold_where_they_held_as_ifs(12);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_14() {
        or_ifs_hold_where_they_held_as_ifs(13);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_15() {
        or_ifs_hold_where_they_held_as_ifs(14);
    }

    #[test]
    fn or_ifs_hold_where_they_held_as_ifs_16() {
        or_ifs_hold_where_they_held_as_ifs(15);
    }

    /// Chains of `||` written as `if`s that test one name again, hold one `if` in two places,
    /// mix `if`s with the primitive, hold a `&&` or are held in one, hold a constant, or an
    /// `if g { true } else { false }`: the same formula, definitions, entries and preimages as
    /// two at a time, and the same points and preimages as when such an `if` was read as any
    /// other `if` (PREIMAGE-or-chain).
    #[test]
    fn mixed_chains_of_and_and_or_ifs_on_repeated_names_and_shared_parts() {
        use Prim::{Eq, Ge, Le, Ne, Or};
        let n = |s: &str| Term::Var(s.into());
        let c = |p: Prim, s: &str, i: i64| Term::Prim(p, vec![n(s), Term::Lit(Value::Int(i))]);
        let b = |v: bool| Shared::new(Term::Lit(Value::Bool(v)));
        let and = |a: Term, x: Term| Term::If(Shared::new(a), Shared::new(x), b(false));
        let or = |a: Term, x: Term| Term::If(Shared::new(a), b(true), Shared::new(x));
        let repeated = [c(Ge, "x", 1), c(Le, "y", 3), c(Ge, "x", 0), c(Ge, "x", 1)]
            .into_iter()
            .fold(c(Ge, "x", 0), or);
        let s = Shared::new(or(c(Ge, "x", 1), c(Ge, "y", 0)));
        let twice = Term::If(
            Shared::new(or(
                Term::If(s.clone(), Shared::new(c(Le, "x", 4)), s.clone()),
                c(Ne, "y", 2),
            )),
            b(true),
            s.clone(),
        );
        let mixed = or(
            Term::Prim(Or, vec![or(c(Ge, "x", -2), c(Le, "y", 5)), c(Ge, "x", -2)]),
            or(and(c(Ge, "x", 3), c(Le, "y", -3)), c(Ne, "x", 4)),
        );
        let inside_and = and(
            or(c(Eq, "x", 1), c(Eq, "y", 1)),
            or(and(c(Ge, "x", 0), c(Ge, "y", 0)), c(Eq, "x", 2)),
        );
        let constant = or(
            or(Term::Lit(Value::Bool(false)), c(Ge, "x", 7)),
            or(Term::Lit(Value::Bool(true)), c(Le, "y", 2)),
        );
        let boolish = or(
            Term::If(Shared::new(c(Ge, "x", 2)), b(true), b(false)),
            or(c(Le, "y", -1), c(Eq, "x", 0)),
        );
        let head = Shared::new(or(or(c(Le, "x", -4), c(Ge, "y", 4)), c(Eq, "x", 0)));
        let shared_head = and(
            Term::If(head.clone(), b(true), Shared::new(c(Eq, "y", 3))),
            Term::If(head.clone(), b(true), head.clone()),
        );
        for t in [
            repeated,
            twice,
            mixed,
            inside_and,
            constant,
            boolish,
            shared_head,
        ] {
            let (old, new) = (translate(&t, true), translate(&t, false));
            assert_eq!(new.formula, old.formula, "{t:?}");
            assert!(new.formula.is_some(), "{t:?}");
            assert_eq!(new.defs, old.defs, "{t:?}");
            assert_eq!(new.log, old.log, "{t:?}");
            for (k, v) in &new.memo {
                assert_eq!(old.memo.get(k), Some(v), "entry {k:?}: {t:?}");
            }
            for w in [true, false] {
                TWO_AT_A_TIME.set(true);
                let po = preimage(&t, &domains(), &Demand::Bool(w));
                TWO_AT_A_TIME.set(false);
                assert_eq!(preimage(&t, &domains(), &Demand::Bool(w)), po, "{w}: {t:?}");
            }
            let (_, decided, differ) = holds_where_it_held_as_ifs(&t, true);
            assert!(decided.iter().all(|&d| d), "{t:?}");
            assert_eq!(differ, Vec::<&str>::new(), "{t:?}");
        }
    }

    /// What `t` gives with `x` and `y` at `at`, `Some(None)` for a failure; `None` when the run
    /// does not end within its fuel.
    fn run_at(t: &Term, at: (i64, i64)) -> Option<Option<Value>> {
        let bind = |n: &str, v: i64, b: Term| {
            Term::Let(
                n.into(),
                Shared::new(Term::Lit(Value::Int(v))),
                Shared::new(b),
            )
        };
        let t = bind("x", at.0, bind("y", at.1, t.clone()));
        match Evaluator::new(World::new()).with_fuel(1_000).run(&t) {
            Err(zed_kernel::KernelError::OutOfFuel) => None,
            r => Some(r.ok()),
        }
    }

    /// A preimage's relation, its formula and definitions as built.
    fn relation(p: &Preimage) -> Option<(String, Vec<String>)> {
        p.relation.as_ref().map(|r| {
            let defs = r
                .defs
                .iter()
                .map(|(n, w, f)| format!("{n} {w} {}", built(f)));
            (built(&r.body), defs.collect())
        })
    }

    /// What the round `round` checks of `t`: its translation (formula, definitions, cut,
    /// stops) and the whole preimage of each demand are what the memo before
    /// ST-formula-k2-rec gives, each entry made below a stop gives what reading its term again
    /// on the stack it began on gives ([`RECHECK`]), and each preimage holds every point of
    /// `x, y` in `-6..=6` at which the interpreter meets the demand, and only those where it
    /// is exact. The points stop at the first run that does not end. Gives the preimages,
    /// whether the translation stopped, the points met, and whether a run did not end.
    fn check(t: &Term, round: usize) -> ([Preimage; 2], bool, usize, bool) {
        let doms = domains();
        let demands = [true, false].map(Demand::Bool);
        NONE_HELD.set(true);
        let before = translate(t, false);
        let pb = demands.clone().map(|d| preimage(t, &doms, &d));
        NONE_HELD.set(false);
        let now = translate(t, false);
        let pn = demands.clone().map(|d| preimage(t, &doms, &d));
        RECHECK.set(true);
        translate(t, false);
        for d in &demands {
            preimage(t, &doms, d);
        }
        RECHECK.set(false);
        assert_eq!(now.formula, before.formula, "round {round}: {t:?}");
        assert_eq!(now.defs, before.defs, "round {round}: {t:?}");
        assert_eq!(now.cut, before.cut, "round {round}: {t:?}");
        assert_eq!(now.stops, before.stops, "round {round}: {t:?}");
        for ((p, q), d) in pn.iter().zip(&pb).zip(&demands) {
            assert_eq!(p, q, "round {round}, {d:?}: {t:?}");
            assert_eq!(relation(p), relation(q), "round {round}, {d:?}: {t:?}");
        }
        let mut met = 0;
        for x in -6..=6 {
            for y in -6..=6 {
                let Some(v) = run_at(t, (x, y)) else {
                    return (pn, now.cut != usize::MAX, met, true);
                };
                for (p, d) in pn.iter().zip(&demands) {
                    let inside = p.domains["x"].contains(x) && p.domains["y"].contains(y);
                    if v.as_ref().is_some_and(|v| d.holds(v)) {
                        met += 1;
                        assert!(inside, "round {round}, {d:?} at {x}, {y}: {t:?}");
                    } else {
                        let fails = !(p.exact && inside);
                        assert!(fails, "round {round}, {d:?} exact at {x}, {y}: {t:?}");
                    }
                }
            }
        }
        (pn, now.cut != usize::MAX, met, false)
    }

    /// An entry made below a stop is read where the lambdas being read when it began are still
    /// being read, and it gives there what the memo before ST-formula-k2-rec gave, which
    /// read the term again at each place ([`check`]), on random programs of functions that
    /// call themselves and each other ([`Gen::group`]), nested, with shared tests and calls
    /// whose arguments read the inputs, so that entries are read within other summaries and
    /// on higher stacks. Checks the rounds of part `part` ([`PARTS`]) of 1,000 of one seed,
    /// those whose remainder by [`PARTS`] is `part`, so that each part has about its share of
    /// every kind of program (taken an eighth in a row, rounds 375 to 499 held too few entries
    /// read again). Every round's program is generated, so that a round checks the same
    /// program whichever part it is in.
    fn entries_below_a_stop(part: usize) {
        let mut g = Gen::new(0x2545_f491_4f6c_dd1d, true);
        READS.set([0; 3]);
        CHECKED.set([0; 5]);
        let (mut met, mut endless, mut stopped) = (0, 0, 0);
        for round in 0..1000 {
            g.pool.clear();
            let t = match g.rng.below(3) {
                0 => g.group(4),
                1 => g.itself(4),
                _ => {
                    let p = if g.rng.below(2) == 0 {
                        Prim::And
                    } else {
                        Prim::Or
                    };
                    Term::Prim(p, vec![g.test(4), g.test(4)])
                }
            };
            if round % PARTS != part {
                continue;
            }
            let (_, s, m, e) = check(&t, round);
            stopped += usize::from(s);
            met += m;
            endless += usize::from(e);
        }
        let [reads, higher, other] = READS.get();
        let [checked, unchecked, raised, inside, everywhere] = CHECKED.get();
        eprintln!(
            "held reads {reads}, on a higher stack {higher}, under other inputs {other}; read \
             again {checked}, of kinds not compared {unchecked}, on a higher stack {raised}, \
             under other inputs {inside}, entries that hold anywhere {everywhere}; stopped \
             {stopped}, points met {met}, rounds out of fuel {endless}"
        );
        // Each part has more than its share, rounded down, of the counts the 1,000 rounds had
        // to have, so together the parts have more: reads > 5000, higher > 3000, other > 2000,
        // stopped > 400, met > 100,000, checked > 4000, raised > 3000, inside > 2000 and
        // everywhere > 500,000.
        let n = PARTS;
        assert!(stopped > 400 / n && met > 100_000 / n);
        let n = n as u64;
        assert!(reads > 5000 / n && higher > 3000 / n && other > 2000 / n);
        assert!(checked > 4000 / n && raised > 3000 / n && inside > 2000 / n);
        assert!(everywhere > 500_000 / n);
    }

    #[test]
    fn entries_made_below_a_stop_give_what_reading_the_term_again_gives_1() {
        entries_below_a_stop(0);
    }

    #[test]
    fn entries_made_below_a_stop_give_what_reading_the_term_again_gives_2() {
        entries_below_a_stop(1);
    }

    #[test]
    fn entries_made_below_a_stop_give_what_reading_the_term_again_gives_3() {
        entries_below_a_stop(2);
    }

    #[test]
    fn entries_made_below_a_stop_give_what_reading_the_term_again_gives_4() {
        entries_below_a_stop(3);
    }

    #[test]
    fn entries_made_below_a_stop_give_what_reading_the_term_again_gives_5() {
        entries_below_a_stop(4);
    }

    #[test]
    fn entries_made_below_a_stop_give_what_reading_the_term_again_gives_6() {
        entries_below_a_stop(5);
    }

    #[test]
    fn entries_made_below_a_stop_give_what_reading_the_term_again_gives_7() {
        entries_below_a_stop(6);
    }

    #[test]
    fn entries_made_below_a_stop_give_what_reading_the_term_again_gives_8() {
        entries_below_a_stop(7);
    }

    /// The summaries of `if` chains over one input ([`Pa`]) and over each class of remainders
    /// ([`ByClass`]) that [`RECHECK`] reads again give what reading their terms again gives,
    /// on the random programs of [`entries_below_a_stop`] whose tests may also compare a chain
    /// with a constant ([`Gen::chain_test`]). Checks the rounds of part `part` ([`PARTS`]) of 400
    /// of one seed, those whose remainder by [`PARTS`] is `part`. Each part must meet both
    /// kinds of summary; a summary made below a stop is met by some parts only, and
    /// [`a_summary_made_below_a_stop_is_read_again`] makes one on purpose.
    fn summaries_read_again(part: usize) {
        let mut g = Gen::new(0x5851_f42d_4c95_7f2d, true);
        g.chains = true;
        CHECKED.set([0; 5]);
        SUMMARIES.set([0; 4]);
        let (mut met, mut endless) = (0, 0);
        for round in 0..400 {
            g.pool.clear();
            let t = match g.rng.below(4) {
                0 => g.group(3),
                1 => g.itself(3),
                2 => g.chain_test(),
                _ => {
                    let p = if g.rng.below(2) == 0 {
                        Prim::And
                    } else {
                        Prim::Or
                    };
                    Term::Prim(p, vec![g.test(3), g.test(3)])
                }
            };
            if round % PARTS != part {
                continue;
            }
            let (_, _, m, e) = check(&t, round);
            met += m;
            endless += usize::from(e);
        }
        let [checked, unchecked, _, _, everywhere] = CHECKED.get();
        let [pa, pa_everywhere, by_class, by_class_everywhere] = SUMMARIES.get();
        eprintln!(
            "read again {checked}, of kinds not compared {unchecked}, entries that hold \
             anywhere {everywhere}; summaries held {pa}, anywhere {pa_everywhere}; by class \
             held {by_class}, anywhere {by_class_everywhere}; points met {met}, rounds out of \
             fuel {endless}"
        );
        assert_eq!(unchecked, 0);
        assert!(pa_everywhere > 0 && by_class_everywhere > 0);
    }

    #[test]
    fn summaries_read_again_give_what_reading_the_term_again_gives_1() {
        summaries_read_again(0);
    }

    #[test]
    fn summaries_read_again_give_what_reading_the_term_again_gives_2() {
        summaries_read_again(1);
    }

    #[test]
    fn summaries_read_again_give_what_reading_the_term_again_gives_3() {
        summaries_read_again(2);
    }

    #[test]
    fn summaries_read_again_give_what_reading_the_term_again_gives_4() {
        summaries_read_again(3);
    }

    #[test]
    fn summaries_read_again_give_what_reading_the_term_again_gives_5() {
        summaries_read_again(4);
    }

    #[test]
    fn summaries_read_again_give_what_reading_the_term_again_gives_6() {
        summaries_read_again(5);
    }

    #[test]
    fn summaries_read_again_give_what_reading_the_term_again_gives_7() {
        summaries_read_again(6);
    }

    #[test]
    fn summaries_read_again_give_what_reading_the_term_again_gives_8() {
        summaries_read_again(7);
    }

    /// The classes of [`unite`] without its remembered refusals and its look-up of the caller
    /// and callee: each join looks through the smaller class's functions.
    fn unite_by_looking(first: &[usize], joins: &[(usize, usize)]) -> (Vec<usize>, Vec<bool>) {
        fn find(parent: &mut [usize], mut v: usize) -> usize {
            while parent[v] != v {
                v = parent[v];
            }
            v
        }
        let nodes = *first.last().unwrap();
        let owner = |v: usize| first.partition_point(|&f| f <= v) - 1;
        let mut parent: Vec<usize> = (0..nodes).collect();
        let mut funs: Vec<HashSet<usize>> = (0..nodes).map(|v| HashSet::from([owner(v)])).collect();
        let mut joined = vec![false; nodes];
        for &(a, b) in joins {
            let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
            let (big, small) = match funs[ra].len() >= funs[rb].len() {
                true => (ra, rb),
                false => (rb, ra),
            };
            if ra == rb || funs[small].iter().any(|x| funs[big].contains(x)) {
                continue;
            }
            parent[small] = big;
            let f = std::mem::take(&mut funs[small]);
            funs[big].extend(f);
            joined[big] = true;
        }
        let root = (0..nodes).map(|v| find(&mut parent, v)).collect();
        (root, joined)
    }

    /// The preimage of an order of one input with an integer literal read at once
    /// ([`order_with_literal`]) is that of the general path ([`preimage_in`]), over random
    /// domains of one to three pieces, some ends infinite, literals among them the ends of
    /// `i64`, the four orders, the literal on either side, and both outcomes.
    #[test]
    fn an_order_with_a_literal_has_the_preimage_of_the_general_path() {
        let mut rng = Rng(0x6a09_e667_f3bc_c908);
        let x: Arc<str> = "x".into();
        let ops = [Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge];
        let (mut read, mut empty) = (0, 0);
        for _ in 0..4000 {
            let mut pieces = Vec::new();
            for _ in 0..1 + rng.below(3) {
                let lo = rng.below(41) as i64 - 20;
                let hi = lo + rng.below(10) as i64;
                let lo = if rng.below(8) == 0 {
                    NegInf
                } else {
                    End::of(lo)
                };
                let hi = if rng.below(8) == 0 {
                    PosInf
                } else {
                    End::of(hi)
                };
                pieces.push((lo, hi));
            }
            let inputs = Domains::from([(x.clone(), IntervalSet::from_pieces(pieces))]);
            let k = match rng.below(20) {
                0 => i64::MIN,
                1 => i64::MAX,
                _ => rng.below(51) as i64 - 25,
            };
            let (v, l) = (Term::Var(x.clone()), Term::Lit(Value::Int(k)));
            let op = ops[rng.below(4) as usize];
            let term = if rng.below(2) == 0 {
                Term::Prim(op, vec![v, l])
            } else {
                Term::Prim(op, vec![l, v])
            };
            let demand = Demand::Bool(rng.below(2) == 0);
            let Some(fast) = order_with_literal(&term, &inputs, &demand) else {
                assert!(
                    inputs[&x].is_empty(),
                    "{term} over {inputs:?} is read at once"
                );
                continue;
            };
            let mut tx = Tx::new();
            let root = tx.terms.add(&term);
            let general = preimage_in(&mut tx, root, &term, &inputs, NONE_LISTED, &demand);
            assert_eq!(fast, general, "{term} over {inputs:?}, {demand:?}");
            read += 1;
            empty += usize::from(fast.domains[&x].is_empty());
        }
        assert!(
            read > 3000 && empty > 300,
            "{read} read at once, {empty} empty"
        );
    }

    /// The summary of an `if` of two integer literals guarded by an order of an input against
    /// an integer literal, read at once ([`order_if`]), is the transfer's ([`Walk::pa`]),
    /// over random domains of one to three pieces, some ends infinite or at the end of `i128`
    /// that [`in_range`] refuses, literals among them the ends of `i64`, the four orders, the
    /// literal on either side, and a second input the term does not read.
    #[test]
    fn an_if_of_literals_on_an_order_has_the_summary_of_the_transfer() {
        let mut rng = Rng(0xbb67_ae85_84ca_a73b);
        let (x, y): (Arc<str>, Arc<str>) = ("x".into(), "y".into());
        let ops = [Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge];
        let (mut both, mut one, mut none) = (0, 0, 0);
        for _ in 0..4000 {
            let mut pieces = Vec::new();
            for _ in 0..1 + rng.below(3) {
                let lo = rng.below(41) as i64 - 20;
                let hi = lo + rng.below(10) as i64;
                let end = |v: i64, inf: End, rng: &mut Rng| match rng.below(16) {
                    0 | 1 => inf,
                    2 => Fin(Num::from(i128::MAX)),
                    _ => End::of(v),
                };
                let lo = end(lo, NegInf, &mut rng);
                let hi = end(hi, PosInf, &mut rng);
                if lo <= hi {
                    pieces.push((lo, hi));
                }
            }
            let dom = IntervalSet::from_pieces(pieces);
            if dom.is_empty() {
                continue;
            }
            let mut inputs = Domains::from([(x.clone(), dom)]);
            if rng.below(4) == 0 {
                inputs.insert(y.clone(), IntervalSet::range(End::of(0), End::of(5)));
            }
            let k = match rng.below(20) {
                0 => i64::MIN,
                1 => i64::MAX,
                _ => rng.below(51) as i64 - 25,
            };
            let (v, l) = (Term::Var(x.clone()), Term::Lit(Value::Int(k)));
            let op = ops[rng.below(4) as usize];
            let guard = if rng.below(2) == 0 {
                Term::Prim(op, vec![v, l])
            } else {
                Term::Prim(op, vec![l, v])
            };
            let arm = |rng: &mut Rng| Term::Lit(Value::Int(rng.below(7) as i64 - 3));
            let (a, b) = (arm(&mut rng), arm(&mut rng));
            let term = Term::If(Shared::new(guard), Shared::new(a), Shared::new(b));
            let fast = order_if(&term, &inputs).expect("the form read at once");
            let mut tx = Tx::new();
            let root = tx.terms.add(&term);
            let marks = tx.landmarks(&inputs, &Demand::Bool(true));
            tx.start(&inputs, marks);
            let general = tx.pa(root, ROOT);
            assert!(
                fast == general,
                "{term} over {inputs:?}: {:?} read at once, {:?} by the transfer",
                fast.as_ref().map(pa_pieces),
                general.as_ref().map(pa_pieces),
            );
            match &fast {
                Some(Pa::Piecewise { .. }) => both += 1,
                Some(_) => one += 1,
                None => none += 1,
            }
        }
        assert!(
            both > 1000 && one > 500 && none > 100,
            "{both} sliced, {one} constant, {none} with no summary"
        );
    }

    /// [`unite`] gives the classes of the union that looks for a shared function at each join,
    /// root for root, over random functions of 0 to 4 parameters and random joins, among them
    /// two parameters of one function and joins repeated.
    #[test]
    fn the_classes_are_those_of_a_join_refused_by_looking() {
        let mut rng = Rng(0x2f6b_8a1c_93d4_e507);
        let mut refused = 0;
        for _ in 0..2000 {
            let mut first = vec![0];
            for _ in 0..1 + rng.below(12) {
                first.push(first.last().unwrap() + rng.below(5) as usize);
            }
            let nodes = *first.last().unwrap() as u64;
            if nodes == 0 {
                continue;
            }
            let joins: Vec<(usize, usize)> = (0..rng.below(3 * nodes + 1))
                .map(|_| (rng.below(nodes) as usize, rng.below(nodes) as usize))
                .collect();
            let (root, joined) = unite(&first, &joins);
            let looked = unite_by_looking(&first, &joins);
            assert_eq!(
                (&root, &joined),
                (&looked.0, &looked.1),
                "functions from {first:?}, joins {joins:?}"
            );
            // Each class holds at most one parameter of a function.
            for k in 0..first.len() - 1 {
                let roots: HashSet<usize> = (first[k]..first[k + 1]).map(|v| root[v]).collect();
                assert_eq!(roots.len(), first[k + 1] - first[k], "{first:?} {joins:?}");
            }
            refused += joins.iter().filter(|&&(a, b)| root[a] != root[b]).count();
        }
        assert!(refused > 1000, "{refused} joins refused");
    }

    /// Eight pairs of classes of n/8 functions each, each pair sharing one function `s(x, y)`
    /// (`x` in the first class, `y` in the second), and n/8 functions
    /// `t{j}(x) = ra(x: x) && rb(y: x)` a pair, each joining its parameter to the first class
    /// and then refused against the second for `s`, which is neither its caller nor its callee.
    /// Looking through the smaller class at each refusal is O(n²) (eight pairs, so the place of
    /// `s` in each class's order varies less between runs); remembered, a repeated refusal is
    /// O(1).
    #[test]
    fn refused_joins_between_two_large_classes_scale() {
        // A function of `params` parameters added after those of `first`: its first parameter.
        fn function(first: &mut Vec<usize>, params: usize) -> usize {
            let at = *first.last().unwrap();
            first.push(at + params);
            at
        }
        let input = |n: usize| {
            let (mut first, mut joins, mut pairs) = (vec![0], Vec::new(), Vec::new());
            for _ in 0..8 {
                let (ra, rb) = (function(&mut first, 1), function(&mut first, 1));
                let s = function(&mut first, 2);
                joins.extend([(s, ra), (s + 1, rb)]);
                for _ in 0..n / 8 {
                    let (a, b) = (function(&mut first, 1), function(&mut first, 1));
                    joins.extend([(a, ra), (b, rb)]);
                }
                for _ in 0..n / 8 {
                    let t = function(&mut first, 1);
                    joins.extend([(t, ra), (t, rb)]);
                }
                pairs.push((ra, rb));
            }
            (first, joins, pairs)
        };
        let (small, large) = (input(1000), input(8000));
        let (root, _) = unite(&large.0, &large.1);
        for &(ra, rb) in &large.2 {
            assert_ne!(root[ra], root[rb], "the two classes of a pair stay apart");
        }
        crate::scaling::compare(
            "refused joins between two classes of n/8 functions, eight pairs, n = 1000 and 8000",
            1,
            || {
                std::hint::black_box(unite(&small.0, &small.1));
            },
            || {
                std::hint::black_box(unite(&large.0, &large.1));
            },
        );
    }

    /// [`Gen::chain`] makes a chain of `n` `if`s in work of order `n`: each level reads the
    /// one term below it, shared, so neither the work nor the term doubles at a level.
    #[test]
    fn a_chain_is_made_in_work_of_order_its_length() {
        crate::scaling::check_order("a chain of n ifs over one input made", 2000, 1, |n| {
            let mut g = Gen::new(0x5851_f42d_4c95_7f2d, true);
            g.chains = true;
            std::hint::black_box(g.chain(n, true));
        });
    }

    /// The preimage of `chain(k) <= 2` ([`Gen::chain`]) over `x` and `y` in `[-6, 6]`, exact.
    fn chain_preimage(seed: u64, k: usize) {
        let doms: Domains = [
            ("x".into(), IntervalSet::of(-6, 6)),
            ("y".into(), IntervalSet::of(-6, 6)),
        ]
        .into();
        let mut g = Gen::new(seed, true);
        g.chains = true;
        let t = Term::Prim(Prim::Le, vec![g.chain(k, true), Term::Lit(Value::Int(2))]);
        let p = preimage(&t, &doms, &Demand::Bool(true));
        assert!(p.exact, "seed {seed:#x}, k = {k}: {p:?}");
    }

    /// A chain of guards on `x mod 3` whose arms move, reflect, negate, scale and clamp the
    /// term below, with `min` and `max` across their constant and `0 * u` (COMPLEXITY.md row
    /// S22-order-chain: 6.7 ms, 209 ms, 3.37 s and 30.2 s at k = 20, 40, 80 and 160). Each
    /// level is one summary over the classes ([`ByClass`]), so the shared term is read once.
    #[test]
    fn a_chain_is_read_in_time_near_its_length() {
        crate::scaling::check_order("the preimage of a chain of k ifs", 10, 1, |k| {
            chain_preimage(0x5851_f42d_4c95_7f2d, k)
        });
    }

    /// A chain on `y` whose guards compare `y` with constants or take `y mod 2`, with `min`
    /// arms across their constant, and `if`s on a comparison whose arms read the remainder in
    /// different ways ([`Walk::by_class_if`], [`ByClass::clamp`]).
    #[test]
    fn a_chain_with_clamps_is_read_in_time_near_its_length() {
        crate::scaling::check_order(
            "the preimage of a chain of k ifs, mixed guards",
            10,
            1,
            |k| chain_preimage(0xa, k),
        );
    }

    /// A chain whose guards compare `x` with constants, with `min` and `max` arms across their
    /// constant: one summary of each level ([`Pa::clamp`]).
    #[test]
    fn a_chain_of_comparisons_is_read_in_time_near_its_length() {
        crate::scaling::check_order(
            "the preimage of a chain of k ifs, comparisons",
            10,
            1,
            |k| chain_preimage(1, k),
        );
    }

    /// `false || (if 2x > max(x, x) {ym + -3 <= -6} else {2x > max(x, x)}) ||
    /// (let n0 = min(x, 3) - min(x, -3) in let n1 = stage(n0) in ... n_k == -7)`, with
    /// `ym = if y mod 2 != 1 {-1} else {-1}` and `stage(n) = if n < 2 {-1} else {(if n != -4
    /// {n + 3} else {max(n, 2)}) - (-1)}`: round 81 of `summaries_read_again` (seed
    /// `0x5851_f42d_4c95_7f2d`, part 1) minimized and grown to `k` stages (item
    /// PREIMAGE-slow-rounds).
    fn staged_chain(k: usize) -> Term {
        let v = |n: &str| Term::Var(n.into());
        let int = |i: i64| Term::Lit(Value::Int(i));
        let p2 = |p: Prim, a: Term, b: Term| Term::Prim(p, vec![a, b]);
        let if_ =
            |c: Term, a: Term, b: Term| Term::If(Shared::new(c), Shared::new(a), Shared::new(b));
        let stage = |n: Term| {
            let inner = if_(
                p2(Prim::Ne, n.clone(), int(-4)),
                p2(Prim::Add, n.clone(), int(3)),
                p2(Prim::Max, n.clone(), int(2)),
            );
            if_(
                p2(Prim::Lt, n, int(2)),
                int(-1),
                p2(Prim::Sub, inner, int(-1)),
            )
        };
        let mut body = p2(Prim::Eq, v(&format!("n{k}")), int(-7));
        for i in (1..=k).rev() {
            body = Term::Let(
                format!("n{i}").into(),
                Shared::new(stage(v(&format!("n{}", i - 1)))),
                Shared::new(body),
            );
        }
        let arg = p2(
            Prim::Sub,
            p2(Prim::Min, v("x"), int(3)),
            p2(Prim::Min, v("x"), int(-3)),
        );
        let call = Term::Let("n0".into(), Shared::new(arg), Shared::new(body));
        let c = Shared::new(p2(
            Prim::Gt,
            p2(Prim::Mul, int(2), v("x")),
            p2(Prim::Max, v("x"), v("x")),
        ));
        let ym = if_(
            p2(Prim::Ne, p2(Prim::Mod, v("y"), int(2)), int(1)),
            Term::Prim(Prim::Neg, vec![int(1)]),
            Term::Prim(Prim::Neg, vec![int(1)]),
        );
        let left = Term::If(
            c.clone(),
            Shared::new(p2(Prim::Le, p2(Prim::Add, ym, int(-3)), int(-6))),
            c,
        );
        let left = p2(Prim::Or, Term::Lit(Value::Bool(false)), left);
        p2(Prim::Or, left, call)
    }

    /// The preimage of [`staged_chain`] under `false`, whose hulls are tightened by questions
    /// to the solver over the whole formula (`presburger::project_each`). Before item
    /// PREIMAGE-slow-rounds each question probed every disjunct again; now the points found
    /// are kept across the questions and a disjunct is searched from both ends of the chain.
    /// What is left is the probe of the formula itself, whose `learn` settles a bound at
    /// stage `i` in about `i` rounds of the whole formula (COMPLEXITY.md
    /// PREIMAGE-slow-rounds).
    #[test]
    fn a_staged_chain_under_false_is_read_in_time_near_its_length() {
        crate::scaling::check_order(
            "the preimage under false of a chain of k stages",
            4,
            1,
            |k| {
                let p = preimage(&staged_chain(k), &domains(), &Demand::Bool(false));
                assert!(p.exact, "k = {k}: {p:?}");
            },
        );
    }

    /// The preimage of [`staged_chain`] under `false` is the whole box at every length, under
    /// `true` empty: no stage reaches `-7`, and the left side holds nowhere.
    #[test]
    fn a_staged_chain_is_read_exactly() {
        for k in [1, 2, 5] {
            let t = staged_chain(k);
            let all = preimage(&t, &domains(), &Demand::Bool(false));
            assert!(all.exact, "k = {k}: {all:?}");
            assert_eq!(all.domains, domains(), "k = {k}");
            let none = preimage(&t, &domains(), &Demand::Bool(true));
            assert!(none.exact, "k = {k}: {none:?}");
            assert!(
                none.domains.values().all(IntervalSet::is_empty),
                "k = {k}: {none:?}"
            );
        }
    }

    /// `min` and `max` of a summary with a constant ([`clamp_treap`]) agree with the summary
    /// clamped point by point, on random piecewise summaries.
    #[test]
    fn a_clamped_summary_is_the_summary_clamped_at_every_point() {
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        for round in 0..2000 {
            let mut root = None;
            let mut lo = -40i64;
            for _ in 0..1 + rng.below(6) {
                let hi = lo + rng.below(12) as i64;
                let (a, b) = (rng.below(7) as i128 - 3, rng.below(21) as i128 - 10);
                let node = make_node(End::of(lo), End::of(hi), a.into(), b.into(), None, None);
                root = join_treap(root, Some(node));
                lo = hi + 1 + rng.below(3) as i64;
            }
            let c = rng.below(31) as i128 - 15;
            let min = rng.below(2) == 0;
            let clamped = clamp_treap(&root, min, &c.into());
            for x in -40..=lo + 12 {
                let want = point(&root, x).map(|v| if min { v.min(c) } else { v.max(c) });
                assert_eq!(
                    point(&clamped, x),
                    want,
                    "round {round}, x = {x}, min {min}, c = {c}"
                );
            }
            // The values the root keeps are those of its pieces.
            if let Some(r) = &clamped {
                let vals = (-40..=lo + 12).filter_map(|x| point(&clamped, x));
                let (vlo, vhi) =
                    vals.fold((i128::MAX, i128::MIN), |(l, h), v| (l.min(v), h.max(v)));
                assert!(
                    r.vals.0 <= Val::Fin(vlo.into()) && Val::Fin(vhi.into()) <= r.vals.1,
                    "round {round}: {:?}",
                    r.vals
                );
            }
        }
    }

    /// The summary of `abs(u)` and of `min` and `max` of two terms of one input ([`Walk::pa`])
    /// is the interpreter's value at every point of the input's domain, on random terms of `x`
    /// built from those, `+`, `-`, a product with a constant and integer literals; every such
    /// term has a summary.
    #[test]
    fn abs_and_two_term_min_and_max_have_the_value_at_every_point() {
        fn term(rng: &mut Rng, d: u32) -> Term {
            let lit = |v: i64| Term::Lit(Value::Int(v));
            if d == 0 || rng.below(4) == 0 {
                return match rng.below(3) {
                    0 => lit(rng.below(13) as i64 - 6),
                    _ => Term::Var("x".into()),
                };
            }
            let p = |p: Prim, args: Vec<Term>| Term::Prim(p, args);
            match rng.below(6) {
                0 => p(Prim::Abs, vec![term(rng, d - 1)]),
                1 => p(Prim::Min, vec![term(rng, d - 1), term(rng, d - 1)]),
                2 => p(Prim::Max, vec![term(rng, d - 1), term(rng, d - 1)]),
                3 => p(Prim::Add, vec![term(rng, d - 1), term(rng, d - 1)]),
                4 => p(Prim::Sub, vec![term(rng, d - 1), term(rng, d - 1)]),
                _ => p(
                    Prim::Mul,
                    vec![lit(rng.below(7) as i64 - 3), term(rng, d - 1)],
                ),
            }
        }
        let mut rng = Rng(0x6a09_e667_f3bc_c908);
        let x: Arc<str> = "x".into();
        let mut pieces = 0;
        for round in 0..1500 {
            let t = term(&mut rng, 4);
            let lo = rng.below(41) as i64 - 30;
            let hi = lo + rng.below(30) as i64;
            let inputs = Domains::from([(x.clone(), IntervalSet::of(lo, hi))]);
            let mut tx = Tx::new();
            let root = tx.terms.add(&t);
            let marks = tx.landmarks(&inputs, &Demand::Bool(true));
            tx.start(&inputs, marks);
            let Some(pa) = tx.pa(root, ROOT) else {
                panic!("round {round}: {t} over {lo}..={hi} has no summary");
            };
            if let Pa::Piecewise { root, .. } = &pa {
                pieces += treap_pieces(root).len();
            }
            for v in lo..=hi {
                let at = match &pa {
                    Pa::Piecewise { root, .. } => point(root, v),
                    Pa::Linear { a, b, .. } => (&(a * &Int::from(v)) + b).to_i128(),
                    Pa::Const(c) => c.to_i128(),
                };
                let run = Term::Let(
                    x.clone(),
                    Shared::new(Term::Lit(Value::Int(v))),
                    Shared::new(t.clone()),
                );
                let want = match eval(&run) {
                    Ok(Value::Int(n)) => Some(i128::from(n)),
                    other => panic!("round {round}: {t} at x = {v}: {other:?}"),
                };
                assert_eq!(at, want, "round {round}: {t} at x = {v}");
                // The bounds the root keeps hold the value.
                if let (Pa::Piecewise { root: Some(r), .. }, Some(w)) = (&pa, want) {
                    let w = Val::Fin(Int::from(w));
                    assert!(
                        r.vals.0 <= w && w <= r.vals.1,
                        "round {round}: {t}: {:?}",
                        r.vals
                    );
                }
            }
        }
        // Many of the summaries have pieces: the check reads the choices.
        assert!(pieces > 1000, "{pieces} pieces");
    }

    /// `abs` of a line and `min` and `max` of two lines keep exact bounds at the root
    /// ([`Pa::by_sign`]), over a bounded domain and over all integers, where the line added to
    /// a clamp ([`Pa::plus`]) kept an infinite bound.
    #[test]
    fn abs_min_and_max_of_lines_keep_exact_bounds() {
        let x = || Term::Var("x".into());
        let lit = |v: i64| Term::Lit(Value::Int(v));
        let p = |p: Prim, args: Vec<Term>| Term::Prim(p, args);
        let lin = |a: i64, b: i64| p(Prim::Add, vec![p(Prim::Mul, vec![lit(a), x()]), lit(b)]);
        let bounds = |t: &Term, dom: IntervalSet| {
            let inputs = Domains::from([(Arc::<str>::from("x"), dom)]);
            let mut tx = Tx::new();
            let root = tx.terms.add(t);
            let marks = tx.landmarks(&inputs, &Demand::Bool(true));
            tx.start(&inputs, marks);
            match tx.pa(root, ROOT) {
                Some(Pa::Piecewise { root: Some(r), .. }) => r.vals.clone(),
                _ => panic!("{t} has no summary with pieces"),
            }
        };
        let fin = |v: i128| Val::Fin(Int::from(v));
        let top = IntervalSet::top();
        assert_eq!(
            bounds(&p(Prim::Abs, vec![x()]), top.clone()),
            (fin(0), Val::Pos)
        );
        assert_eq!(
            bounds(&p(Prim::Abs, vec![lin(2, -3)]), IntervalSet::of(-4, 6)),
            (fin(1), fin(11))
        );
        assert_eq!(
            bounds(&p(Prim::Abs, vec![lin(-3, 7)]), IntervalSet::of(-2, 5)),
            (fin(1), fin(13))
        );
        let two = |q: Prim, dom: IntervalSet| bounds(&p(q, vec![lin(1, 1), lin(-1, 10)]), dom);
        assert_eq!(two(Prim::Min, top.clone()), (Val::Neg, fin(5)));
        assert_eq!(two(Prim::Max, top.clone()), (fin(6), Val::Pos));
        assert_eq!(two(Prim::Min, IntervalSet::of(0, 20)), (fin(-10), fin(5)));
        assert_eq!(two(Prim::Max, IntervalSet::of(0, 20)), (fin(6), fin(21)));
        // Parallel lines: one is chosen over the whole domain.
        let par = p(Prim::Max, vec![lin(2, 1), lin(2, -4)]);
        assert_eq!(bounds(&par, IntervalSet::of(-3, 3)), (fin(-5), fin(7)));
    }

    /// A random summary with pieces from -40 on, gaps between some, and lines added to and
    /// scalings of some stretches by tags, so that the tags below a node carry slopes.
    fn random_treap(rng: &mut Rng) -> Tree {
        let mut root = None;
        let mut lo = -40i64;
        for _ in 0..1 + rng.below(8) {
            let hi = lo + rng.below(10) as i64;
            let (a, b) = (rng.below(7) as i128 - 3, rng.below(21) as i128 - 10);
            let node = make_node(End::of(lo), End::of(hi), a.into(), b.into(), None, None);
            root = join_treap(root, Some(node));
            lo = hi + 1 + rng.below(3) as i64;
        }
        for _ in 0..rng.below(3) {
            let (below, above) = split_at(root, rng.below(60) as i128 - 40);
            let f = Tag {
                mul: (rng.below(5) as i128 - 2).into(),
                slope: (rng.below(7) as i128 - 3).into(),
                add: (rng.below(11) as i128 - 5).into(),
            };
            let below = below.map(|n| apply_tag(&n, &f));
            root = join_treap(below, above);
        }
        root
    }

    /// Checks that every node's bounds hold the values of its subtree and that its count is
    /// the number of its pieces, on the inputs -60..=60.
    fn check_nodes(t: &Tree) {
        let Some(n) = t else {
            return;
        };
        let vals: Vec<i128> = (-60..=60).filter_map(|x| point(t, x)).collect();
        let pieces = treap_pieces(t);
        assert_eq!(n.len, pieces.len());
        for v in vals {
            assert!(
                n.vals.0 <= Val::Fin(v.into()) && Val::Fin(v.into()) <= n.vals.1,
                "{v} outside {:?}",
                n.vals
            );
        }
        let (left, right) = push_down(n);
        check_nodes(&left);
        check_nodes(&right);
    }

    /// The sum and the difference of two random piecewise summaries ([`Pa::plus`]) agree with
    /// the sum point by point, defined where both are; with a line, likewise; and the
    /// preimage of a random set under the sum ([`invert_treap`]) and the sum clamped
    /// ([`clamp_treap`]) agree with the points.
    #[test]
    fn a_sum_of_summaries_is_the_sum_at_every_point() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        let var: Arc<str> = "n".into();
        let piecewise = |root: Tree| Pa::Piecewise {
            var: var.clone(),
            root,
        };
        for round in 0..2000 {
            let (p, q) = (random_treap(&mut rng), random_treap(&mut rng));
            let sign = if rng.below(2) == 0 { 1 } else { -1 };
            let line = (rng.below(7) as i128 - 3, rng.below(21) as i128 - 10);
            let sums = [
                (piecewise(p.clone()), piecewise(q.clone())),
                (
                    piecewise(p.clone()),
                    Pa::Linear {
                        var: var.clone(),
                        a: line.0.into(),
                        b: line.1.into(),
                    },
                ),
                (
                    Pa::Linear {
                        var: var.clone(),
                        a: line.0.into(),
                        b: line.1.into(),
                    },
                    piecewise(q.clone()),
                ),
            ];
            for (k, (u, v)) in sums.iter().enumerate() {
                let at = |pa: &Pa, x: i64| match pa {
                    Pa::Piecewise { root, .. } => point(root, x),
                    Pa::Linear { a, b, .. } => (&(a * &Int::from(x)) + b).to_i128(),
                    Pa::Const(c) => c.to_i128(),
                };
                let Some(Pa::Piecewise { root: sum, .. }) = u.plus(v, sign) else {
                    panic!("round {round}, case {k}: no summary");
                };
                for x in -60..=60 {
                    let want = at(u, x).zip(at(v, x)).map(|(s, t)| s + sign * t);
                    assert_eq!(point(&sum, x), want, "round {round}, case {k}, x = {x}");
                }
                check_nodes(&sum);
                let lo = rng.below(41) as i64 - 20;
                let z = IntervalSet::of(lo, lo + rng.below(15) as i64);
                let mut got = Vec::new();
                invert_treap(&sum, &Tag::ID, &z, &mut got);
                for x in -60..=60 {
                    let hit = got
                        .iter()
                        .any(|(l, h)| *l <= End::of(x) && End::of(x) <= *h);
                    let want = point(&sum, x).is_some_and(|v| z.contains(v as i64));
                    assert_eq!(hit, want, "round {round}, case {k}, x = {x}, z = {z:?}");
                }
                let c = rng.below(31) as i128 - 15;
                let clamped = clamp_treap(&sum, true, &c.into());
                for x in -60..=60 {
                    assert_eq!(point(&clamped, x), point(&sum, x).map(|v| v.min(c)));
                }
            }
        }
    }

    /// The value of the summary `t` at `x`, or `None` where it has no piece. A node's own
    /// piece has its maps applied; its children get its tag ([`push_down`]).
    fn point(t: &Tree, x: i64) -> Option<i128> {
        let n = t.as_ref()?;
        let (left, right) = push_down(n);
        if End::of(x) < n.lo {
            return point(&left, x);
        }
        if End::of(x) > n.hi {
            return point(&right, x);
        }
        (&(&n.a * &Int::from(x)) + &n.b).to_i128()
    }

    mod written {
        //! Hand-written programs, one for each way an entry made below a stop could be read
        //! where it no longer holds.
        use super::*;

        fn v(n: &str) -> Term {
            Term::Var(n.into())
        }
        fn int(i: i64) -> Term {
            Term::Lit(Value::Int(i))
        }
        fn prim(p: Prim, a: Term, b: Term) -> Term {
            Term::Prim(p, vec![a, b])
        }
        fn app(f: Term, args: Vec<Term>) -> Term {
            Term::App(Shared::new(f), args)
        }
        fn lam(ps: &[&str], body: Term) -> Term {
            Term::Lam(ps.iter().map(|&p| p.into()).collect(), Shared::new(body))
        }
        fn let_(n: &str, e: Term, b: Term) -> Term {
            Term::Let(n.into(), Shared::new(e), Shared::new(b))
        }
        fn if_(c: Term, a: Term, b: Term) -> Term {
            Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
        }

        /// The counters of [`check`] on `t`, and its preimages shown: for each demand, the
        /// box, whether it is exact, and the stops.
        fn run(t: &Term) -> (usize, [u64; 3], [u64; 5], String) {
            MADE.with_borrow_mut(HashMap::clear);
            READS.set([0; 3]);
            CHECKED.set([0; 5]);
            let (ps, _, _, endless) = check(t, 0);
            assert!(!endless, "{t:?}");
            let shown = ps.map(|p| {
                format!(
                    "x {} y {}{} stops {}",
                    p.domains["x"],
                    p.domains["y"],
                    if p.exact { " exact" } else { "" },
                    p.stops.len()
                )
            });
            (
                MADE.with_borrow(HashMap::len),
                READS.get(),
                CHECKED.get(),
                shown.join("; "),
            )
        }

        use Prim::{Add, And, Eq, Ge, Le, Lt, Min, Mul, Or, Sub};

        /// `f(f, n - c)`.
        fn again(c: i64) -> Term {
            app(v("f"), vec![v("f"), prim(Sub, v("n"), int(c))])
        }

        /// `let f = (f, n) -> if n <= 0 { base } else { step } in f(f, arg)`.
        fn rec(base: Term, step: Term, arg: Term) -> Term {
            let f = lam(&["f", "n"], if_(prim(Le, v("n"), int(0)), base, step));
            let_("f", f, app(v("f"), vec![v("f"), arg]))
        }

        /// `let k = (g) -> g(g, 0) <= x in let w = (g, n) -> if n <= 0 { 1 } else { if k(g)
        /// { 1 } else { 2 } } in w(w, x) >= 1 && k(w)`: `k`'s body stops at `w` within `w`, so
        /// its entries are held, and `k(w)` is read again once `w` has returned.
        #[test]
        fn an_entry_that_stops_at_a_lambda_being_read_is_held() {
            let k = lam(&["g"], prim(Le, app(v("g"), vec![v("g"), int(0)]), v("x")));
            let w = lam(
                &["g", "n"],
                if_(
                    prim(Le, v("n"), int(0)),
                    int(1),
                    if_(app(v("k"), vec![v("g")]), int(1), int(2)),
                ),
            );
            let body = prim(
                And,
                prim(Ge, app(v("w"), vec![v("w"), v("x")]), int(1)),
                app(v("k"), vec![v("w")]),
            );
            let (made, reads, _, shown) = run(&let_("k", k, let_("w", w, body)));
            assert_eq!(
                shown,
                "x [1..=6] y [-6..=6] stops 2; x [-6..=0] y [-6..=6] exact stops 2"
            );
            assert!(made > 0 && reads[0] > 0, "{made} {reads:?}");
        }

        /// `f(f, n) = if n <= 0 { ((q) -> x - 3 <= 1)(n) } else { (let s = f(f, n - 1) && 2
        /// <= n in (s || ((u) -> s)(x + n - y)) && ((w) -> f(f, n - 2) || s)(-3 - y)) || y <=
        /// x }`: entries made within the lambda of `w` are not read within the lambda of `u`,
        /// at the same height of the stack.
        #[test]
        fn an_entry_made_within_one_lambda_is_not_read_within_another() {
            let s = prim(And, again(1), prim(Le, int(2), v("n")));
            let first = prim(
                Or,
                v("s"),
                app(
                    lam(&["u"], v("s")),
                    vec![prim(Add, v("x"), prim(Sub, v("n"), v("y")))],
                ),
            );
            let second = app(
                lam(&["w"], prim(Or, again(2), v("s"))),
                vec![prim(Sub, int(-3), v("y"))],
            );
            let step = prim(
                Or,
                let_("s", s, prim(And, first, second)),
                prim(Le, v("y"), v("x")),
            );
            let base = app(
                lam(&["q"], prim(Le, prim(Sub, v("x"), int(3)), int(1))),
                vec![v("n")],
            );
            let arg = prim(Min, prim(Sub, prim(Sub, int(1), v("y")), v("x")), int(4));
            let (made, reads, checked, shown) = run(&rec(base, step, arg));
            assert_eq!(
                shown,
                "x [-6..=6] y [-6..=6] stops 2; x [-6..=6] y [-5..=6] stops 2"
            );
            assert!(
                made > 0 && reads[1] > 0 && checked[2] > 0,
                "{reads:?} {checked:?}"
            );
        }

        /// `f(f, n) = if n <= 0 { n <= y } else { let a = f(f, n - 1) || x <= n in a && ((p)
        /// -> a || (p >= y && x <= n))(n + x) }` with `f(f, 2)`: `a` stops at `f`, and is read
        /// again within the lambda of `p`, on a higher stack and with `p` among the inputs.
        /// With `p` named `x`, the `x <= n` within it is another term than the one in `a`.
        fn higher(p: &str) -> ([u64; 3], [u64; 5], String) {
            let a = prim(Or, again(1), prim(Le, v("x"), v("n")));
            let inner = lam(
                &[p],
                prim(
                    Or,
                    v("a"),
                    prim(And, prim(Ge, v(p), v("y")), prim(Le, v("x"), v("n"))),
                ),
            );
            let step = let_(
                "a",
                a,
                prim(And, v("a"), app(inner, vec![prim(Add, v("n"), v("x"))])),
            );
            let (made, reads, checked, shown) = run(&rec(prim(Le, v("n"), v("y")), step, int(2)));
            assert!(made > 0 && reads[1] > 0 && reads[2] > 0, "{reads:?}");
            assert!(checked[2] > 0 && checked[3] > 0, "{checked:?}");
            (reads, checked, shown)
        }

        #[test]
        fn an_entry_read_within_a_call_holds_under_its_inputs() {
            let (_, _, shown) = higher("u");
            assert_eq!(
                shown,
                "x [-6..=6] y [-6..=6] stops 1; x [3..=6] y [-6..=6] stops 1"
            );
        }

        #[test]
        fn a_parameter_that_shadows_an_input_reaches_no_entry_of_the_input() {
            let (_, _, shown) = higher("x");
            assert_eq!(
                shown,
                "x [-6..=6] y [-6..=6] stops 1; x [3..=6] y [-6..=6] stops 1"
            );
        }

        /// `f(f, n) = if n <= 0 { 2 < 2 } else { let s = f(f, n - 1) || -1 + y == 2 * y in (s
        /// || n < n) || ((u) -> s || s)(-2) }` with `f(f, -3)`: the `||` within the lambda of
        /// `u` reads `s` only from the memo, and stops where `s` stopped.
        #[test]
        fn a_hit_passes_its_cut_to_the_reader() {
            let s = prim(
                Or,
                again(1),
                prim(Eq, prim(Add, int(-1), v("y")), prim(Mul, int(2), v("y"))),
            );
            let inner = app(lam(&["u"], prim(Or, v("s"), v("s"))), vec![int(-2)]);
            let step = let_(
                "s",
                s,
                prim(Or, prim(Or, v("s"), prim(Lt, v("n"), v("n"))), inner),
            );
            let (made, reads, checked, shown) = run(&rec(prim(Lt, int(2), int(2)), step, int(-3)));
            assert_eq!(
                shown,
                "x [] y [] exact stops 1; x [-6..=6] y [-6..=6] exact stops 1"
            );
            assert!(
                made > 0 && reads[0] > 0 && checked[0] > 0,
                "{reads:?} {checked:?}"
            );
        }

        /// `x mod m == r`.
        fn class(m: i64, r: i64) -> Term {
            prim(Eq, prim(Prim::Mod, v("x"), int(m)), int(r))
        }

        /// `x mod 3 != 0 && (if x <= 2 { false } else { x < x })`: the transfer of the test
        /// `if` in a class asks for its summary by class, whose making read the transfer of the
        /// `if` in turn, without end (S22-order).
        #[test]
        fn a_test_if_in_a_class_does_not_read_its_own_summary() {
            let test = if_(
                prim(Le, v("x"), int(2)),
                Term::Lit(Value::Bool(false)),
                prim(Lt, v("x"), v("x")),
            );
            let t = prim(
                And,
                prim(Prim::Ne, prim(Prim::Mod, v("x"), int(3)), int(0)),
                test,
            );
            let (_, _, checked, shown) = run(&t);
            assert_eq!(
                shown,
                "x [] y [] exact stops 0; x [-6..=6] y [-6..=6] exact stops 0"
            );
            assert_eq!(checked[1], 0, "{checked:?}");
        }

        /// `let t = if x < 0 { u + 1 } else { 3 - u }`, with `u = if x mod m == 0 { x } else
        /// { x + 1 }`, read under `t <= 2 && t >= -3` and under `t >= -3 && t <= 2`: the
        /// summaries of `t` and `u` are made under the first test read, and the preimages are
        /// the same in either order. With `m = 2` the split by remainders reads the term alone,
        /// with the summaries by class ([`ByClass`]); with `m = 8` the guard lies within two
        /// periods, and the transfer reads it with the plain summaries ([`Pa`]).
        #[test]
        fn a_shared_chain_gives_one_preimage_in_either_order() {
            for (m, kind, expected) in [
                (
                    2,
                    3,
                    "x [-5..=-1, 1..=6] y [-6..=6] exact stops 0; x [-6..=-6, 0..=0] y [-6..=6] \
                     exact stops 0",
                ),
                (
                    8,
                    1,
                    "x [-5..=-1, 1..=5] y [-6..=6] exact stops 0; x [-6..=-6, 0..=0, 6..=6] y \
                     [-6..=6] exact stops 0",
                ),
            ] {
                let u = if_(class(m, 0), v("x"), prim(Add, v("x"), int(1)));
                let t = if_(
                    prim(Lt, v("x"), int(0)),
                    prim(Add, v("u"), int(1)),
                    prim(Sub, int(3), v("u")),
                );
                let (a, b) = (prim(Le, v("t"), int(2)), prim(Ge, v("t"), int(-3)));
                let both =
                    |p: Term, q: Term| let_("u", u.clone(), let_("t", t.clone(), prim(And, p, q)));
                SUMMARIES.set([0; 4]);
                let (ab, _, _, _) = check(&both(a.clone(), b.clone()), 0);
                let (ba, _, _, _) = check(&both(b.clone(), a.clone()), 1);
                assert_eq!(ab, ba, "m = {m}");
                assert!(SUMMARIES.get()[kind] > 0, "m = {m}: {:?}", SUMMARIES.get());
                let (_, _, _, shown) = run(&both(a, b));
                assert_eq!(shown, expected, "m = {m}");
            }
        }

        /// `f(f, n) = if n <= 0 { x <= 1 } else { (if x mod 2 == 0 { s } else { s - 1 }) <= 3 }`,
        /// with `s = if f(f, n - 1) { x + 1 } else { 2 - x }`: the summary of the chain is
        /// made while `f` is being read, below a stop, and read again there ([`RECHECK`]).
        #[test]
        fn a_summary_made_below_a_stop_is_read_again() {
            let s = if_(
                again(1),
                prim(Add, v("x"), int(1)),
                prim(Sub, int(2), v("x")),
            );
            let chain = if_(class(2, 0), v("s"), prim(Sub, v("s"), int(1)));
            let step = let_("s", s, prim(Le, chain, int(3)));
            SUMMARIES.set([0; 4]);
            let (_, _, checked, shown) = run(&rec(prim(Le, v("x"), int(1)), step, v("y")));
            assert_eq!(
                shown,
                "x [-6..=6] y [-6..=6] stops 1; x [-6..=-2, 2..=6] y [-6..=6] stops 1"
            );
            assert_eq!(checked[1], 0, "{checked:?}");
            assert!(SUMMARIES.get()[0] > 0, "{:?}", SUMMARIES.get());
        }
    }
}

#[cfg(test)]
mod r6_numeric_tests {
    use super::*;

    #[test]
    fn minimum_i128_divisor_keeps_the_full_remainder_interval() {
        let x = presburger::Atom::Sym("x".into());
        let mut tr = Tr::new(false);
        let n = tr.pair_by_constant(&Lin::atom(x.clone()), &Int::from(i128::MIN));
        let def = tr.defs[n as usize].2.clone();
        let samples = [
            (0i128, 0i128, 0i128),
            (1, 0, 1),
            (-1, 1, i128::MAX),
            (i128::MIN, 1, 0),
        ];
        for (v, q, r) in samples {
            let at = |qv: i128, rv: i128| {
                Formula::and(vec![
                    def.clone(),
                    Formula::Con(Con::eq(&Lin::atom(x.clone()), &Lin::constant(v))),
                    Formula::Con(Con::eq(
                        &Lin::atom(presburger::Atom::Aux(n)),
                        &Lin::constant(qv),
                    )),
                    Formula::Con(Con::eq(
                        &Lin::atom(presburger::Atom::Aux(n + 1)),
                        &Lin::constant(rv),
                    )),
                ])
            };
            assert_eq!(presburger::decide(&at(q, r)), Ok(true));
            assert_eq!(
                presburger::decide(&at(q, if r == 0 { 1 } else { 0 })),
                Ok(false)
            );
        }
    }
}
