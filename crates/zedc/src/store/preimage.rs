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

use zed_kernel::{Evaluator, Prim, Shared, Term, Value, World, eval, on_stack};

use super::int::Int;
use super::interval::{End, IntervalSet, Num};
use super::lattice::{Congruence, Landmarks, Lattice};
use super::presburger::{self, Con, Formula, Lin, Refusal, Relation};
use super::revision::{self, Exponent, Op, Tonicity, reduce_congruence};
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

/// The inputs on which the piecewise-affine summary of `term` ([`Pa`]) takes a value in `z`,
/// read without the transfer around it, or `None` when the summary of `term` or its inversion
/// is given up: for the tests that check where the summary exists and what it says.
#[doc(hidden)]
pub fn summary_preimage(term: &Term, inputs: &Domains, z: &IntervalSet) -> Option<Domains> {
    on_stack(|| {
        let mut tx = Tx::new();
        let root = tx.terms.add(term);
        let marks = tx.landmarks(inputs, &Demand::Ints(z.clone()));
        tx.start(inputs, marks);
        let pa = tx.pa(root, ROOT)?;
        let r = tx.invert_pa(&pa, z)?;
        Some(tx.whole(&r))
    })
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
    // A split by remainders found exact over the whole box is the preimage. The transfer over
    // the box, run first otherwise, reads a guard on a remainder inexactly when its set spans
    // more than two periods (row C17), and then reads a chain of such guards once for each
    // demand the chain's arms shift, `O(k^2)` for `k` guards; in a class the chain is read
    // once for all classes ([`Tx::by_class`]).
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
    // [`Tx::by_class`] does not read. Test:
    // `l01_25_preimage_catalog::s22::remainders_read_by_each_class_keep_the_transfer_first_scales`,
    // COMPLEXITY.md row S22e-quad. A complete solution would hold the congruence facet in
    // the backward transfer's sets, so that one transfer carries every class at once.
    //
    // A split that finds a mixed stretch over many periods ([`Split::Wide`]) is kept, and the
    // transfer and the split over the transfer's box run as without it: over that narrower box
    // the split may be exact where over the whole box it is not (`many_remainders` below
    // `i mod 1024 == 0`, row S22e-wide). When neither is exact the kept answer is the
    // preimage, its box met with the transfer's, and the linear stage is not run.
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
                early = Some((dom, found));
                whole_tried = true;
            }
            Split::NotExact => whole_tried = true,
            Split::Deferred => {}
        }
    }

    tx.start(inputs, marks.clone());
    let r = tx.back(root, ROOT, demand);
    let mut r = Whole {
        dom: tx.whole(&r),
        exact: r.exact,
    };
    let mut stops = std::mem::take(&mut tx.run.stops);
    let mut enumerated = false;
    if !r.exact && !is_empty(&r.dom) {
        tx.start(&r.dom, marks.clone());
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
            Split::Wide(dom, found) => return wide(term, dom, found, demand, stops),
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
        return wide(term, dom.collect(), found, demand, stops);
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

/// The preimage of a split by remainders over many periods ([`Split::Wide`]): its box, not
/// exact, with the classes' relation and the refusal that left the box wider, or the box
/// listed when it can be ([`enumerate`]). The linear stage is not run on the term
/// ([`split_residues`] says why).
fn wide(
    term: &Term,
    dom: Domains,
    (rel, why): ClassRelation,
    demand: &Demand,
    mut stops: Vec<Stop>,
) -> Preimage {
    let mut r = Whole { dom, exact: false };
    let mut enumerated = false;
    if let Some(e) = enumerate(term, &r.dom, demand) {
        r = e;
        enumerated = true;
    }
    stops.dedup();
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
/// with the refusal for which a disjunct was left out, as the linear stage projects its own
/// relation ([`linear`]), here with one pair of auxiliary variables for the split input.
fn project_classes(rel: &Relation, dom: &Domains) -> Result<(Domains, Option<Refusal>), Refusal> {
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
    Ok((out, skipped.first().copied()))
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
/// exactly ([`Tx::back_arith`]). The preimage is the union over the classes `R` of the
/// transfer's set `S_R` for `x` within `R`: the members of every `S_R`, and the members of
/// each `S_R` outside that common part whose remainder is in `R`. The other inputs must
/// have the same sets in every class whose set is not empty, so that the union is a box.
///
/// Design (COMPLEXITY.md rows S22e-quad and S22e-wide). (A) The runs of the classes share what
/// they compute without reading the class ([`Kept`]), and a term is read once for every class
/// as one summary over the classes ([`Tx::by_class`]): an `if` on the remainder takes its arms'
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
/// stage was slow and inexact for a cause in its translation, not in the term: it gives each
/// occurrence of `x mod m` its own pair of auxiliary variables, so `k` guards hold `k` pairs
/// whose projection is above linear, and its check of exactness decides the negated body, `k`
/// disjuncts. Now the split answers itself ([`Split::Wide`]): the classes' sets are one
/// relation with one pair of auxiliary variables for the split input, one flat disjunct for
/// each piece ([`residue_relation`]); the box is narrowed to its projection over the box's
/// hull, linear in the pieces ([`project_classes`]); and the box is exact when every member
/// lies in the set of its class, a sweep over the pieces with the classes marked in a Fenwick
/// tree, `O(P log P)` for `P` pieces, with no Presburger decision ([`covers`]). Before the
/// first transfer such an answer is kept, and the transfer and the split over its box run as
/// without it ([`preimage_in`]): over that narrower box the split may be exact where over the
/// whole box it is not. Measured from `k` to `8k`: `k` guards `i mod 1024 != j`, 17.3M to
/// 20.6M (`k` = 4; main 0.86G and 3.0G at 8 and 16, inexact), and `many_remainders(k)` below
/// `if (i mod 1024 == 0) { false }`, 85.9M to 498M (`k` = 4; main 11.3G and 84.1G at 8 and
/// 16, inexact); both are now exact.
///
/// Complexity tradeoff: a term the summary does not read is read by each class's run, `G`
/// times the cost of one transfer of it for `G` classes, and `G` is at most `2d + 1` for `d`
/// distinct constants compared: `O(G n log n)`, up to `O(n^2 log n)`, where that transfer is
/// `O(n log n)`. Such terms are listed at [`Tx::by_class`] (an `if` whose arms differ by more
/// than a constant in some class, a test of a term that reads a remainder, `min` and `max`
/// across their constant, values that may leave `i64`). The split is not tried when the terms
/// compare remainders of two inputs or two moduli, and it is given up when a class's transfer
/// is not exact or when two classes narrow another input differently; those inputs get the
/// linear stage's answer, as before. Why: the classes of two pairs combine as a product, `G1 *
/// G2` transfers, and boxes that differ in two inputs have a union that is not a box (row
/// C14). Trigger: a guard `x mod m == c` for `d` distinct `c` above such a term (the cost);
/// two remainders compared; another input narrowed by class. Test:
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
    marks: &Landmarks,
    early: bool,
) -> Split {
    let mut deferred = false;
    match split_classes(tx, root, dom, demand, marks, early, &mut deferred) {
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
    marks: &Landmarks,
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
    let mut common: Option<IntervalSet> = None;
    let mut rest: Option<Domains> = None;
    let mut classes = Vec::with_capacity(cuts.len() - 1);
    let mut marks = marks.clone();
    let mut kept = Kept::default();
    for (index, w) in cuts.windows(2).enumerate() {
        tx.start(dom, marks);
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
        let mut d = tx.whole(&r);
        let s = d.remove(&name).expect("the split input is an input");
        if !s.is_empty() {
            match &rest {
                Some(o) if *o != d => return None,
                Some(_) => {}
                None => rest = Some(d),
            }
        }
        common = Some(match common {
            Some(c) => c.meet(&s),
            None => s.clone(),
        });
        classes.push((s, class));
    }
    let common = common.expect("at least two classes");
    let mut pieces = common.pieces().to_vec();
    let mut wide = false;
    let mut parts = Vec::new();
    for (s, class) in &classes {
        let own = common.complement_in(s);
        for (lo, hi) in own.pieces() {
            // An end moves in to the nearest member of the class, which [`mod_pre`] leaves on
            // a half-line.
            let Some(within) = in_class(lo, hi, class, m) else {
                continue;
            };
            let (hull, exact) = mod_pre(class, c, &within);
            if exact {
                pieces.extend_from_slice(hull.pieces());
                continue;
            }
            // The merged periods between the first and the last are read once more, which
            // lists their own first and last, as the transfer's box split again did before.
            for (a, b) in hull.pieces() {
                let (part, exact) = mod_pre(class, c, &IntervalSet::range(a.clone(), b.clone()));
                wide |= !exact;
                pieces.extend_from_slice(part.pieces());
            }
        }
        if !own.is_empty() {
            parts.push((own, class));
        }
    }
    let Some(mut rest) = rest else {
        let none = dom.keys().map(|k| (k.clone(), IntervalSet::empty()));
        return Some((none.collect(), None));
    };
    rest.insert(name.clone(), IntervalSet::from_pieces(pieces));
    if !wide {
        return Some((rest, None));
    }
    // A stretch over more than two periods holds the class's remainders in each period, a
    // piece for each; the box holds their hull, and the relation the remainders. The box is
    // narrowed to the relation's projection, which lists the periods within the box, and is
    // exact when every member lies in the set of its class ([`covers`]).
    let rel = residue_relation(&name, c, &common, &parts);
    let (out, why) = match project_classes(&rel, &rest) {
        Ok(found) => found,
        Err(why) => (rest, Some(why)),
    };
    let sets: Vec<&IntervalSet> = classes.iter().map(|(s, _)| s).collect();
    if covers(&out[&name], &sets, &cuts, m) {
        return Some((out, None));
    }
    Some((out, Some((rel, why))))
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
    parts: &[(IntervalSet, &IntervalSet)],
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
    let mut body: Vec<Formula> = common.pieces().iter().map(|(lo, hi)| one(lo, hi)).collect();
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
            revision::tonicity(&op(p, None)?, arg)
        }
        (Lt | Le, 0) | (Gt | Ge, 1) | (Not, 0) => Tonicity::Down,
        (Lt | Le, 1) | (Gt | Ge, 0) | (And | Or, _) => Tonicity::Up,
        _ => return None,
    };
    (t != Tonicity::None).then_some(t)
}

/// The revision table's operator for a primitive, with the constant exponent of `**`.
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

/// The number of factors of a power, held by what the revision table reads of an exponent
/// ([`Exponent`]): its value while it fits in `u32`, and its parity. Nested squaring names
/// double the count at each name, so an exact count would cost `d` bits at depth `d`.
#[derive(Clone, Copy)]
struct Count {
    fits: Option<u32>,
    odd: bool,
}

impl Count {
    const ONE: Count = Count {
        fits: Some(1),
        odd: true,
    };

    fn add(self, other: Count) -> Count {
        Count {
            fits: self
                .fits
                .zip(other.fits)
                .and_then(|(j, k)| j.checked_add(k)),
            odd: self.odd != other.odd,
        }
    }

    /// Two or more factors: a count past `u32::MAX` is.
    fn is_several(self) -> bool {
        self.fits.is_none_or(|k| k > 1)
    }

    fn exponent(self) -> Exponent {
        match self.fits {
            Some(k) => k.into(),
            None => Exponent::Past { odd: self.odd },
        }
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
    /// A literal of another kind, a lambda, a primitive as a value, or a term outside the
    /// catalog: the term itself.
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
    by_form: HashMap<Form, Tid>,
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
        *seen.entry(s.id()).or_insert_with(|| self.number(s, todo))
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
    /// ([`Tx::by_class`]) is computed once for every copy. `O(1)` per term, each read once.
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
            Node::Lit(_) | Node::Lam(..) | Node::PrimFn(_) | Node::Other => Form::Own(t),
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
    /// The class of remainders the run is restricted to, by [`split_residues`].
    residue: Option<Residue>,
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
    /// Whether the run read a guard on the remainder by itself ([`Tx::back_arith`]), not from
    /// the summary over every class ([`Tx::by_class`]).
    alone: bool,
}

/// What a run computes without reading its class of remainders, kept from one class's run to
/// the next by [`split_residues`]: the forward values, constants, inputs read, clips and
/// reaches, the summaries of calls by number with their forward values, and the summaries
/// over every class ([`Tx::by_class`]).
#[derive(Default)]
struct Kept {
    sums: HashMap<Summary, u32>,
    fwds: HashMap<u32, Fwd>,
    fwd: HashMap<At, Fwd>,
    constant: HashMap<At, Option<Value>>,
    mentions: HashMap<At, Option<bool>>,
    clip: HashMap<At, Option<IntervalSet>>,
    by_class: HashMap<At, Option<ByClass>>,
    reads_mod: HashMap<At, bool>,
}

impl Run {
    /// Takes what the run computed without reading its class.
    fn keep(&mut self) -> Kept {
        let m = &mut self.memo;
        Kept {
            sums: std::mem::take(&mut self.sums),
            fwds: std::mem::take(&mut self.fwds),
            fwd: std::mem::take(&mut m.fwd),
            constant: std::mem::take(&mut m.constant),
            mentions: std::mem::take(&mut m.mentions),
            clip: std::mem::take(&mut m.clip),
            by_class: std::mem::take(&mut m.by_class),
            reads_mod: std::mem::take(&mut m.reads_mod),
        }
    }

    /// Puts back what [`Run::keep`] took, at the start of a run over the same box.
    fn restore(&mut self, k: Kept) {
        let m = &mut self.memo;
        (self.sums, self.fwds) = (k.sums, k.fwds);
        (m.fwd, m.constant, m.mentions) = (k.fwd, k.constant, k.mentions);
        (m.clip, m.by_class) = (k.clip, k.by_class);
        m.reads_mod = k.reads_mod;
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
    /// The piecewise-affine summary of an integer term of one input ([`Tx::pa`]).
    pa: HashMap<At, Option<Pa>>,
    /// The interval an integer demand on a term is met with before it is read ([`Tx::clip`]).
    clip: HashMap<At, Option<IntervalSet>>,
    /// The summaries of a term in every class of remainders of a split ([`Tx::by_class`]).
    by_class: HashMap<At, Option<ByClass>>,
    /// Whether a term may read a remainder, so that its transfer may depend on a split's class
    /// ([`Tx::reads_mod`]).
    reads_mod: HashMap<At, bool>,
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
    /// How each product, by the term and scope its names lead to, reads as a power ([`Tx::power`]).
    /// It depends on the terms and scopes alone, so it outlives one box.
    powers: HashMap<At, Power>,
    run: Run,
    cx: Cx,
}

impl<'t> Tx<'t> {
    fn new() -> Self {
        Tx {
            terms: Terms::default(),
            scopes: vec![Scope::new()],
            scope_ids: HashMap::new(),
            powers: HashMap::new(),
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
        let ends = |s: &IntervalSet| -> Vec<Num> {
            s.pieces()
                .iter()
                .flat_map(|(a, b)| [a, b])
                .filter_map(|e| match e {
                    Fin(v) => Some(v.clone()),
                    _ => None,
                })
                .collect()
        };
        let demanded = match demand {
            Demand::Ints(z) => ends(z),
            Demand::Bool(_) => Vec::new(),
        };
        let ints = (self.terms.ints.iter().cloned())
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

    /// The input `x` and modulus `c` of the remainders `x mod c` the terms compare with
    /// constants, and the ends of the classes those constants cut `[0, |c|)` into, from `0` to
    /// `|c|`: `None` unless one input and one modulus are compared, in two or more classes.
    /// The time is that of the terms' nodes, and the sorting of the ends.
    fn residue_cuts(&self, inputs: &Domains) -> Option<(Name, i64, Vec<i128>)> {
        let mut found = None;
        let mut cuts = Vec::new();
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
                if c == 0 || !inputs.contains_key(self.name(x)) {
                    continue;
                }
                // `x mod c` and `x mod -c` are the same remainder.
                let m = c.unsigned_abs() as i128;
                let (fx, fc) = *found.get_or_insert((x, c));
                if (fx, fc.unsigned_abs() as i128) != (x, m) {
                    return None;
                }
                cuts.extend([v as i128, v as i128 + 1].map(|e| e.clamp(0, m)));
            }
        }
        let (x, c) = found?;
        cuts.extend([0, c.unsigned_abs() as i128]);
        cuts.sort_unstable();
        cuts.dedup();
        (cuts.len() > 2).then_some((x, c, cuts))
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

    /// Whether the term may read a remainder `u mod c`: `false` only when it reads none,
    /// through its bindings, and calls no lambda. A run restricted to a class of remainders
    /// reads the class only at a remainder ([`Tx::back_arith`], [`Tx::residue_test`]), so the
    /// transfer of a term for which this is `false` is the same in every class.
    fn reads_mod(&mut self, t: Tid, env: Eid) -> bool {
        self.cached(|m| &mut m.reads_mod, (t, env), |s| s.reads_mod_at(t, env))
    }

    fn reads_mod_at(&mut self, t: Tid, env: Eid) -> bool {
        match self.node(t) {
            Node::Int(_) | Node::Bool(_) | Node::Lit(_) => false,
            Node::PrimFn(p) => p == Prim::Mod,
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.reads_mod(bt, be),
                None => false,
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.reads_mod(e, env) || self.reads_mod(b, inner)
            }
            Node::Prim(p, args) => {
                p == Prim::Mod || (0..args.len()).any(|i| self.reads_mod(self.arg(args, i), env))
            }
            Node::App(f, args) => {
                !matches!(self.callee(f, env), Ok(Callee::Prim(p)) if p != Prim::Mod)
                    || (0..args.len()).any(|i| self.reads_mod(self.arg(args, i), env))
            }
            Node::If(g, a, b) => {
                self.reads_mod(g, env) || self.reads_mod(a, env) || self.reads_mod(b, env)
            }
            Node::Lam(..) | Node::Other => true,
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
                Term::Lam(names, Shared::new(self.close(b, env, &inner)?))
            }
            Node::App(f, args) => Term::App(Shared::new(c(f)?), all(args)?),
            Node::Prim(p, args) => Term::Prim(p, all(args)?),
            Node::If(g, a, b) => {
                Term::If(Shared::new(c(g)?), Shared::new(c(a)?), Shared::new(c(b)?))
            }
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

    /// The constant exponent `t` of a `**`, when it is an integer at least 0, of any size: a
    /// kernel integer past the 64-bit range is kept as the kernel holds it, unbuilt.
    fn exponent(&mut self, t: Tid, env: Eid) -> Option<Exponent> {
        match self.constant(t, env)? {
            Value::Int(n) if n >= 0 => Some(Int::from(n).into()),
            Value::Big(k) if !k.is_negative() => Some(Exponent::Big(k)),
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

    /// The product `t` as a power, when it multiplies two or more factors that are all the same
    /// term: that factor, the scope it is read in, and the number of factors. Any number of
    /// factors is read (DESIGN.md sec:constraints, "How a constraint reaches the domains").
    fn power(&mut self, t: Tid, env: Eid) -> Option<(Tid, Eid, Exponent)> {
        let at = self.followed(t, env);
        self.read_powers(at);
        match self.powers[&at] {
            Some((f, fe, k)) if k.is_several() => Some((f, fe, k.exponent())),
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
                    self.powers.insert(at, Some((t, env, Count::ONE)));
                    continue;
                }
            };
            let a = self.followed(self.arg(args, 0), env);
            let b = self.followed(self.arg(args, 1), env);
            match (self.powers.get(&a), self.powers.get(&b)) {
                (Some(pa), Some(pb)) => {
                    todo.pop();
                    let p = self.joined(*pa, *pb);
                    self.powers.insert(at, p);
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
    /// `2^64` factors at the 64th name, so the count is a [`Count`], O(1) to add.
    fn joined(&self, a: Power, b: Power) -> Power {
        let ((s, se, j), (u, ue, k)) = (a?, b?);
        let alike = match (self.node(s), self.node(u)) {
            (Node::Var(x), Node::Var(y)) if x == y => true,
            _ => se == ue && self.same(s, u),
        };
        if !alike {
            return None;
        }
        Some((s, se, j.add(k)))
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
            Node::Lit(Value::Big(n)) => Fwd::int(IntervalSet::point(Num::from(&**n))),
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
            return self.arith(&Op::Pow(k), &b, &b, false);
        }
        let fwd = |s: &mut Self, i: usize| s.fwd(s.arg(args, i), env);
        match p {
            Neg | Abs => {
                let a = fwd(self, 0);
                self.arith(&op(p, None).expect("scalar"), &a, &a, false)
            }
            Pow => match self.exponent(self.arg(args, 1), env) {
                Some(k) => {
                    let a = fwd(self, 0);
                    self.arith(&Op::Pow(k), &a, &a, false)
                }
                None => Fwd::top(),
            },
            Add | Sub | Mul | IntDiv | Mod | Min | Max => {
                let a = fwd(self, 0);
                let b = fwd(self, 1);
                let by_zero = matches!(p, IntDiv | Mod) && b.ints.contains(0);
                self.arith(&op(p, None).expect("scalar"), &a, &b, by_zero)
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
    fn arith(&self, o: &Op, a: &Fwd, b: &Fwd, by_zero: bool) -> Fwd {
        Fwd {
            ints: revision::forward(o, &a.ints, &b.ints),
            fails: !a.is_int() || !b.is_int() || by_zero,
            ..Fwd::none()
        }
    }

    // ---- Clipping demands ---------------------------------------------------------------

    /// An interval that holds every integer value of the term, for a term whose backward
    /// result under an integer demand `z` is its result under `z` met with the interval:
    /// an input, a literal, a name bound to such a term, a constant added to or subtracted
    /// from one, a choice between two of them, and their `min` or `max`. `None` for any other
    /// term.
    fn clip(&mut self, t: Tid, env: Eid) -> Option<IntervalSet> {
        self.cached(|m| &mut m.clip, (t, env), |s| s.clip_at(t, env))
    }

    fn clip_at(&mut self, t: Tid, env: Eid) -> Option<IntervalSet> {
        if let Node::Var(x) = self.node(t) {
            return match self.lookup(env, x) {
                Some((bt, be)) => self.clip(bt, be),
                None => self.cx.inputs.get(self.name(x)).map(|dom| dom.hull()),
            };
        }
        // As in [`Tx::back_in`], a term that reads no input is decided by running it.
        match self.constant(t, env) {
            Some(Value::Int(n)) => return Some(IntervalSet::single(n)),
            Some(_) => return None,
            None => {}
        }
        match self.node(t) {
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.clip(b, inner)
            }
            Node::If(_, a, b) => {
                let fa = self.clip(a, env)?;
                let fb = self.clip(b, env)?;
                Some(fa.join(&fb).hull())
            }
            Node::Prim(p @ (Prim::Add | Prim::Sub), args) if args.len() == 2 => {
                let (a, b) = (self.arg(args, 0), self.arg(args, 1));
                match (p, self.constant_int(a, env), self.constant_int(b, env)) {
                    (Prim::Add, Some(c), None) => Some(shift(&self.clip(b, env)?, c as i128)),
                    (Prim::Add, None, Some(c)) => Some(shift(&self.clip(a, env)?, c as i128)),
                    (Prim::Sub, None, Some(c)) => Some(shift(&self.clip(a, env)?, -(c as i128))),
                    (Prim::Sub, Some(c), None) => Some(reflect(&self.clip(b, env)?, c as i128)),
                    _ => None,
                }
            }
            // `min` and `max` are monotone in each operand, so their hull is the operator on
            // the operands' ends.
            Node::Prim(p @ (Prim::Min | Prim::Max), args) if args.len() == 2 => {
                let (ca, cb) = (
                    self.clip(self.arg(args, 0), env)?,
                    self.clip(self.arg(args, 1), env)?,
                );
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

    fn back(&mut self, t: Tid, env: Eid, d: &Demand) -> Res {
        self.back_at(t, env, d)
    }

    fn back_at(&mut self, t: Tid, env: Eid, d: &Demand) -> Res {
        // An integer demand is read as its meet with the term's values, so that demands that
        // differ only outside them are one.
        let met;
        let d = match d {
            Demand::Ints(z) => {
                let clip = self.clip(t, env);
                match clip {
                    Some(f) => {
                        met = Demand::Ints(z.meet(&f));
                        &met
                    }
                    None => d,
                }
            }
            _ => d,
        };
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
                if let Demand::Ints(z) = d
                    && let Some(r) = self.pa(t, env).and_then(|pa| self.invert_pa(&pa, z))
                {
                    return r;
                }
                if let Some(index) = self.run.residue.as_ref().map(|r| r.index) {
                    // A test in a class of remainders: the summary over every class, 1 where
                    // it holds and 0 where it fails.
                    if let Demand::Bool(w) = *d
                        && self.fwd(t, env).is_bool()
                        && let Some(pa) = self.by_class(t, env).and_then(|c| c.get(index))
                        && let Some(r) = self.invert_pa(&pa, &IntervalSet::of(w.into(), w.into()))
                    {
                        return r;
                    }
                    // A guard on the remainder takes one arm throughout the class.
                    if let Some(yes) = self.residue_test(g, env) {
                        let taken = yes.iter().any(|&(i, j)| i <= index && index <= j);
                        return self.back_at(if taken { a } else { b }, env, d);
                    }
                }
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
            return self.back_unary(&Op::Pow(k), base, be, z);
        }
        let a = self.arg(args, 0);
        match p {
            Neg | Abs => {
                return self.back_unary(&op(p, None).expect("scalar"), a, env, z);
            }
            Pow => {
                let b = self.arg(args, 1);
                return match self.exponent(b, env) {
                    Some(k) => self.back_unary(&Op::Pow(k), a, env, z),
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
            (Sub, Some(c), _) => self.back_at(b, env, &ints(reflect(z, c as i128))),
            (Mul, Some(c), _) => self.back_at(b, env, &ints(times_pre(z, c))),
            (Mul, _, Some(c)) => self.back_at(a, env, &ints(times_pre(z, c))),
            (IntDiv, _, Some(c)) => self.back_at(a, env, &ints(div_pre(z, c))),
            (Mod, _, Some(c)) => {
                // Within the run's class of remainders of the input `a`, every point is in `z`
                // or none is.
                let m = c.unsigned_abs() as i128;
                let class = match self.node(a) {
                    Node::Var(x) if self.lookup(env, x).is_none() => self
                        .run
                        .residue
                        .as_mut()
                        .filter(|r| r.x == x && r.m == m)
                        .map(|r| {
                            r.alone = true;
                            (r.class.is_subset(z), r.class.meet(z).is_empty())
                        }),
                    _ => None,
                };
                match class {
                    Some((true, _)) => return self.back_at(a, env, &ints(IntervalSet::top())),
                    Some((_, true)) => return Res::none(),
                    _ => {}
                }
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
                let up = IntervalSet::range(lo.clone(), fhi.clone()).is_subset(z);
                let down = IntervalSet::range(flo.clone(), hi.clone()).is_subset(z);
                // min ≥ lo: both are; max ≤ hi: both are. The other rays: either is. When
                // the demand holds the whole forward range, both rays apply; the upward one is
                // taken.
                let both = (p == Min && up) || (p == Max && down && !up);
                let either = (p == Min && down && !up) || (p == Max && up);
                if both || either {
                    let r = if up {
                        IntervalSet::range(lo.clone(), PosInf)
                    } else {
                        IntervalSet::range(NegInf, hi.clone())
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
    fn back_unary(&mut self, o: &Op, c: Tid, env: Eid, z: &IntervalSet) -> Res {
        if let Op::Pow(k) = o
            && k.is_zero()
        {
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
        let za = revision::backward(&o, 0, &fa, &fb, z);
        let zb = revision::backward(&o, 1, &fa, &fb, z);
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

    // ---- Piecewise-affine summaries -----------------------------------------------------

    /// The value of the term as a piecewise-affine function of one input ([`Pa`]), or `None`
    /// when it is not one or when it reads more than one input. Its coefficients, constants
    /// and values lie in `i128` ([`finite`]), and an infinite end of a piece is the limit of
    /// its line there, so `t + 1` over all integers is a summary. Keyed on the term alone, so
    /// an `if` chain whose arms read one shared term is summarized once, whatever demands
    /// reach it.
    fn pa(&mut self, t: Tid, env: Eid) -> Option<Pa> {
        if self.run.void {
            return None;
        }
        // In a class of remainders, an `if` the summary over every class reads is looked up
        // there, so that the classes share one reading of the term.
        if matches!(self.node(t), Node::If(..))
            && !self.fwd(t, env).has_bools()
            && let Some(index) = self.run.residue.as_ref().map(|r| r.index)
            && let Some(p) = self.by_class(t, env).and_then(|b| b.get(index))
        {
            return Some(p);
        }
        self.cached(|m| &mut m.pa, (t, env), |s| s.pa_at(t, env))
    }

    fn pa_at(&mut self, t: Tid, env: Eid) -> Option<Pa> {
        if !matches!(self.node(t), Node::Var(_))
            && let Some(v) = self.constant(t, env)
        {
            return match v {
                Value::Int(c) => Some(Pa::Const(c)),
                _ => None,
            };
        }
        match self.node(t) {
            Node::Int(c) => Some(Pa::Const(c)),
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.pa(bt, be),
                None => {
                    let name = self.name(x);
                    self.cx.inputs.contains_key(name).then(|| Pa::Linear {
                        var: name.clone(),
                        a: 1,
                        b: 0,
                    })
                }
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.pa(b, inner)
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Prim(p)) => {
                    let c = self.terms.call(t, p, args);
                    self.pa(c, env)
                }
                _ => None,
            },
            Node::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => {
                self.pa_prim(t, p, args, env)
            }
            Node::If(g, a, b) => self.pa_if(g, a, b, env),
            _ => None,
        }
    }

    /// An `if` whose guard narrows at most the one input its arms read: the arms' treaps
    /// sliced to the inputs that take each arm, joined in order. Exact, since both guard
    /// results must be.
    fn pa_if(&mut self, g: Tid, a: Tid, b: Tid, env: Eid) -> Option<Pa> {
        let gt = self.back_at(g, env, &Demand::Bool(true));
        let gf = self.back_at(g, env, &Demand::Bool(false));
        if !gt.exact || !gf.exact {
            return None;
        }
        let pa = self.pa(a, env)?;
        let pb = self.pa(b, env)?;
        self.pa_select(g, env, &pa, &pb)
    }

    /// The summary that is `pa` on the inputs where the test `g` holds and `pb` where it
    /// fails ([`Tx::pa_if`]).
    fn pa_select(&mut self, g: Tid, env: Eid, pa: &Pa, pb: &Pa) -> Option<Pa> {
        let gt = self.back_at(g, env, &Demand::Bool(true));
        let gf = self.back_at(g, env, &Demand::Bool(false));
        if !gt.exact || !gf.exact {
            return None;
        }
        let (yes, no) = (!self.empty(&gt), !self.empty(&gf));
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
        let dom = self.cx.inputs.get(var)?;
        let mut slices = Vec::new();
        for (taken, r, arm) in [(yes, &gt, pa), (no, &gf, pb)] {
            if !taken {
                continue;
            }
            let set = r.dom.get(var).map_or(&**dom, |s| &**s);
            let tree = arm.to_treap(dom)?;
            if !in_range(set) {
                return None;
            }
            for (lo, hi) in set.pieces() {
                if let Some(s) = slice_treap(tree.clone(), lo, hi)? {
                    slices.push((key(lo), s));
                }
            }
        }
        slices.sort_by_key(|&(lo, _)| lo);
        let mut root = None;
        for (_, s) in slices {
            root = join_treap(root, Some(s))?;
        }
        Some(Pa::Piecewise {
            var: var.clone(),
            root,
        })
    }

    /// `-u`, `u + c`, `c + u`, `u - c`, `c - u` and `c * u` for a summarized `u` and a
    /// constant `c`; the arity was checked by the caller.
    fn pa_prim(&mut self, t: Tid, p: Prim, args: Span, env: Eid) -> Option<Pa> {
        let a = self.arg(args, 0);
        match p {
            Prim::Neg => self.pa(a, env)?.affine(-1, 0),
            Prim::Add => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_int(a, env) {
                    return self.pa(b, env)?.affine(1, c.into());
                }
                let c = self.constant_int(b, env)?;
                self.pa(a, env)?.affine(1, c.into())
            }
            Prim::Sub => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_int(b, env) {
                    return self.pa(a, env)?.affine(1, -i128::from(c));
                }
                let c = self.constant_int(a, env)?;
                self.pa(b, env)?.affine(-1, c.into())
            }
            Prim::Mul => {
                if self.power(t, env).is_some() {
                    return None;
                }
                let b = self.arg(args, 1);
                let (c, u) = match self.constant_int(a, env) {
                    Some(c) => (c, b),
                    None => (self.constant_int(b, env)?, a),
                };
                if c == 0 {
                    return None;
                }
                self.pa(u, env)?.affine(c.into(), 0)
            }
            _ => None,
        }
    }

    /// The summary ([`Tx::pa`]) of the term in every class of remainders of the run's split
    /// ([`split_residues`]), built once for all classes, with a test's `false` and `true` read
    /// as 0 and 1: `None` outside a split, and for a term other than those read here.
    ///
    /// - An `if` whose guard compares the split's remainder with a constant: in each class such
    ///   a guard is true throughout or false throughout, so the `if` is the arm it takes, and
    ///   the summaries of the classes are those of the `no` arm with the classes where the
    ///   guard holds taken from the `yes` arm, `O(log G)` for `G` classes. Such a comparison
    ///   as a value is read the same way, as an `if` with arms 1 and 0.
    /// - A term that reads no remainder ([`Tx::reads_mod`]): its transfer is the same in every
    ///   class, so its summary is read once, [`Tx::pa_at`], or for a test the one that is 1
    ///   and 0 on the sets the transfer finds exactly where it holds and where it fails.
    /// - An `if` on a test that reads no remainder: when both arms are one summary in every
    ///   class, the summary of the `if` is too, sliced once ([`Tx::pa_select`]); when the arms
    ///   add constants to one tree whose summaries are a base plus a constant in each class
    ///   (`t` and `t + 1` for one `t`, [`ByClass`]), the tree is kept and its base is sliced
    ///   once, `O(log n)`, since adding a constant commutes with slicing by the guard's sets.
    /// - `-u`, `u + c`, `u - c`, `c - u` and `c * u`: every summary is mapped, `O(1)`; `not u`
    ///   is `1 - u`; `min` and `max` of `u` and a constant `c` are `u` or `c` in every class
    ///   when the forward values of `u`, the same in every class, lie on one side of `c`.
    ///
    /// Complexity tradeoff: a term this does not read is read in each class by its own run,
    /// `O(G n log n)` for `G` classes, as before this summary (row S22e). Given up: an `if` on
    /// a test that reads no remainder whose arms differ by more than a constant in some class,
    /// or whose classes' summaries are not one base plus a constant (each class's summary is
    /// then sliced in its own way, so the classes share no step); a test of a term that reads
    /// a remainder (its set in each class is the inverse of that class's own summary); `min`
    /// and `max` whose other argument's values cross the constant; and a term whose values or
    /// coefficients may pass `i64::MAX` in magnitude (the summary checks them on the bounds of
    /// every class at once, where the transfer checks each class). Trigger: such a term between
    /// the root and the remainder guards, for example `if i >= 3 { t } else { -t }`, `t >= 0`
    /// below an `if` on the remainder, `min(t, 5)` with `t` on both sides of 5, or a domain
    /// unbounded on either side. Test:
    /// `l01_25_preimage_catalog::s22::remainder_chains_outside_the_shared_summary_keep_their_preimages`,
    /// COMPLEXITY.md rows S22e-quad and S22e-wide. A complete solution would hold the
    /// congruence facet in the backward transfer's sets (`x mod m` in a set of classes beside
    /// the interval), so that one transfer carries every class at once.
    fn by_class(&mut self, t: Tid, env: Eid) -> Option<ByClass> {
        let t = self.terms.form(t);
        self.cached(|m| &mut m.by_class, (t, env), |s| s.by_class_at(t, env))
    }

    fn by_class_at(&mut self, t: Tid, env: Eid) -> Option<ByClass> {
        let n = self.run.residue.as_ref()?.cuts.len() - 1;
        // As in [`Tx::pa_at`].
        if !matches!(self.node(t), Node::Var(_))
            && let Some(v) = self.constant(t, env)
        {
            return match v {
                Value::Int(c) => ByClass::constant(c, n),
                Value::Bool(b) => ByClass::constant(b.into(), n),
                _ => None,
            };
        }
        let read = self.by_class_node(t, env, n);
        if read.is_some() || matches!(self.node(t), Node::Var(_)) || self.reads_mod(t, env) {
            return read;
        }
        // The transfer of the term is the same in every class.
        let pa = if self.fwd(t, env).is_bool() {
            self.pa_select(t, env, &Pa::Const(1), &Pa::Const(0))?
        } else {
            self.pa_at(t, env)?
        };
        let var = pa.var().cloned();
        let x = match &var {
            Some(v) => self.magnitude(v)?,
            None => 0,
        };
        let bound = Bound::of(&pa, x);
        ByClass::based(pa, var, bound, n)
    }

    /// The largest magnitude of the domain of the input `var`, when it is bounded.
    fn magnitude(&self, var: &Arc<str>) -> Option<u128> {
        let (lo, hi) = self.cx.inputs.get(var)?.bounds()?;
        Some(input(lo)?.unsigned_abs().max(input(hi)?.unsigned_abs()))
    }

    /// [`Tx::by_class`] of the term by its kind.
    fn by_class_node(&mut self, t: Tid, env: Eid, n: usize) -> Option<ByClass> {
        match self.node(t) {
            Node::Int(c) => ByClass::constant(c, n),
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.by_class(bt, be),
                None => {
                    let name = self.name(x).clone();
                    let bound = Bound {
                        a: 1,
                        b: 0,
                        x: self.magnitude(&name)?,
                        mul: 1,
                    };
                    let pa = Pa::Linear {
                        var: name.clone(),
                        a: 1,
                        b: 0,
                    };
                    ByClass::based(pa, Some(name), bound, n)
                }
            },
            Node::Let(m, e, b) => {
                let inner = self.let_env(m, e, env);
                self.by_class(b, inner)
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Prim(p)) => {
                    let c = self.terms.call(t, p, args);
                    self.by_class(c, env)
                }
                _ => None,
            },
            Node::Prim(p, args) if p.arity().is_none_or(|k| k == args.len()) => {
                self.by_class_prim(t, p, args, env, n)
            }
            Node::If(g, a, b) => match self.residue_test(g, env) {
                Some(yes) => {
                    let ca = self.by_class(a, env)?;
                    let cb = self.by_class(b, env)?;
                    ByClass::choose(&ca, &cb, &yes)
                }
                None => self.by_class_if(g, a, b, env),
            },
            _ => None,
        }
    }

    /// [`Tx::by_class`] of an `if` whose guard `g` is not on the split's remainder.
    fn by_class_if(&mut self, g: Tid, a: Tid, b: Tid, env: Eid) -> Option<ByClass> {
        if self.reads_mod(g, env) {
            return None;
        }
        let ca = self.by_class(a, env)?;
        let cb = self.by_class(b, env)?;
        let bound = ca.bound.max(cb.bound);
        if ca.adds
            && cb.adds
            && Rc::ptr_eq(&ca.root, &cb.root)
            && let (Some(u), Some(v)) = (&ca.base, &cb.base)
            && same_pa(u, v)
        {
            // In class `i` the arms are `u + d_i + ca.shift` and `u + d_i + cb.shift`.
            let pa = u.affine(1, ca.shift)?;
            let pb = u.affine(1, cb.shift)?;
            let base = self.pa_select(g, env, &pa, &pb)?;
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
        let (pa, pb) = (ca.uniform()?, cb.uniform()?);
        let pa = self.pa_select(g, env, &pa, &pb)?;
        let var = pa.var().cloned().or(ca.var.clone());
        ByClass::based(pa, var, bound, ca.n)
    }

    /// [`Tx::pa_prim`] over every class.
    fn by_class_prim(
        &mut self,
        t: Tid,
        p: Prim,
        args: Span,
        env: Eid,
        n: usize,
    ) -> Option<ByClass> {
        let a = self.arg(args, 0);
        match p {
            Prim::Neg => self.by_class(a, env)?.affine((-1, 0)),
            Prim::Not => self.by_class(a, env)?.affine((-1, 1)),
            Prim::Add => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_int(a, env) {
                    return self.by_class(b, env)?.affine((1, c.into()));
                }
                let c = self.constant_int(b, env)?;
                self.by_class(a, env)?.affine((1, c.into()))
            }
            Prim::Sub => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_int(b, env) {
                    return self.by_class(a, env)?.affine((1, -i128::from(c)));
                }
                let c = self.constant_int(a, env)?;
                self.by_class(b, env)?.affine((-1, c.into()))
            }
            Prim::Mul => {
                if self.power(t, env).is_some() {
                    return None;
                }
                let b = self.arg(args, 1);
                let (c, u) = match self.constant_int(a, env) {
                    Some(c) => (c, b),
                    None => (self.constant_int(b, env)?, a),
                };
                if c == 0 {
                    return None;
                }
                self.by_class(u, env)?.affine((c.into(), 0))
            }
            Prim::Min | Prim::Max => {
                let b = self.arg(args, 1);
                let (c, u) = match self.constant_int(a, env) {
                    Some(c) => (c, b),
                    None => (self.constant_int(b, env)?, a),
                };
                // The forward values are read over the box, the same in every class.
                let f = self.fwd(u, env);
                let (Fin(lo), Fin(hi)) = f.ints.bounds()? else {
                    return None;
                };
                let c_num = Num::from(c);
                let (below, above) = (*hi <= c_num, *lo >= c_num);
                match (p, below, above) {
                    (Prim::Min, true, _) | (Prim::Max, _, true) => self.by_class(u, env),
                    (Prim::Min, _, true) | (Prim::Max, true, _) => ByClass::constant(c, n),
                    _ => None,
                }
            }
            Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge | Prim::Eq | Prim::Ne => {
                let yes = self.residue_test(t, env)?;
                ByClass::choose(&ByClass::constant(1, n)?, &ByClass::constant(0, n)?, &yes)
            }
            _ => None,
        }
    }

    /// The classes of the run's split in which the test `g` is true, as ranges of class
    /// numbers, when `g` compares the split's remainder `x mod c` with a constant in the way
    /// [`Tx::back_compare`] reads as a demand on the remainder, so that in each class the
    /// transfer finds the test true throughout or false throughout ([`Tx::back_arith`]).
    fn residue_test(&mut self, g: Tid, env: Eid) -> Option<Vec<(usize, usize)>> {
        let Node::Prim(p @ (Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge | Prim::Eq | Prim::Ne), args) =
            self.node(g)
        else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let (a, b) = (self.arg(args, 0), self.arg(args, 1));
        if !self.fwd(a, env).is_int() || !self.fwd(b, env).is_int() {
            return None;
        }
        let (r, z) = match self.constant_int(b, env) {
            Some(v) => (a, ray(p, v)),
            None => (b, ray(mirror(p), self.constant_int(a, env)?)),
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
        let c = self.constant_int(self.arg(margs, 1), env)?;
        let res = self.run.residue.as_ref()?;
        if res.x != x || res.m != c.unsigned_abs() as i128 {
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
            // The cuts hold the ends of every such test's set ([`Tx::residue_cuts`]).
            if res.cuts[i] != lo || res.cuts[j + 1] != hi + 1 {
                return None;
            }
            yes.push((i, j));
        }
        Some(yes)
    }

    /// The inputs on which `pa` takes a value in `z`, or `None` when an intermediate value
    /// leaves `i128` and the caller reads the `if` as before.
    fn invert_pa(&self, pa: &Pa, z: &IntervalSet) -> Option<Res> {
        let (var, dom) = match pa {
            Pa::Const(c) => {
                return Some(if z.contains(*c) {
                    Res::all()
                } else {
                    Res::none()
                });
            }
            Pa::Linear { var, .. } | Pa::Piecewise { var, .. } => (var, self.cx.inputs.get(var)?),
        };
        if !in_range(z) {
            return None;
        }
        let root = pa.to_treap(dom)?;
        let mut pieces = Vec::new();
        invert_treap(&root, (1, 0), z, &mut pieces)?;
        let met = IntervalSet::from_pieces(pieces).meet(dom);
        if met.is_empty() {
            return Some(Res::none());
        }
        let mut r = Res::all();
        if met != **dom {
            r.dom.insert(var.clone(), Rc::new(met));
        }
        Some(r)
    }
}

/// An integer term as a function of one input `var` (R1_GEMINI Thm 3.1: the value of a term
/// built from one input by `if`s on that input, constants, negation, adding a constant and
/// multiplying by one is affine on each of finitely many intervals of the input, cut at the
/// domain's and the guards' ends). The coefficients, constants and values lie in `i128`, every
/// step checked there, so an affine step ([`Pa::affine`], [`apply_tag`]) is given up only when
/// one leaves `i128`. Kernel integers are unbounded, so a value outside `i64` is a value of the
/// term, and the summary reads it as one: `i64::MIN - (u + 3)` is summarized, although its
/// constant `i64::MIN - 3` lies outside `i64`, and so is `u + 1` at `u = i64::MAX`. At an
/// infinite end of the domain a piece takes the infinity its line tends to ([`value_at`]),
/// never the value at an end of `i64`.
#[derive(Clone)]
enum Pa {
    /// The constant `c` everywhere.
    Const(i64),
    /// `a * var + b` over the whole domain of `var`.
    Linear { var: Arc<str>, a: i128, b: i128 },
    /// Disjoint intervals of `var`, on each of which the value is affine; a gap is a part of
    /// the domain where the term has no integer value.
    Piecewise { var: Arc<str>, root: Tree },
}

impl Pa {
    fn var(&self) -> Option<&Arc<str>> {
        match self {
            Pa::Const(_) => None,
            Pa::Linear { var, .. } | Pa::Piecewise { var, .. } => Some(var),
        }
    }

    /// `mul * self + add`, or `None` when a coefficient or a constant leaves `i128`, or the
    /// value of a [`Pa::Const`], the term's one value, leaves `i64`.
    fn affine(&self, mul: i128, add: i128) -> Option<Pa> {
        match self {
            Pa::Const(c) => {
                let v = i128::from(*c).checked_mul(mul)?.checked_add(add)?;
                Some(Pa::Const(i64::try_from(v).ok()?))
            }
            Pa::Linear { var, a, b } => Some(Pa::Linear {
                var: var.clone(),
                a: a.checked_mul(mul)?,
                b: b.checked_mul(mul)?.checked_add(add)?,
            }),
            Pa::Piecewise { var, root } => Some(Pa::Piecewise {
                var: var.clone(),
                root: match root {
                    Some(r) => Some(apply_tag(r, (mul, add))?),
                    None => None,
                },
            }),
        }
    }

    /// The treap over `dom`, the domain of the input.
    fn to_treap(&self, dom: &IntervalSet) -> Option<Tree> {
        let (a, b) = match self {
            Pa::Piecewise { root, .. } => return Some(root.clone()),
            Pa::Const(c) => (0, i128::from(*c)),
            Pa::Linear { a, b, .. } => (*a, *b),
        };
        if !in_range(dom) {
            return None;
        }
        let mut root = None;
        for (lo, hi) in dom.pieces() {
            root = join_treap(
                root,
                Some(make_node(lo.clone(), hi.clone(), a, b, None, None)?),
            )?;
        }
        Some(root)
    }
}

/// The summaries ([`Pa`]) of one term in each of the `n` classes of remainders of a split
/// ([`Tx::by_class`]), as a persistent tree over the class numbers `0..n`: a node covers a
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
/// ([`Tx::by_class_if`]).
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
/// that each class's summary is the one its own run computes ([`Tx::pa`]).
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
        let (a, b) = match pa {
            Pa::Const(c) => (0, c.unsigned_abs().into()),
            Pa::Linear { a, b, .. } => (a.unsigned_abs(), b.unsigned_abs()),
            Pa::Piecewise { root: None, .. } => (0, 0),
            Pa::Piecewise { root: Some(r), .. } => {
                (0, r.vals.0.unsigned_abs().max(r.vals.1.unsigned_abs()))
            }
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
        ByClass::same(Pa::Const(c), None, bound, n)
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
            Leaf::Own(pa) => pa.affine(f.0, f.1),
            Leaf::Base(g) => {
                let f = compose(*g, f)?;
                self.base.as_ref()?.affine(f.0, f.1)
            }
        }
    }
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
                    (Some(x), Some(y)) => Rc::ptr_eq(x, y),
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
        Cls::Same(Leaf::Own(pa)) => Cls::Same(Leaf::Own(pa.affine(f.0, f.1)?)),
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
/// shared by every summary built from it. Splitting, joining and a change of every value
/// by an affine map each take `O(log n)` expected time.
type Tree = Option<Rc<PaNode>>;

/// One piece of a [`Pa`] and the subtree it roots.
#[derive(Clone)]
struct PaNode {
    /// The piece: the inputs `lo..=hi`, on which the value is `a * x + b`.
    lo: End,
    hi: End,
    a: i128,
    b: i128,
    /// The least and the greatest input in the subtree.
    span: (End, End),
    /// The least and the greatest value in the subtree, so that inverting skips a subtree
    /// whose values miss the demand.
    vals: (i128, i128),
    /// Whether the subtree's pieces cover `span` with no gap, so that a subtree whose values
    /// lie in one piece of the demand is taken whole.
    dense: bool,
    /// A heap priority, fixed by the piece's ends, so the shape does not depend on the order
    /// of the operations that built it.
    prio: u64,
    /// The affine map `(mul, add)` still to be applied to both children: `a`, `b` and `vals`
    /// of this node already include it.
    tag: (i128, i128),
    left: Tree,
    right: Tree,
}

/// The infinities among a summary's values ([`PaNode::vals`]): the value an affine piece with
/// an infinite end tends to there. Every finite value lies strictly between them ([`finite`]).
const NEG: i128 = i128::MIN;
const POS: i128 = i128::MAX;

/// `v` when it lies strictly between the infinities [`NEG`] and [`POS`].
// Complexity tradeoff: a summary whose coefficient, constant or value leaves `i128` is given
// up (`None` from [`value_at`], [`map_vals`], [`apply_tag`], [`Pa::affine`] and
// [`invert_piece`]), and the `if` it was to summarize is read arm by arm by the transfer
// before: exact, at the cost of the per-arm transfer, about `k^2.8` on an `if` chain of `k`
// levels over a shared term. Why: the treap's coefficients, constants and values are `i128`,
// which keeps each treap operation O(1) per node; numbers of any size would cost time in
// their bits at every node and step. Trigger: a value of a kept arm, a coefficient or a
// constant past about `2^127` in magnitude. Test:
// `l01_25_preimage_catalog::wide_ends::values_past_i128_take_the_transfer_before`.
// COMPLEXITY.md S22. A complete solution would hold the treap's numbers as `Num`.
fn finite(v: i128) -> Option<i128> {
    (NEG < v && v < POS).then_some(v)
}

/// The value `a * x + b` at the end `x` of a piece: at an infinite end, the infinity the line
/// tends to there, or `b` when `a` is 0; `None` when a finite value leaves `i128`.
fn value_at(x: &End, a: i128, b: i128) -> Option<i128> {
    match x {
        Fin(v) => finite(a.checked_mul(small(v))?.checked_add(b)?),
        _ if a == 0 => finite(b),
        NegInf if a > 0 => Some(NEG),
        PosInf if a < 0 => Some(NEG),
        _ => Some(POS),
    }
}

/// Whether every finite end of `s` lies strictly between the infinities [`NEG`] and [`POS`],
/// as the summary's ends must: they are compared as `i128` with the infinities as its ends.
// Complexity tradeoff: the piecewise-affine summary of an `if` chain is given up when a
// domain or a demand it reads has a finite end past `i128`, and the `if` is read as before
// S22a (each arm by the catalog): exact, at the cost of the per-arm transfer, about `k^2.8`
// on a chain of `k` levels over a shared term. Why: the summary's pieces, values and tags are
// `i128`, which keeps each treap operation O(1) per node; ends of any size would cost time in
// their bits at every node. Trigger: an input domain, an arm's set or a demand with a finite
// end of magnitude about `2^127` or more. Test:
// `l01_25_preimage_catalog::wide_ends::ends_past_i128_take_the_transfer_before`.
// COMPLEXITY.md S33. A complete solution would hold the pieces' ends and values as `Num`.
fn in_range(s: &IntervalSet) -> bool {
    s.pieces().iter().all(|(lo, hi)| {
        [lo, hi]
            .into_iter()
            .all(|e| !matches!(e, Fin(v) if v.to_i128().and_then(finite).is_none()))
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

/// An end of an input's domain as an input, for the bounds of [`ByClass`]: the infinities are
/// the ends of `i64`, and `None` for a finite end outside `i64`.
fn input(e: &End) -> Option<i128> {
    match e {
        NegInf => Some(i64::MIN.into()),
        Fin(v) => v.to_i64().map(i128::from),
        PosInf => Some(i64::MAX.into()),
    }
}

/// `(lo, hi)` mapped by `x -> mul * x + add`, in order, for `mul` not 0: an infinity stays one
/// of the same sign when `mul > 0` and becomes the other when `mul < 0`; `None` when a finite
/// value leaves `i128`.
fn map_vals((lo, hi): (i128, i128), (mul, add): (i128, i128)) -> Option<(i128, i128)> {
    let f = |v: i128| match v {
        NEG | POS if mul > 0 => Some(v),
        NEG => Some(POS),
        POS => Some(NEG),
        _ => finite(v.checked_mul(mul)?.checked_add(add)?),
    };
    if mul >= 0 {
        Some((f(lo)?, f(hi)?))
    } else {
        Some((f(hi)?, f(lo)?))
    }
}

/// The map `inner` followed by `outer`.
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

/// The node for the piece `lo..=hi` with value `a * x + b` over two subtrees with no tag
/// above them; `None` when a value leaves `i128`.
fn make_node(lo: End, hi: End, a: i128, b: i128, left: Tree, right: Tree) -> Option<Rc<PaNode>> {
    let (u, v) = (value_at(&lo, a, b)?, value_at(&hi, a, b)?);
    let mut vals = (u.min(v), u.max(v));
    let mut span = (lo.clone(), hi.clone());
    let mut dense = true;
    let next = |x: &End, y: &End| matches!((x, y), (Fin(x), Fin(y)) if small(x) + 1 == small(y));
    if let Some(l) = &left {
        vals = (vals.0.min(l.vals.0), vals.1.max(l.vals.1));
        span.0 = l.span.0.clone();
        dense &= l.dense && next(&l.span.1, &lo);
    }
    if let Some(r) = &right {
        vals = (vals.0.min(r.vals.0), vals.1.max(r.vals.1));
        span.1 = r.span.1.clone();
        dense &= r.dense && next(&hi, &r.span.0);
    }
    let prio = prio_of(&lo, &hi);
    Some(Rc::new(PaNode {
        lo,
        hi,
        a,
        b,
        span,
        vals,
        dense,
        prio,
        tag: (1, 0),
        left,
        right,
    }))
}

/// The subtree with every value mapped by `x -> mul * x + add`, in `O(1)`; `None` when a
/// coefficient, a constant or a value leaves `i128`.
fn apply_tag(node: &Rc<PaNode>, f: (i128, i128)) -> Option<Rc<PaNode>> {
    if f == (1, 0) {
        return Some(node.clone());
    }
    let (mul, add) = f;
    Some(Rc::new(PaNode {
        a: node.a.checked_mul(mul)?,
        b: node.b.checked_mul(mul)?.checked_add(add)?,
        vals: map_vals(node.vals, f)?,
        tag: compose(node.tag, f)?,
        ..(**node).clone()
    }))
}

/// The two children with the node's tag applied.
fn push_down(node: &PaNode) -> Option<(Tree, Tree)> {
    let tagged = |c: &Tree| match c {
        Some(c) => apply_tag(c, node.tag).map(Some),
        None => Some(None),
    };
    Some((tagged(&node.left)?, tagged(&node.right)?))
}

/// The pieces of `left`, then those of `right`, which all lie above them.
fn join_treap(left: Tree, right: Tree) -> Option<Tree> {
    match (left, right) {
        (None, r) => Some(r),
        (l, None) => Some(l),
        (Some(l), Some(r)) => {
            if l.prio >= r.prio {
                let (ll, lr) = push_down(&l)?;
                let nr = join_treap(lr, Some(r))?;
                make_node(l.lo.clone(), l.hi.clone(), l.a, l.b, ll, nr).map(Some)
            } else {
                let (rl, rr) = push_down(&r)?;
                let nl = join_treap(Some(l), rl)?;
                make_node(r.lo.clone(), r.hi.clone(), r.a, r.b, nl, rr).map(Some)
            }
        }
    }
}

/// The inputs below `cut`, and the rest. A piece that holds `cut - 1` and `cut` is cut in
/// two; both lie in `i128`, since `cut` is above the piece's lower end and at most its upper
/// end, which [`in_range`] admitted.
fn split_at(root: Tree, cut: i128) -> Option<(Tree, Tree)> {
    let Some(node) = root else {
        return Some((None, None));
    };
    if cut <= key(&node.span.0) {
        return Some((None, Some(node)));
    }
    if cut > key(&node.span.1) {
        return Some((Some(node), None));
    }
    let (left, right) = push_down(&node)?;
    let (lo, hi, a, b) = (node.lo.clone(), node.hi.clone(), node.a, node.b);
    if cut <= key(&lo) {
        let (ll, lr) = split_at(left, cut)?;
        Some((ll, Some(make_node(lo, hi, a, b, lr, right)?)))
    } else if cut > key(&hi) {
        let (rl, rr) = split_at(right, cut)?;
        Some((Some(make_node(lo, hi, a, b, left, rl)?), rr))
    } else {
        let (below, above) = (End::from(cut - 1), End::from(cut));
        let l = join_treap(left, Some(make_node(lo, below, a, b, None, None)?))?;
        let r = join_treap(Some(make_node(above, hi, a, b, None, None)?), right)?;
        Some((l, r))
    }
}

/// The pieces of `root` within `lo..=hi`, whose finite ends lie strictly between the
/// infinities ([`in_range`]), so that a cut is never confused with an infinity.
fn slice_treap(root: Tree, lo: &End, hi: &End) -> Option<Tree> {
    let root = match lo {
        Fin(v) => split_at(root, small(v))?.1,
        _ => root,
    };
    match hi {
        Fin(v) => Some(split_at(root, small(v) + 1)?.0),
        _ => Some(root),
    }
}

/// Appends to `out` the inputs of `node`'s subtree whose value, mapped by `f` (the tags
/// above it), lies in `z`. A subtree whose values miss `z` is skipped, and one whose values
/// lie in one piece of `z` and whose pieces leave no gap is taken whole, so the time is
/// `O((m + 1) log n)` for `m` pieces met.
fn invert_treap(
    node: &Tree,
    f: (i128, i128),
    z: &IntervalSet,
    out: &mut Vec<(End, End)>,
) -> Option<()> {
    let Some(n) = node else {
        return Some(());
    };
    let (lo, hi) = map_vals(n.vals, f)?;
    let zs = z.pieces();
    let i = zs.partition_point(|(_, zhi)| key(zhi) < lo);
    let Some((zlo, zhi)) = zs.get(i) else {
        return Some(());
    };
    if key(zlo) > hi {
        return Some(());
    }
    if n.dense && key(zlo) <= lo && hi <= key(zhi) {
        out.push(n.span.clone());
        return Some(());
    }
    let below = compose(n.tag, f)?;
    invert_treap(&n.left, below, z, out)?;
    let (a, b) = compose((n.a, n.b), f)?;
    invert_piece(&n.lo, &n.hi, a, b, z, out)?;
    invert_treap(&n.right, below, z, out)
}

/// Appends to `out` the inputs `x` in `lo..=hi` with `a * x + b` in `z`. Exact, so no end is
/// rounded: an infinite end of the piece is a limit of the line, never an input, and an input
/// found may lie outside `i64`.
fn invert_piece(
    lo: &End,
    hi: &End,
    a: i128,
    b: i128,
    z: &IntervalSet,
    out: &mut Vec<(End, End)>,
) -> Option<()> {
    let (u, v) = (value_at(lo, a, b)?, value_at(hi, a, b)?);
    let (vlo, vhi) = (u.min(v), u.max(v));
    let zs = z.pieces();
    let start = zs.partition_point(|(_, zhi)| key(zhi) < vlo);
    for (zlo, zhi) in &zs[start..] {
        if key(zlo) > vhi {
            break;
        }
        if a == 0 {
            // The one value, `b`, lies in this piece of `z`.
            out.push((lo.clone(), hi.clone()));
            break;
        }
        // The inputs whose value lies in `zlo..=zhi`, where an infinite end of `z` bounds
        // none. A coefficient may lie outside `i64`, so the differences with `b` are checked.
        let (xl, xh) = if a > 0 {
            (
                solve(zlo, |zl| ceil_div(zl.checked_sub(b)?, a), NegInf)?,
                solve(zhi, |zh| Some(floor_div(zh.checked_sub(b)?, a)), PosInf)?,
            )
        } else {
            let d = a.checked_neg()?;
            (
                solve(zhi, |zh| ceil_div(b.checked_sub(zh)?, d), NegInf)?,
                solve(zlo, |zl| Some(floor_div(b.checked_sub(zl)?, d)), PosInf)?,
            )
        };
        let (xl, xh) = (xl.max(lo.clone()), xh.min(hi.clone()));
        if xl <= xh {
            out.push((xl, xh));
        }
    }
    Some(())
}

/// `f` of the finite end `e`, as an end, or `inf` when `e` is infinite.
fn solve(e: &End, f: impl FnOnce(i128) -> Option<i128>, inf: End) -> Option<End> {
    match e {
        Fin(_) => f(key(e)).map(End::from),
        _ => Some(inf),
    }
}

/// `n / d` rounded down, for `d > 0`.
fn floor_div(n: i128, d: i128) -> i128 {
    n.div_euclid(d)
}

/// `n / d` rounded up, for `d > 0`; `None` for `n = i128::MIN`.
fn ceil_div(n: i128, d: i128) -> Option<i128> {
    Some(-n.checked_neg()?.div_euclid(d))
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
    fn one(x: &IntervalSet) -> Option<(&End, &End)> {
        x.bounds().filter(|(l, h)| l == h)
    }
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
    IntervalSet::from_pieces(z.pieces().iter().map(|(lo, hi)| (m(lo), m(hi))).collect())
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
    IntervalSet::from_pieces(
        z.pieces()
            .iter()
            .rev()
            .map(|(lo, hi)| (m(hi), m(lo)))
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
            .iter()
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
            .iter()
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
            .iter()
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
    let mut axes: Vec<(Arc<str>, Vec<Num>)> = Vec::new();
    for (k, s) in dom {
        let mut vs = Vec::new();
        for (lo, hi) in s.pieces() {
            match (lo, hi) {
                (Fin(lo), Fin(hi)) if (hi - lo) <= Num::ONE => {
                    vs.push(lo.clone());
                    if hi != lo {
                        vs.push(hi.clone());
                    }
                }
                _ => return None,
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
                t = Term::Let(
                    k.clone(),
                    Shared::new(Term::Lit(Value::from(v))),
                    Shared::new(t),
                );
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
