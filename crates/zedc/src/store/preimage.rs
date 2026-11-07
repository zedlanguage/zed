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

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Arc;

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Pattern, Prim, Shared, Term, Value, World, eval, on_stack};

use super::int::Int;
use super::interval::{End, IntervalSet, Num};
use super::landmarks::Landmarks;
use super::lattice::{Congruence, Lattice};
use super::presburger::{self, Con, Formula, Joining, Lin, Mark, Refusal, Relation};
use super::revision::{self, Exponent, Op, Tonicity, reduce_congruence};
use crate::stage;
use End::{Fin, NegInf, PosInf};
use zed_kernel::frames::{Deep, Stack};

/// The box of a term whose value `v` is known: every point when `v` meets the demand, none
/// otherwise.
fn decided(d: &Demand, v: &Value) -> Res {
    if d.holds(v) { Res::all() } else { Res::none() }
}

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
    // `store::preimage::tests::a_chain_split_by_two_classes_is_read_in_time_near_its_length`.
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
    Ok((out, skipped.first().cloned()))
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
    let mut tr = Tr::new(products);
    let mut out = Vec::new();
    for t in terms {
        let root = tx.terms.add(t);
        let first = tr.defs.len();
        let body = tx.relation(&mut tr, root, ROOT)?;
        out.push(Relation {
            body,
            defs: tr.written(first),
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
pub struct Scoped<'t> {
    tx: Tx<'t>,
    scope: Eid,
    /// The translations kept, with the `products` they were made under.
    kept: Option<(bool, Translations)>,
    /// The kept translations of calls, by each name their arguments' terms hold: a call whose
    /// arguments name what is not an input of the body read next is dropped before it, so what
    /// is kept is what a body over the same names can find again, and a unit whose bodies
    /// name their inputs apart (`x@1`, `x@2`) holds O(n) entries, not each body's calls.
    by_name: HashMap<Arc<str>, Vec<Rc<Logged>>>,
    /// The auxiliary variables of every relation read under the `products` of `kept`, each
    /// numbered once for the scope, so that a kept translation that holds one serves every
    /// body (LOAD-chain-aux).
    tr: Tr,
    /// The coordinates of each function whose relation was read, by its body: each parameter
    /// as an atom and a constant added to it ([`Frame`]) (LOAD-chain-args).
    frames: HashMap<*const Term, Frame>,
    /// For the relation read last, each atom of its coordinates as its input less the
    /// constant: `x = a + c`, so `a = x - c`, by which [`Scoped::written`] writes the relation
    /// over the inputs. Empty when the coordinates are the inputs.
    back: HashMap<Arc<str>, Lin>,
}

/// The coordinates a relation of [`Scoped`] is read in: for each parameter, the atom and the
/// constant whose sum it is bound to, the atoms distinct. Each input so has one value for each
/// value of the atoms and back, and whether the relation can hold or fail is the same in
/// either. A caller whose call passes each of its callee's parameters one of its own plus a
/// constant (`p(x: x + 1)`, `p(y: x)`) is read in its callee's coordinates, so the call's
/// arguments are the terms its callee's own calls were translated under, and its translation is
/// shared (LOAD-chain-args).
type Frame = Vec<(Arc<str>, i64)>;

/// The translation tables of a [`Memo`], kept by [`Scoped`] from one body to the next.
#[derive(Default)]
struct Translations {
    lin: HashMap<At, Entry<Option<Lin>>>,
    formula: HashMap<At, Entry<Option<Formula>>>,
    lin_calls: HashMap<CallKey, Entry<Option<Lin>>>,
    formula_calls: HashMap<CallKey, Entry<Option<Formula>>>,
}

impl Memo {
    /// Takes the translation tables.
    fn take_translations(&mut self) -> Translations {
        Translations {
            lin: std::mem::take(&mut self.lin),
            formula: std::mem::take(&mut self.formula),
            lin_calls: std::mem::take(&mut self.lin_calls),
            formula_calls: std::mem::take(&mut self.formula_calls),
        }
    }

    /// Puts back the tables [`Memo::take_translations`] took.
    fn put_translations(&mut self, t: Translations) {
        (self.lin, self.formula) = (t.lin, t.formula);
        (self.lin_calls, self.formula_calls) = (t.lin_calls, t.formula_calls);
    }
}

impl<'t> Scoped<'t> {
    /// The scope of `lets`, a chain of `let`s whose last body is never read: each name bound
    /// to its term, read in the scope of the names bound before it.
    pub fn new(lets: &'t Term) -> Self {
        let mut tx = Tx::new();
        tx.start(&Domains::new(), Landmarks::none());
        let mut t = tx.terms.add(lets);
        let mut scope = ROOT;
        while let Node::Let(n, e, b) = tx.node(t) {
            scope = tx.let_env(n, e, scope);
            t = b;
        }
        Scoped {
            tx,
            scope,
            kept: None,
            by_name: HashMap::new(),
            tr: Tr::new(false),
            frames: HashMap::new(),
            back: HashMap::new(),
        }
    }

    /// The body of the relation the linear-relation domain states for the test `body` of
    /// parameters `params` over the free names `inputs`, the i-th parameter standing for the
    /// i-th input, read under the scope, its auxiliary variables defined by [`Scoped::def`]:
    /// the relation [`Scoped::written`] writes is the one [`relations`] states over `inputs`
    /// for `body` closed by the scope's lets, under lets outside them that bind each
    /// parameter to its input. A parameter so names its input whatever the scope binds, a
    /// prelude word or a definition of the unit; an input named like a prelude word, `min`,
    /// is the input. Products of two symbols are atoms when `products` holds. `None` when the
    /// body is outside the domain. Time of the body, of the parameters and of the parts of the
    /// scope no earlier body read.
    pub fn relation(
        &mut self,
        body: &'t Term,
        params: &[Arc<str>],
        inputs: &[Arc<str>],
        products: bool,
    ) -> Option<Formula> {
        debug_assert_eq!(params.len(), inputs.len(), "one input for each parameter");
        let tx = &mut self.tx;
        let doms: Domains = inputs
            .iter()
            .map(|n| (n.clone(), IntervalSet::top()))
            .collect();
        // A new run over the body's inputs, with what the runs before it found of the terms
        // without reading the inputs.
        let kept = tx.run.keep();
        tx.start(&doms, Landmarks::none());
        tx.run.restore(kept);
        tx.fresh = Some(Fresh::new(
            tx.terms.nodes.len() as Tid,
            tx.scopes.len() as Eid,
        ));
        let root = tx.terms.add(body);
        let past = tx.terms.nodes.len() as Tid;
        // Each parameter bound to its input, read where the scope binds nothing. The input's
        // term is the body's own, so what is found of it, which reads the input, is dropped
        // with the body's entries and never meets a body of other inputs.
        let mut own = self.scope;
        for (p, x) in params.iter().zip(inputs) {
            let (p, x) = (tx.terms.name(p), tx.terms.name(x));
            let to = (tx.terms.own_var(x), ROOT);
            own = tx.bind(own, p, to);
        }
        // The translations the bodies before made under the same `products`.
        let m = &mut tx.run.memo;
        m.log.clear();
        match self.kept.take() {
            Some((p, t)) if p == products => m.put_translations(t),
            _ => {
                self.by_name.clear();
                self.tr = Tr::new(products);
            }
        }
        // The body read in its callee's coordinates when it has them ([`Frame`]): each
        // parameter bound to its atom plus its constant, the atoms the inputs.
        let frame = self.coordinates(root..past, own, inputs, products);
        let tx = &mut self.tx;
        let mut scope = own;
        if frame
            .iter()
            .zip(inputs)
            .any(|((a, c), x)| a != x || *c != 0)
        {
            scope = self.scope;
            for (p, (a, c)) in params.iter().zip(&frame) {
                let (p, a) = (tx.terms.name(p), tx.terms.name(a));
                let to = (tx.terms.own_sum(a, *c), ROOT);
                scope = tx.bind(scope, p, to);
            }
            tx.cx.inputs = (frame.iter())
                .map(|(a, _)| (a.clone(), Rc::new(IntervalSet::top())))
                .collect();
        }
        self.frames.insert(body as *const Term, frame.clone());
        let m = &mut tx.run.memo;
        // O(the names held and the inputs), each dropped entry once.
        let names: HashSet<&Arc<str>> = frame.iter().map(|(a, _)| a).collect();
        self.by_name.retain(|name, keys| {
            if names.contains(name) {
                return true;
            }
            for k in keys.drain(..) {
                match &*k {
                    Logged::LinCall(k) => _ = m.lin_calls.remove(k),
                    Logged::FormulaCall(k) => _ = m.formula_calls.remove(k),
                    Logged::Lin(_) | Logged::Formula(_) => {}
                }
            }
            false
        });
        let body = tx.formula(&mut self.tr, root, scope);
        // The calls this body translated and kept, each under the names its arguments hold:
        // O(the size of their keys).
        fn sym(f: &presburger::Factor) -> Option<&Arc<str>> {
            match f {
                presburger::Factor::Sym(s) => Some(s),
                presburger::Factor::Aux(_) => None,
            }
        }
        for e in tx.run.memo.log.drain(..) {
            let (Logged::LinCall(k) | Logged::FormulaCall(k)) = &e else {
                continue;
            };
            let mut named: Vec<&Arc<str>> = Vec::new();
            for a in k.1.iter().flat_map(|l| l.terms.keys()) {
                let (f, g) = match a {
                    presburger::Atom::Sym(s) => (Some(s), None),
                    presburger::Atom::Product(f, g) => (sym(f), sym(g)),
                    presburger::Atom::Aux(_) => (None, None),
                };
                named.extend(f.into_iter().chain(g));
            }
            named.sort_unstable();
            named.dedup();
            let named: Vec<Arc<str>> = named.into_iter().cloned().collect();
            let e = Rc::new(e);
            for s in named {
                self.by_name.entry(s).or_default().push(e.clone());
            }
        }
        tx.drop_fresh();
        self.kept = Some((products, tx.run.memo.take_translations()));
        self.back = (frame.into_iter().zip(inputs))
            .filter(|((a, c), x)| a != *x || *c != 0)
            .map(|((a, c), x)| {
                let x = Lin::atom(presburger::Atom::Sym(x.clone()));
                (a, x.minus(&Lin::constant(c)))
            })
            .collect();
        body
    }

    /// The coordinates to read the body of the terms `body` in ([`Frame`]): those of the first
    /// call in it, in the order the terms are numbered, to a function whose relation was read,
    /// whose arguments are each one of the body's parameters plus a constant, no parameter
    /// twice, and whose coordinates leave free the names of the parameters it is not passed;
    /// each parameter as its input when there is none. `own` binds each parameter to its
    /// input. The arguments are translated under `own` and their entries forgotten. Time of the
    /// body's terms and of the arguments of the calls to such functions.
    ///
    /// The coordinates only choose which atoms the relation is written over, so another choice
    /// changes no answer, only which translations are shared. Complexity tradeoff: a call that
    /// passes a multiple (`x: 2 * x`), a constant, or one parameter twice (`x: x, y: x`) leaves
    /// the body in its own coordinates, and its callee is translated again under it, so a chain
    /// of n such links costs O(n²) (COMPLEXITY.md row LOAD-chain-args; a map that is not a
    /// bijection of the integers changes whether the relation holds at an integer point).
    fn coordinates(
        &mut self,
        body: std::ops::Range<Tid>,
        own: Eid,
        inputs: &[Arc<str>],
        products: bool,
    ) -> Frame {
        let identity = || inputs.iter().map(|x| (x.clone(), 0)).collect();
        if self.frames.is_empty() {
            return identity();
        }
        let at: HashMap<&Arc<str>, usize> =
            inputs.iter().enumerate().map(|(i, x)| (x, i)).collect();
        let tx = &mut self.tx;
        for t in body {
            let Node::App(f, args) = tx.node(t) else {
                continue;
            };
            let Ok(Callee::Lam(ps, b, _)) = tx.callee(f, own) else {
                continue;
            };
            let Some(callee) = (tx.terms.src[b as usize])
                .and_then(|b| self.frames.get(&(b as *const Term)))
                .filter(|c| c.len() == ps.len() && ps.len() == args.len())
            else {
                continue;
            };
            let logged = tx.run.memo.log.len();
            let mut tr = Tr::new(products);
            let mut frame: Vec<Option<(Arc<str>, i64)>> = vec![None; inputs.len()];
            let mut through = || {
                for (i, (a, d)) in callee.iter().enumerate() {
                    // The argument is `x + c` for the parameter `x` standing for input `j`; the
                    // callee's parameter is `a + d`, so `x` is `a + d - c`.
                    let l = tx.lin(&mut tr, tx.arg(args, i), own)?;
                    let mut terms = l.terms.iter();
                    let (Some((presburger::Atom::Sym(x), one)), None) =
                        (terms.next(), terms.next())
                    else {
                        return None;
                    };
                    let j = *at.get(x).filter(|_| *one == Int::ONE)?;
                    let c = d.checked_sub(i64::try_from(l.constant.to_i128()?).ok()?)?;
                    if frame[j].replace((a.clone(), c)).is_some() {
                        return None;
                    }
                }
                Some(())
            };
            let found = through();
            tx.forget(logged);
            if found.is_none() {
                continue;
            }
            // The parameters the call is not passed keep their inputs, unless the callee's
            // coordinates name one of them.
            let named: HashSet<&Arc<str>> = frame.iter().flatten().map(|(a, _)| a).collect();
            if (frame.iter().zip(inputs)).any(|(f, x)| f.is_none() && named.contains(x)) {
                continue;
            }
            return (frame.into_iter().zip(inputs))
                .map(|(f, x)| f.unwrap_or_else(|| (x.clone(), 0)))
                .collect();
        }
        identity()
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

    /// Whether the relation read last was read in coordinates other than its inputs
    /// (`Frame`). O(1).
    pub fn moved(&self) -> bool {
        !self.back.is_empty()
    }

    /// The relation of `body`, the body [`Scoped::relation`] gave last: over its inputs, each
    /// atom of its coordinates (`Frame`) written as the input it stands for, with the
    /// definitions it reaches, its auxiliary variables numbered from 0 in the order the scope
    /// numbered them.
    /// It is the relation [`relations`] states for the body closed over the definitions it
    /// reaches, but for the numbering of the auxiliary variables when a definition was made
    /// for another body first. For a message and for tests: time of the body and of the
    /// definitions it reaches.
    pub fn written(&self, body: &Formula) -> Relation {
        use presburger::Atom;
        let auxes = |f: &Formula| -> Vec<u32> {
            let mut out = Vec::new();
            for a in f.atoms() {
                match a {
                    Atom::Aux(n) => out.push(n),
                    Atom::Product(f, g) => {
                        for h in [f, g] {
                            if let presburger::Factor::Aux(n) = h {
                                out.push(n);
                            }
                        }
                    }
                    Atom::Sym(_) => {}
                }
            }
            out
        };
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
        if reached.is_empty() && self.back.is_empty() {
            return Relation {
                body: body.clone(),
                defs: Vec::new(),
            };
        }
        reached.sort_unstable();
        let at: HashMap<u32, u32> = (reached.iter().enumerate())
            .map(|(i, &n)| (n, i as u32))
            .collect();
        let to = |n: u32| at[&n];
        let lin = |l: &Lin| renumbered(l, &to, &self.back);
        let renumber = |f: &Formula| {
            f.map_cons(&|c| {
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
        Relation {
            body: renumber(body),
            defs,
        }
    }

    /// The number of scopes and remembered entries the scope holds from one body to the next:
    /// O(n) after n bodies, whatever the bodies read (LOAD-chain).
    pub fn held(&self) -> usize {
        let (tx, m) = (&self.tx, &self.tx.run.memo);
        let kept = self.kept.as_ref().map_or(0, |(_, t)| {
            t.lin.len() + t.formula.len() + t.lin_calls.len() + t.formula_calls.len()
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
    let mut tr = Tr::new(false);
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
            Ok(meets) => (out, !meets, skipped.first().cloned()),
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
}

impl Tr {
    fn new(products: bool) -> Tr {
        Tr {
            defs: Vec::new(),
            products,
            pairs: HashMap::new(),
            made: Vec::new(),
        }
    }

    /// The definitions from `first` on, as a [`Relation`] lists them.
    fn written(&self, first: usize) -> Vec<(u32, String, Formula)> {
        (self.defs[first..].iter())
            .map(|(n, w, f)| (*n, w.to_string(), f.clone()))
            .collect()
    }

    /// Undoes the definitions from `mark` on, and the pairs among them.
    fn truncate(&mut self, mark: usize) {
        self.defs.truncate(mark);
        while let Some(key) = self.made.last()
            && self.pairs[key] as usize >= mark
        {
            self.pairs.remove(key);
            self.made.pop();
        }
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
    /// leaves one; where `n` is 0 the operation fails, and `q` and `r` are left free, so no
    /// fact about them is proved there. `a div n` and `a mod n` share the pair. `None` when `n`
    /// is a constant or holds a product.
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
    ByConstant(&'static str, Lin, i128),
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
        match self {
            What::ByConstant(op, a, c) => format!("{} {op} {c}", operand(&l(a))),
            What::ByTerm(op, a, n) => format!("{} {op} {}", operand(&l(a)), operand(&l(n))),
            What::If(g, a, b) => {
                let g = match to {
                    Some(to) => g.map_cons(&|c| {
                        Formula::Con(Con {
                            lin: to(&c.lin),
                            rel: c.rel,
                        })
                    }),
                    None => g.clone(),
                };
                format!("if {g} then {} else {}", l(a), l(b))
            }
            What::Abs(a) => format!("abs({})", l(a)),
            What::Min(a, b) => format!("min({}, {})", l(a), l(b)),
            What::Max(a, b) => format!("max({}, {})", l(a), l(b)),
        }
    }
}

impl fmt::Display for What {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.written(None))
    }
}

/// `l` with each auxiliary variable `n` numbered `to(n)` and each atom that `back` maps
/// replaced by what it maps it to, a product of two factors by the product of what they are
/// replaced by. Time of the terms of `l` and of what they are replaced by, times the log of
/// their number.
fn renumbered(l: &Lin, to: &dyn Fn(u32) -> u32, back: &HashMap<Arc<str>, Lin>) -> Lin {
    use presburger::{Atom, Factor};
    let factor = |f: &Factor| match f {
        Factor::Aux(n) => Lin::atom(Atom::Aux(to(*n))),
        Factor::Sym(s) => (back.get(s).cloned()).unwrap_or_else(|| Lin::atom(f.atom())),
    };
    let mut out = Lin::constant(l.constant.clone());
    for (a, c) in &l.terms {
        let v = match a {
            Atom::Aux(n) => factor(&Factor::Aux(*n)),
            Atom::Sym(s) => factor(&Factor::Sym(s.clone())),
            Atom::Product(f, g) => (factor(f).product(&factor(g)))
                .expect("two factors, each an atom plus a constant, multiply"),
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
/// value whose carrier is inferred: an arm `is f64` or `is rat` for each carrier it follows,
/// each to a literal, and last the literal itself. Any other match is outside the catalog.
pub(super) fn follow_own(arms: &[(Pattern, Term)]) -> Option<&Term> {
    let ((Pattern::Wild, own), rest) = arms.split_last()? else {
        return None;
    };
    let carrier = |(p, v): &(Pattern, Term)| {
        matches!(p, Pattern::Is(t) if *t == Type::f64() || *t == Type::rat())
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

    /// `x + c` as a term shared with no other, as [`Terms::own_var`] makes `x`.
    fn own_sum(&mut self, x: Name, c: i64) -> Tid {
        let x = self.own_var(x);
        if c == 0 {
            return x;
        }
        let n = self.nodes.len() as Tid;
        self.nodes.push(Node::Int(c));
        self.src.push(None);
        let at = self.kids.len();
        self.kids.extend([x, n]);
        let t = self.nodes.len() as Tid;
        self.nodes.push(Node::Prim(Prim::Add, Span::new(at, 2)));
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
}

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
/// reaches, the summaries of calls by number with their forward values, and the summaries
/// over every class ([`Walk::by_class`]).
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
        }
    }

    /// Puts back what [`Run::keep`] took, at the start of a run over the same box.
    fn restore(&mut self, k: Kept) {
        let m = &mut self.memo;
        (self.sums, self.sids, self.fwds) = (k.sums, k.sids, k.fwds);
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
    mentions: HashMap<At, Entry<Option<bool>>>,
    constant: HashMap<At, Entry<Option<Value>>>,
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
type Table<K, V> = fn(&mut Memo) -> &mut HashMap<K, Entry<V>>;

/// A context: the inputs it reads, those of the transfer and the parameters of the summaries
/// it is within.
struct Cx {
    inputs: Sets,
    /// The lowest place on the stack of lambdas being read whose lambda a call stopped at,
    /// since the result being computed began. A result is remembered wherever it is reached
    /// only when that place is not below the stack's height when it began; otherwise it
    /// depends on the lambdas below that height, and is remembered while they are there
    /// ([`Entry`]).
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
    /// What the body being read by [`Scoped::relation`] made, which [`Tx::drop_fresh`] drops.
    fresh: Option<Fresh>,
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
            fresh: None,
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
            let inputs = &self.cx.inputs;
            let table = (self.remainder_cuts(|k| inputs.contains_key(k)).into_iter())
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
    /// earlier terms are dropped, and those of `tr`'s earlier terms are not reused.
    fn relation(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Formula> {
        let m = &mut self.run.memo;
        m.lin.clear();
        m.formula.clear();
        m.lin_calls.clear();
        m.formula_calls.clear();
        m.log.clear();
        tr.pairs.clear();
        tr.made.clear();
        self.formula(tr, t, env)
    }

    /// [`Walk::formula`] on a new stack, adding to the translation `tr`.
    fn formula(&mut self, tr: &mut Tr, t: Tid, env: Eid) -> Option<Formula> {
        let w = Walk::translating(self, tr);
        w.stack.run(w.formula(t, env))
    }

    /// The largest magnitude of the domain of the input `var`, when it is bounded.
    fn magnitude(&self, var: &Arc<str>) -> Option<u128> {
        let (lo, hi) = self.cx.inputs.get(var)?.bounds()?;
        Some(input(lo)?.unsigned_abs().max(input(hi)?.unsigned_abs()))
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
}

impl<'m, 't> Walk<'m, 't> {
    fn new(tx: &'m mut Tx<'t>) -> Self {
        Walk {
            tx: RefCell::new(tx),
            tr: None,
            stack: Stack::default(),
        }
    }

    /// A walk that translates into the linear-relation domain, adding to `tr`.
    fn translating(tx: &'m mut Tx<'t>, tr: &'m mut Tr) -> Self {
        Walk {
            tx: RefCell::new(tx),
            tr: Some(RefCell::new(tr)),
            stack: Stack::default(),
        }
    }

    /// `f` on the transfer's state. `f` must not reach `self`, which it could only borrow again.
    fn with<R>(&self, f: impl FnOnce(&mut Tx<'t>) -> R) -> R {
        f(&mut self.tx.borrow_mut())
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
                    tx.cx.inputs.contains_key(x)
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

    /// The term with every bound name replaced by the closed term it is bound to, for a term
    /// that reads no input. `local` holds the names bound within the term being closed: to
    /// the closed term a `let` binds, or to `None` for a lambda's parameter, which stays.
    fn close(&'m self, t: Tid, env: Eid, local: Rc<Local>) -> Deep<'m, Option<Term>> {
        self.stack.call(move || self.close_at(t, env, local))
    }

    async fn close_all(&'m self, args: Span, env: Eid, local: &Rc<Local>) -> Option<Vec<Term>> {
        let mut out = Vec::with_capacity(args.len());
        for i in 0..args.len() {
            out.push(self.close(self.arg(args, i), env, local.clone()).await?);
        }
        Some(out)
    }

    async fn close_at(&'m self, t: Tid, env: Eid, local: Rc<Local>) -> Option<Term> {
        Some(match self.node(t) {
            Node::Var(x) => match (local.get(&x), self.lookup(env, x)) {
                (Some(Some(bound)), _) => (**bound).clone(),
                (Some(None), _) | (None, None) => Term::Var(self.name(x)),
                (None, Some((bt, be))) => self.close(bt, be, Rc::new(Local::new())).await?,
            },
            Node::Int(n) => Term::Lit(Value::Int(n)),
            Node::Bool(b) => Term::Lit(Value::Bool(b)),
            Node::Lit(v) => Term::Lit(v.clone()),
            Node::PrimFn(p) => Term::PrimFn(p),
            Node::Let(n, e, b) => {
                // The body reads `n` as the closed bound term.
                let e = self.close(e, env, local.clone()).await?;
                let inner = Rc::new(local.update(n, Some(Rc::new(e))));
                self.close(b, env, inner).await?
            }
            Node::Lam(ps, b) => {
                let mut inner = (*local).clone();
                let mut names = Vec::with_capacity(ps.len());
                for i in 0..ps.len() {
                    let p = self.param(ps, i);
                    inner.insert(p, None);
                    names.push(self.name(p));
                }
                Term::Lam(
                    names,
                    Shared::new(self.close(b, env, Rc::new(inner)).await?),
                )
            }
            Node::App(f, args) => {
                let f = self.close(f, env, local.clone()).await?;
                Term::App(Shared::new(f), self.close_all(args, env, &local).await?)
            }
            Node::Prim(p, args) => Term::Prim(p, self.close_all(args, env, &local).await?),
            Node::If(g, a, b) => {
                let g = self.close(g, env, local.clone()).await?;
                let a = self.close(a, env, local.clone()).await?;
                let b = self.close(b, env, local).await?;
                Term::If(Shared::new(g), Shared::new(a), Shared::new(b))
            }
            Node::Follow(v, own, arms) => {
                let mut arms = arms.to_vec();
                arms.push((Pattern::Wild, self.close(own, env, local.clone()).await?));
                Term::Match(Shared::new(self.close(v, env, local).await?), arms)
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
                let dom = self.with(|tx| f.ints.snap(&tx.run.marks));
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
                _ => run_closed(&self.close_all_bound(t, env).await?),
            },
            _ => run_closed(&self.close_all_bound(t, env).await?),
        }
    }

    /// [`Walk::close`] with no name bound within the term.
    fn close_all_bound(&'m self, t: Tid, env: Eid) -> Deep<'m, Option<Term>> {
        self.close(t, env, Rc::new(Local::new()))
    }

    async fn constant_int(&'m self, t: Tid, env: Eid) -> Option<i64> {
        match self.constant(t, env).await? {
            Value::Int(n) => Some(n),
            _ => None,
        }
    }

    /// The constant exponent `t` of a `**`, when it is an integer at least 0, of any size: a
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
                Some((bt, be)) => self.fwd(bt, be).await,
                None => self.with(|tx| match tx.cx.inputs.get(tx.name(x)) {
                    Some(dom) => Fwd::int((**dom).clone()),
                    None => Fwd::top(),
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

    async fn fwd_prim(&'m self, t: Tid, p: Prim, args: Span, env: Eid) -> Fwd {
        use Prim::*;
        if p.arity().is_some_and(|n| n != args.len()) {
            return Fwd::top();
        }
        if p == Mul
            && let Some((base, be, k)) = self.with(|tx| tx.power(t, env))
        {
            let b = self.fwd(base, be).await;
            return arith(&Op::Pow(k), &b, &b, false);
        }
        match p {
            Neg | Abs => {
                let a = self.fwd(self.arg(args, 0), env).await;
                arith(&op(p, None).expect("scalar"), &a, &a, false)
            }
            Pow => match self.exponent(self.arg(args, 1), env).await {
                Some(k) => {
                    let a = self.fwd(self.arg(args, 0), env).await;
                    arith(&Op::Pow(k), &a, &a, false)
                }
                None => Fwd::top(),
            },
            Add | Sub | Mul | IntDiv | Mod | Min | Max => {
                let a = self.fwd(self.arg(args, 0), env).await;
                let b = self.fwd(self.arg(args, 1), env).await;
                let by_zero = matches!(p, IntDiv | Mod) && b.ints.contains(0);
                arith(&op(p, None).expect("scalar"), &a, &b, by_zero)
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
                None => self.with(|tx| tx.cx.inputs.get(tx.name(x)).map(|dom| dom.hull())),
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
                    match (tx.cx.inputs.get(x), &d) {
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
                let s = self.with(|tx| z.snap(&tx.run.marks));
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
                if tx.cx.inputs.get(k).is_some_and(|w| w != z) {
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
                let (s, exact) = mod_pre(z, c, &fa);
                let mut r = self.back(a, env, ints(s)).await;
                r.exact &= exact;
                r
            }
            (Min | Max, Some(c), _) => self.back(b, env, ints(minmax_pre(p, z, c))).await,
            (Min | Max, _, Some(c)) => self.back(a, env, ints(minmax_pre(p, z, c))).await,
            (Min | Max, None, None) => {
                let f = self.fwd(t, env).await.ints;
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
                    let ra = self.back(a, env, ints(r.clone())).await;
                    let rb = self.back(b, env, ints(r)).await;
                    return if both {
                        self.meet(ra, rb)
                    } else {
                        self.union(ra, rb)
                    };
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
            // `c ** 0` is 1 wherever `c` is an integer.
            return if z.contains(1) {
                self.back(c, env, Demand::Ints(IntervalSet::top())).await
            } else {
                Res::none()
            };
        }
        let fc = self.fwd(c, env).await.ints;
        let zc = revision::backward(o, 0, &fc, &fc, z);
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
    /// `**`, and branches), or two operands that both read inputs. Test:
    /// `l01_25_preimage_catalog::entries::a_strict_disjunction_with_a_failing_side_is_necessary_only`.
    /// COMPLEXITY.md row C16. A complete solution is `@exact` ([`exact_preimage`]), which
    /// searches the box at a cost in its points.
    async fn project(&'m self, p: Prim, a: Tid, b: Tid, env: Eid, z: &IntervalSet) -> Res {
        let o = op(p, None).expect("binary scalar operator");
        let fa = self.fwd(a, env).await.ints;
        let fb = self.fwd(b, env).await.ints;
        let za = revision::backward(&o, 0, &fa, &fb, z);
        let zb = revision::backward(&o, 1, &fa, &fb, z);
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
    /// and values lie in `i128` ([`finite`]), and an infinite end of a piece is the limit of
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
                Value::Int(c) => Some(Pa::Const(c)),
                _ => None,
            };
        }
        match self.node(t) {
            Node::Int(c) => Some(Pa::Const(c)),
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.pa(bt, be).await,
                None => self.with(|tx| {
                    let name = tx.name(x);
                    tx.cx.inputs.contains_key(name).then(|| Pa::Linear {
                        var: name.clone(),
                        a: 1,
                        b: 0,
                    })
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
            let dom = tx.cx.inputs.get(var)?;
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
        })
    }

    /// `-u`, `u + c`, `c + u`, `u - c`, `c - u` and `c * u` for a summarized `u` and a
    /// constant `c`, and `u + v` and `u - v` for two lines of one input ([`Pa::plus`]); the
    /// arity was checked by the caller.
    async fn pa_prim(&'m self, t: Tid, p: Prim, args: Span, env: Eid) -> Option<Pa> {
        let a = self.arg(args, 0);
        match p {
            Prim::Neg => self.pa(a, env).await?.affine(-1, 0),
            Prim::Add => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_int(a, env).await {
                    return self.pa(b, env).await?.affine(1, c.into());
                }
                if let Some(c) = self.constant_int(b, env).await {
                    return self.pa(a, env).await?.affine(1, c.into());
                }
                let pa = self.pa(a, env).await?;
                pa.plus(&self.pa(b, env).await?, 1)
            }
            Prim::Sub => {
                let b = self.arg(args, 1);
                if let Some(c) = self.constant_int(b, env).await {
                    return self.pa(a, env).await?.affine(1, -i128::from(c));
                }
                if let Some(c) = self.constant_int(a, env).await {
                    return self.pa(b, env).await?.affine(-1, c.into());
                }
                let pa = self.pa(a, env).await?;
                pa.plus(&self.pa(b, env).await?, -1)
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
                let pa = self.pa(u, env).await?;
                if c == 0 {
                    // `u` is summarized, so it has a value at every input, and the product is 0.
                    return Some(Pa::Const(0));
                }
                pa.affine(c.into(), 0)
            }
            Prim::Min | Prim::Max => {
                let b = self.arg(args, 1);
                let (c, u) = match self.constant_int(a, env).await {
                    Some(c) => (c, b),
                    None => (self.constant_int(b, env).await?, a),
                };
                let pa = self.pa(u, env).await?;
                let min = p == Prim::Min;
                match pa.var() {
                    None => pa.clamp(min, c, &IntervalSet::empty()),
                    Some(v) => self.with(|tx| pa.clamp(min, c, tx.cx.inputs.get(v)?)),
                }
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
            self.pa_select(t, env, &Pa::Const(1), &Pa::Const(0)).await?
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
                        a: 1,
                        b: 0,
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
                    let ca = self.by_class(a, env).await?;
                    let cb = self.by_class(b, env).await?;
                    ByClass::choose(&ca, &cb, &yes)
                }
                None => self.by_class_if(g, a, b, env).await,
            },
            _ => None,
        }
    }

    /// [`Walk::by_class`] of an `if` whose guard `g` is not on the split's remainder.
    async fn by_class_if(&'m self, g: Tid, a: Tid, b: Tid, env: Eid) -> Option<ByClass> {
        if self.reads_mod(g, env).await {
            return None;
        }
        let ca = self.by_class(a, env).await?;
        let cb = self.by_class(b, env).await?;
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
            &mut pairs,
        )?;
        let mut leaves = Vec::with_capacity(pairs.len());
        for (span, pa, pb) in pairs {
            leaves.push((span, self.pa_select(g, env, &pa, &pb).await?));
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
            Prim::Min | Prim::Max => {
                let b = self.arg(args, 1);
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
                            None => cu.clamp(min, c, &IntervalSet::empty()),
                            Some(v) => self.with(|tx| cu.clamp(min, c, tx.cx.inputs.get(v)?)),
                        }
                    }
                }
            }
            Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge | Prim::Eq | Prim::Ne => {
                let yes = self.residue_test(t, env).await?;
                ByClass::choose(&ByClass::constant(1, n)?, &ByClass::constant(0, n)?, &yes)
            }
            _ => None,
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
        let (x, m, _) = self.remainder_test(g, env).await?;
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
            let dom = tx.cx.inputs.get(&name).cloned();
            (name, dom)
        });
        let dom = dom?;
        let mut out = Res::none();
        for ((i, j), pa) in leaves {
            let r = self.with(|tx| tx.invert_pa(&pa, &z))?;
            let rems =
                IntervalSet::range(End::from(classes.cuts[i]), End::from(classes.cuts[j] - 1));
            let (members, exact) = mod_pre(&rems, c, &dom);
            if members.is_empty() {
                continue;
            }
            let mut within = Res::all();
            within.exact = exact;
            if members != *dom {
                within.dom.insert(name.clone(), Rc::new(members));
            }
            let met = self.meet(r, within);
            out = self.union(out, met);
        }
        Some(out)
    }

    /// The classes of the run's split in which the test `g` is true, as ranges of class
    /// numbers, when `g` compares the split's remainder `x mod c` with a constant in the way
    /// [`Walk::back_compare`] reads as a demand on the remainder, so that in each class the
    /// transfer finds the test true throughout or false throughout ([`Walk::back_arith`]).
    async fn residue_test(&'m self, g: Tid, env: Eid) -> Option<Vec<(usize, usize)>> {
        let (x, m, z) = self.remainder_test(g, env).await?;
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

    /// The input `x`, the modulus `m` and the set of remainders `z` of a test `g` that compares
    /// `x mod c` (`m = |c|`) with a constant in the way [`Walk::back_compare`] reads as a
    /// demand on the remainder: `g` holds where `x mod c` lies in `z`.
    async fn remainder_test(&'m self, g: Tid, env: Eid) -> Option<(Name, i128, IntervalSet)> {
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
        Some((x, c.unsigned_abs() as i128, z))
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
        Some(((body, lam), lins))
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

    async fn lin_at(&'m self, t: Tid, env: Eid) -> Option<Lin> {
        use Prim::*;
        if let Some(v) = self.constant(t, env).await {
            return match v {
                Value::Int(n) => Some(Lin::constant(n)),
                _ => None,
            };
        }
        match self.node(t) {
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.lin(bt, be).await,
                None => self.with(|tx| {
                    let x = tx.name(x);
                    (tx.cx.inputs.contains_key(x))
                        .then(|| Lin::atom(presburger::Atom::Sym(x.clone())))
                }),
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                self.lin(b, inner).await
            }
            Node::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam) if ps.len() == args.len() => {
                    match self.call_key(body, lam, args, env).await {
                        Some(k) => {
                            let call = self.translated(
                                |m| &mut m.lin_calls,
                                k,
                                Logged::LinCall,
                                move || self.lin_call(t, ps, (body, lam), args, env),
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
                    Add => Some(arg(0).await?.plus(&arg(1).await?)),
                    Sub => Some(arg(0).await?.minus(&arg(1).await?)),
                    Neg => Some(arg(0).await?.times(-1)),
                    Mul => {
                        let (a, b) = (arg(0).await?, arg(1).await?);
                        if !products && !a.terms.is_empty() && !b.terms.is_empty() {
                            return None;
                        }
                        a.product(&b)
                    }
                    Pow => match self.constant_int(self.arg(args, 1), env).await? {
                        0 => Some(Lin::constant(1)),
                        1 => arg(0).await,
                        2 if products => {
                            let a = arg(0).await?;
                            a.product(&a)
                        }
                        _ => None,
                    },
                    IntDiv | Mod => {
                        let c = self.constant_int(self.arg(args, 1), env).await;
                        if c.is_none() && products {
                            // A divisor that is not a constant: its product with the quotient
                            // is an atom, which only rung 2's translation admits.
                            let a = arg(0).await?;
                            let n = arg(1).await?;
                            return self.tr(|tr| tr.div_mod_by_term(p, &a, &n));
                        }
                        let c = c.filter(|c| *c != 0)?;
                        let a = arg(0).await?;
                        self.tr(|tr| {
                            // One pair for each dividend and divisor, so that every `x mod m`
                            // and `x div m` of one input names the same quotient and remainder.
                            let key = (a.clone(), Lin::constant(c));
                            let pick = |n: u32| {
                                Lin::atom(presburger::Atom::Aux(if p == IntDiv {
                                    n
                                } else {
                                    n + 1
                                }))
                            };
                            if let Some(&n) = tr.pairs.get(&key) {
                                return Some(pick(n));
                            }
                            // `a == c·q + r` and `0 <= r < |c|`: Euclidean.
                            let n = tr.defs.len() as u32;
                            tr.pairs.insert(key.clone(), n);
                            tr.made.push(key);
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
                            let shown = |op| What::ByConstant(op, a.clone(), c);
                            tr.defs.push((n, shown("div"), def));
                            tr.defs.push((n + 1, shown("mod"), Formula::top()));
                            Some(if p == IntDiv { q } else { r })
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
                    match self.call_key(body, lam, args, env).await {
                        Some(k) => {
                            let call = self.translated(
                                |m| &mut m.formula_calls,
                                k,
                                Logged::FormulaCall,
                                move || self.formula_call(t, ps, (body, lam), args, env),
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
            Node::If(g, a, b) => {
                // The formula of a name is kept whole, as for `&&` below.
                let named = [g, a, b].map(|t| self.whole(t, env));
                let g = self.formula(g, env).await?;
                let (fa, fb) = (self.formula(a, env).await?, self.formula(b, env).await?);
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
                        let b = b.expect("two operands");
                        #[cfg(test)]
                        if presburger::TWO_AT_A_TIME.get() {
                            return self.two_at_a_time(p, a, b, env).await;
                        }
                        self.chain(p, [a, b], env).await
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
                        Some(if p == Ne { Formula::negate(same) } else { same })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The formula of a `&&` (`p` is `And`) or a `||` with the given operands: the operands
    /// of the chain of `p` it heads, each operand that is itself a `p` with no constant value
    /// read through, joined as [`Formula::and_keeping`] or [`Formula::or_keeping`] would join
    /// them two at a time, but in one [`Joining`], so a chain of k operands costs O(k log k)
    /// and not O(k²) (ST-formula-k2). The formula of a name is kept whole, so a named part
    /// used at many places is one node and not copied into each (COMPLEXITY.md S31b). The
    /// operands are read in order, as the two-at-a-time translation reads them, and the
    /// first that has no formula gives none for the whole. An operand of a primitive is held
    /// in its parent alone ([`Terms::ids`]), so the chain is a tree, and each of its nodes is
    /// met once without a visited set.
    async fn chain(&'m self, p: Prim, operands: [Tid; 2], env: Eid) -> Option<Formula> {
        /// An operand to read, or the end of an inner `p`, with where the joining was before
        /// its operands ([`Joining::close`]).
        enum Step {
            Operand(Tid),
            Close(Mark),
        }
        let mut j = Joining::new(p == Prim::And);
        let mut todo = vec![Step::Operand(operands[1]), Step::Operand(operands[0])];
        while let Some(step) = todo.pop() {
            let u = match step {
                Step::Close(mark) => {
                    j.close(mark);
                    continue;
                }
                Step::Operand(u) => u,
            };
            let node = self.node(u);
            if let Node::Prim(q, args) = node
                && q == p
                && q.arity().is_none_or(|n| n == args.len())
                && self.constant(u, env).await.is_none()
            {
                todo.push(Step::Close(j.mark()));
                todo.push(Step::Operand(self.arg(args, 1)));
                todo.push(Step::Operand(self.arg(args, 0)));
                continue;
            }
            let f = self.formula(u, env).await?;
            j.operand(f, self.whole(u, env));
        }
        Some(j.finish())
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

/// An integer operator over its operands' forward values.
fn arith(o: &Op, a: &Fwd, b: &Fwd, by_zero: bool) -> Fwd {
    Fwd {
        ints: revision::forward(o, &a.ints, &b.ints),
        fails: !a.is_int() || !b.is_int() || by_zero,
        ..Fwd::none()
    }
}

/// An integer term as a function of one input `var` (R1_GEMINI Thm 3.1: the value of a term
/// built from one input by `if`s on that input, constants, negation, adding a constant and
/// multiplying by one, and adding two such terms each affine over the whole domain, is affine
/// on each of finitely many intervals of the input, cut at the domain's and the guards'
/// ends). The coefficients, constants and values lie in `i128`, every step checked there, so
/// an affine step ([`Pa::affine`], [`apply_tag`]) is given up only when one leaves `i128`.
/// Kernel integers are unbounded, so a value outside `i64` is a value of the term, and the
/// summary reads it as one: `i64::MIN - (u + 3)` is summarized, although its constant
/// `i64::MIN - 3` lies outside `i64`, and so is `u + 1` at `u = i64::MAX`. At an infinite end
/// of the domain a piece takes the infinity its line tends to ([`value_at`]), never the value
/// at an end of `i64`.
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

    /// `self + sign * other` when both are lines of one input, `a * var + b` over its whole
    /// domain (`n + n`, `n - 2 * n`), `O(1)`; `None` when a coefficient or a constant leaves
    /// `i128`, and for any other pair: a constant operand is read by the caller
    /// ([`Pa::affine`]), and two summaries of different inputs read two inputs.
    ///
    /// Complexity tradeoff: a sum with a [`Pa::Piecewise`] operand gets no summary, so its
    /// backward transfer is the inexact projection and the scope widens: `d` nested tests
    /// `if (…) == 1 { n } else { n + (if n > 0 { n } else { 0 }) }` hold at `n = 1` alone, and
    /// from depth 4 their true arm reads `n` as every integer, as before sums of lines were
    /// summarized; the cost stays `O(d)` (8 to 64 levels: 10 ms to 59 ms). What is given up:
    /// the exact preimage of such a sum. Why: adding two treaps piece by piece costs the
    /// pieces of both, and a chain whose sum at each level reads the `if` below could cost
    /// `O(d^2)`; lines are the sums the nested chains of COMPLEXITY.md row F70 read.
    /// Trigger: an `if` among the operands of a sum of two non-constant terms of one input.
    /// Test: `l01_39_reduced_product::follow::nested_sums_keep_their_arms`. A complete
    /// solution would add a line to every piece by a lazy tag on the treap (a tag
    /// `(mul, add, slope)`), `O(log p)` for `p` pieces, and add two treaps by merging their
    /// cuts, `O(p + q)`.
    fn plus(&self, other: &Pa, sign: i128) -> Option<Pa> {
        match (self, other) {
            (Pa::Linear { var, a, b }, Pa::Linear { var: w, a: c, b: e }) if var == w => {
                Some(Pa::Linear {
                    var: var.clone(),
                    a: a.checked_add(c.checked_mul(sign)?)?,
                    b: b.checked_add(e.checked_mul(sign)?)?,
                })
            }
            _ => None,
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

    /// `min(self, c)`, or `max(self, c)` where not `min`, over `dom`, the domain of the input
    /// ([`clamp_treap`]).
    fn clamp(&self, min: bool, c: i64, dom: &IntervalSet) -> Option<Pa> {
        let var = match self {
            Pa::Const(v) => return Some(Pa::Const(if min { *v.min(&c) } else { *v.max(&c) })),
            Pa::Linear { var, .. } | Pa::Piecewise { var, .. } => var.clone(),
        };
        let root = clamp_treap(&self.to_treap(dom)?, min, c.into())?;
        Some(Pa::Piecewise { var, root })
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

    /// `min(self, c)`, or `max` where not `min`, in every class ([`Pa::clamp`]), each leaf
    /// clamped once for the classes it covers: `O(L (m + 1) log P)` for `L` leaves, at most
    /// the `G` classes, and `m` crossings of `c` among `P` pieces.
    ///
    /// Complexity tradeoff: each leaf is clamped by itself, not the tree's base once, so the
    /// classes share no step here, `O(L)` clamps for a tree of `L` leaves, at most `G`. Why: a
    /// leaf is the base under its own affine map, and a clamp does not commute with a map
    /// that is not the identity, so the leaves' clamps differ. Trigger: `min` or `max` with a
    /// constant of a term whose values lie on both sides of it, below an `if` on the split's
    /// remainder. Test: `store::preimage::tests::a_chain_with_clamps_is_read_in_time_near_its_length`.
    /// COMPLEXITY.md rows S22e-quad and S22-order-chain. A complete solution is the one named
    /// at [`Walk::by_class`]: the congruence facet in the transfer's sets.
    fn clamp(&self, min: bool, c: i64, dom: &IntervalSet) -> Option<ByClass> {
        let root = cls_clamp(&self.root, (1, self.shift), self.base.as_ref(), min, c, dom)?;
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
                Cls::Same(Leaf::Own(pa)) => out.push(((lo, hi), pa.affine(f.0, f.1)?)),
                Cls::Same(Leaf::Base(g)) => {
                    let f = compose(*g, f)?;
                    out.push(((lo, hi), self.base.as_ref()?.affine(f.0, f.1)?));
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
            Leaf::Own(pa) => pa.affine(f.0, f.1),
            Leaf::Base(g) => {
                let f = compose(*g, f)?;
                self.base.as_ref()?.affine(f.0, f.1)
            }
        }
    }
}

/// The summary a leaf holds, `base` standing for [`Leaf::Base`].
fn leaf_pa(leaf: &Leaf, base: Option<&Pa>) -> Option<Pa> {
    match leaf {
        Leaf::Own(pa) => Some(pa.clone()),
        Leaf::Base((mul, add)) => base?.affine(*mul, *add),
    }
}

/// Appends to `out`, in the order of the classes, each range of classes `span` in which both
/// `a` and `b`, trees over `span` with no map above them, are one summary, with those two
/// summaries; `bases` are the summaries of their [`Leaf::Base`] leaves. A range is a node of
/// either tree, so there are at most as many as the two trees have leaves together.
fn cls_zip(
    a: &Rc<Cls>,
    b: &Rc<Cls>,
    bases: (Option<&Pa>, Option<&Pa>),
    (lo, hi): (usize, usize),
    out: &mut Vec<((usize, usize), Pa, Pa)>,
) -> Option<()> {
    if let (Cls::Same(u), Cls::Same(v)) = (&**a, &**b) {
        out.push(((lo, hi), leaf_pa(u, bases.0)?, leaf_pa(v, bases.1)?));
        return Some(());
    }
    let mid = lo + (hi - lo) / 2;
    let (al, ar) = cls_halves(a)?;
    let (bl, br) = cls_halves(b)?;
    cls_zip(&al, &bl, bases, (lo, mid), out)?;
    cls_zip(&ar, &br, bases, (mid, hi), out)
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

/// The tree `node` with the map `f` applied above it and every leaf's summary clamped
/// ([`ByClass::clamp`]); `base` is the summary of the leaves [`Leaf::Base`].
fn cls_clamp(
    node: &Rc<Cls>,
    f: (i128, i128),
    base: Option<&Pa>,
    min: bool,
    c: i64,
    dom: &IntervalSet,
) -> Option<Rc<Cls>> {
    Some(Rc::new(match &**node {
        Cls::Same(leaf) => {
            let pa = match leaf {
                Leaf::Own(pa) => pa.affine(f.0, f.1)?,
                Leaf::Base(g) => {
                    let g = compose(*g, f)?;
                    base?.affine(g.0, g.1)?
                }
            };
            Cls::Same(Leaf::Own(pa.clamp(min, c, dom)?))
        }
        Cls::Split { left, right, tag } => {
            let f = compose(*tag, f)?;
            Cls::Split {
                left: cls_clamp(left, f, base, min, c, dom)?,
                right: cls_clamp(right, f, base, min, c, dom)?,
                tag: (1, 0),
            }
        }
    }))
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

/// `(lo, hi)` mapped by `x -> mul * x + add`, in order: an infinity stays one of the same sign
/// when `mul > 0` and becomes the other when `mul < 0`, and every value, an infinity too,
/// becomes `add` when `mul` is 0 (the limit of a line of slope 0 is its constant, as at
/// [`value_at`]); `None` when a finite value leaves `i128`.
fn map_vals((lo, hi): (i128, i128), (mul, add): (i128, i128)) -> Option<(i128, i128)> {
    if mul == 0 {
        let v = finite(add)?;
        return Some((v, v));
    }
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

/// The pieces of `node`'s subtree with each value `v` made `min(v, c)` where `min`, and
/// `max(v, c)` otherwise. A subtree whose values all lie on the kept side of `c` is kept, and
/// one whose values all lie on the other side is mapped to `c` by a tag ([`map_vals`] with
/// multiplier 0), so only the nodes whose subtree's values lie on both sides of `c` are
/// visited: those on the paths to the `m` pieces whose line crosses `c`, `O((m + 1) log n)`
/// nodes, each joined in `O(log n)`.
fn clamp_treap(node: &Tree, min: bool, c: i128) -> Option<Tree> {
    let Some(n) = node else {
        return Some(None);
    };
    let (lo, hi) = n.vals;
    let (kept, at_c) = if min {
        (hi <= c, lo >= c)
    } else {
        (lo >= c, hi <= c)
    };
    if kept {
        return Some(Some(n.clone()));
    }
    if at_c {
        return apply_tag(n, (0, c)).map(Some);
    }
    let (left, right) = push_down(n)?;
    let mut out = clamp_treap(&left, min, c)?;
    // The inputs of the node's own piece whose value lies on the kept side of `c`: one stretch
    // at an end of the piece, or none, since the line is monotone; the rest take `c`.
    let side = if min {
        IntervalSet::range(NegInf, End::from(c))
    } else {
        IntervalSet::range(End::from(c), PosInf)
    };
    let mut own = Vec::with_capacity(1);
    invert_piece(&n.lo, &n.hi, n.a, n.b, &side, &mut own)?;
    let mut pieces = Vec::with_capacity(3);
    match own.first() {
        None => pieces.push((n.lo.clone(), n.hi.clone(), 0, c)),
        Some((xl, xh)) => {
            if *xl > n.lo {
                pieces.push((n.lo.clone(), xl.pred(), 0, c));
            }
            pieces.push((xl.clone(), xh.clone(), n.a, n.b));
            if *xh < n.hi {
                pieces.push((xh.succ(), n.hi.clone(), 0, c));
            }
        }
    }
    for (plo, phi, a, b) in pieces {
        out = join_treap(out, Some(make_node(plo, phi, a, b, None, None)?))?;
    }
    join_treap(out, clamp_treap(&right, min, c)?)
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

/// The names bound within a term being closed ([`Walk::close`]).
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
        EXACT.with(|c| c.set(c.get() + 1));
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
    use super::presburger::TWO_AT_A_TIME;
    use super::*;
    use std::cell::Cell;
    use std::collections::BTreeSet;

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
    /// A map that leaves `i128` is shown as such.
    fn pa_shown(p: &Pa) -> String {
        let (var, pieces) = match p {
            Pa::Const(c) => (None, vec![(NegInf, PosInf, 0, i128::from(*c))]),
            Pa::Linear { var, a, b } => (Some(var), vec![(NegInf, PosInf, *a, *b)]),
            Pa::Piecewise { var, root } => {
                let Some(pieces) = treap_pieces(root) else {
                    return format!("{var}: a map past i128");
                };
                (Some(var), pieces)
            }
        };
        let mut joined: Vec<(End, End, i128, i128)> = Vec::with_capacity(pieces.len());
        for (lo, hi, a, b) in pieces {
            match joined.last_mut() {
                Some(last) if (last.2, last.3) == (a, b) && last.1.succ() == lo => last.1 = hi,
                _ => joined.push((lo, hi, a, b)),
            }
        }
        // A function constant over every input reads none.
        let var = match joined.as_slice() {
            [(NegInf, PosInf, 0, _)] => None,
            _ => var,
        };
        let shown: Vec<String> = (joined.iter())
            .map(|(lo, hi, a, b)| format!("{lo}..={hi}: {a} x + {b}"))
            .collect();
        format!("{}: {}", var.map_or("no input", |v| &**v), shown.join(", "))
    }

    /// The pieces of a treap in order, each `(lo, hi, a, b)` with the maps above it applied,
    /// or `None` when a map leaves `i128`. The stack is explicit, so a deep treap does not
    /// overflow the thread's.
    fn treap_pieces(root: &Tree) -> Option<Vec<(End, End, i128, i128)>> {
        let mut out = Vec::new();
        let mut stack: Vec<(&PaNode, (i128, i128), bool)> = Vec::new();
        if let Some(n) = root {
            stack.push((n, (1, 0), false));
        }
        while let Some((n, f, left_done)) = stack.pop() {
            let below = compose(n.tag, f)?;
            if !left_done {
                stack.push((n, f, true));
                if let Some(l) = &n.left {
                    stack.push((l, below, false));
                }
                continue;
            }
            let (a, b) = compose((n.a, n.b), f)?;
            out.push((n.lo.clone(), n.hi.clone(), a, b));
            if let Some(r) = &n.right {
                stack.push((r, below, false));
            }
        }
        Some(out)
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
            }
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
                    Term::Prim(p, vec![self.test(d), self.test(d)])
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
                let inner = Term::Prim(p, vec![self.cmp(1), self.cmp(1)]);
                let rhs = Term::Prim(p, vec![self.cmp(1), inner]);
                let x = self.name();
                self.bound.push((x.clone(), Kind::Test));
                lets.push((x, Shared::new(rhs)));
            }
            let p = if self.rng.below(2) == 0 {
                Prim::And
            } else {
                Prim::Or
            };
            let mut t = Term::Prim(p, vec![self.test(3), self.test(3)]);
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
        /// The `&&` and `||` primitive nodes.
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
        tx.start(&domains(), Landmarks::none());
        let mut tr = Tr::new(false);
        let f = tx.formula(&mut tr, root, ROOT);
        TWO_AT_A_TIME.set(false);
        let chains: BTreeSet<Tid> = (0..tx.terms.nodes.len() as Tid)
            .filter(|&u| matches!(tx.node(u), Node::Prim(Prim::And | Prim::Or, _)))
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
        let mut g = Gen::new(0x9e37_79b9_7f4a_7c15, false);
        let (mut some, mut none, mut kept, mut stopped, mut fewer) = (0, 0, 0, 0, 0);
        let only = part * 4000 / PARTS..(part + 1) * 4000 / PARTS;
        for round in 0..only.end {
            g.pool.clear();
            let t = match g.rng.below(4) {
                0 => g.itself(4),
                1 => g.named(),
                _ => {
                    let p = if g.rng.below(2) == 0 {
                        Prim::And
                    } else {
                        Prim::Or
                    };
                    Term::Prim(p, vec![g.test(4), g.test(4)])
                }
            };
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

    /// A chain of guards on `x mod 2` over `[-6, 6]`, which the first split finds wide
    /// ([`Split::Wide`]) and the split over the box it found reads exactly ([`preimage_in`]).
    #[test]
    fn a_chain_split_by_two_classes_is_read_in_time_near_its_length() {
        crate::scaling::check_order("the preimage of a chain of k ifs, x mod 2", 10, 1, |k| {
            chain_preimage(2, k)
        });
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
                let node = make_node(End::of(lo), End::of(hi), a, b, None, None).unwrap();
                root = join_treap(root, Some(node)).unwrap();
                lo = hi + 1 + rng.below(3) as i64;
            }
            let c = rng.below(31) as i128 - 15;
            let min = rng.below(2) == 0;
            let clamped = clamp_treap(&root, min, c).unwrap();
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
                    r.vals.0 <= vlo && vhi <= r.vals.1,
                    "round {round}: {:?}",
                    r.vals
                );
            }
        }
    }

    /// The value of the summary `t` at `x`, or `None` where it has no piece. A node's own
    /// piece has its maps applied; its children get its tag ([`push_down`]).
    fn point(t: &Tree, x: i64) -> Option<i128> {
        let n = t.as_ref()?;
        let (left, right) = push_down(n).unwrap();
        if End::of(x) < n.lo {
            return point(&left, x);
        }
        if End::of(x) > n.hi {
            return point(&right, x);
        }
        Some(n.a * i128::from(x) + n.b)
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
