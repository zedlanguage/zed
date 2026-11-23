//! The backward transfer as it was before the piecewise-affine summary and the demand clip of
//! S22a (main at fdf7918, which holds the 397f1c9 transfer and later changes), retained as an
//! independent catalog, with the exact interval ends of TD-ends, the failure of a base raised to 0
//! (SOUND-div-exact), and a box of `c - x` no longer marked exact when the forward image of
//! `{c} - z` merged pieces (S22-exact-mislabel) unless an enclosing guard removes every input
//! that takes a value in the merged pieces (S22-guard-exact), so that tests can compare the
//! whole `Preimage` of [`super::preimage`] with it. Nothing outside the tests uses it.
//!
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
//! with more than one member; `preimage_listed`), of a term whose form shows that it ends,
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
//!
//! ## Cost of the transfer (PERF-ref-memo-quadratic, `COMPLEXITY.md` row C56)
//!
//! Naive method, main before this item: `Tx::back_doubt` memoizes each (term, demand,
//! doubted values) triple. On a guarded chain `t_j = if (i <= j mod 7 - 3) { t } else { c - t }`
//! each level reflects the demand by a different `c`, so the demands that reach a shared node
//! differ at every level: the memo holds 8,852 keys at 64 links and 350,726 at 512, O(n^2) time
//! and space (148 ms against 13,275 ms on `jmod5_wide`).
//!
//! Used: a term that reads one input is solved once over its reachable DAG (visited set, one
//! pass in topological order), in a 1D state (`State1d`): the input's values partitioned into
//! intervals by the value each takes at the current node, kept in a persistent value-ordered AVL
//! tree with path copying (Adelson-Velsky and Landis, Dokl. Akad. Nauk SSSR 146(2), 1962,
//! pp. 263-266, read 2026-11-21: Lemma 1, height at most `(3/2) log2(N + 1)`; insertion
//! only; the full comment is at `Staircase` in `product.rs`; persistence by path copying as in
//! Driscoll, Sarnak, Sleator and Tarjan, "Making data structures persistent", JCSS 38, 1989,
//! doi:10.1016/0022-0000(89)90034-2, cited in this crate's `lib.rs`, References), so
//! that a branch shares the unchanged subtrees of both arms. A shift or a negation relabels the
//! tree through a lazy tag on its nodes, and a positive quotient (`a = q*c + r`,
//! `tree_division`) maps it in one O(p) pass over its p pieces; a remainder met while the state
//! is already periodic in an incompatible modulus lists the excluded residues in each period that
//! meets the remainder's image (`State1d::modulo_bounded`), at most `m/old + 1` pieces per
//! excluded piece, bounded by moduli written in the program and not by the input range or the
//! chain length. A chain of guards over affine links is solved by an endpoint sweep that keeps
//! the composed affine map in a segment tree of affine maps (the composition of affine maps is
//! associative; Bentley and Wood 1980, doi:10.1109/TC.1980.1675628, sec. IV, p. 574, quoted
//! in this crate's `lib.rs`, References), one O(log n)
//! update per guard endpoint (`Tx::affine_guards`). Terms that read two or more inputs, and step
//! shapes the 1D state does not cover, keep main's memo. The transfer itself follows no paper;
//! the papers are those of the data structures.
//!
//! Earlier methods and why this one. Run 1 (gemini-4-carbon-high): a memo keyed by an input box,
//! with chains of unit steps skipped by composed maps; one chain written with applied lambdas
//! took 231G instructions at 256 links, and `pathological_abs` grew as n^1.66. Run 2
//! (gemini-4-carbon-medium, branch head 8667f519): one-input state trees with exact one-input
//! doubt; near linear on the item's 25 families, but n^3.28 on an `abs` chain with wide gaps,
//! n^2.13 on a `min` chain, and a fallback to main's memo on nested remainders. Run 3
//! (gpt-6.1-sol, 5b0f1eeb): one balanced tree with two orderings and exact inverse intervals;
//! near linear on 40 families, but three answers coarser than main's (calls 22, 45 and 86 of
//! main's answer dump: a product with no exact inverse passed every value but the excluded ones,
//! not the values the product can take), and 114,800M instructions at 128 links of
//! `normal_incompatible_moduli`. This method (cross-review rounds 1 to 3, Sol's round 3 with
//! Opus's sorted listing for remainders) keeps run 3's tree with one ordering only, bounds the
//! product and quotient demands by their forward image (calls 22, 45 and 86 now give main's
//! answer), settles nested remainders at the input by the bounded listing, and replaces the
//! input-ordered tree by the affine sweep.
//!
//! Cost in theory: O(n log n + output) time and O(n + output) space over a chain of n links,
//! with output the pieces of the answer; a nested remainder adds a factor `m/old` per excluded
//! piece, linear in a modulus literal (so exponential in its bits). Not proved in general: the
//! O(log n) cost per link is proved for `normal_round_down` and `normal_min_gap` only (the
//! proofs at `Tx::inverse_states`); for the other families the bound is measured, and
//! `Tx::back_doubt` lists, each with its measured family (PROOF-preimage-ref-chain-cost), the
//! shapes that keep main's memo and the products and quotients that visit every piece of the
//! state. Terms that read two or more inputs grow faster than n on that memo (row
//! PERF-ref-memo-multi-input). Nested remainders do not
//! meet that bound: the state the listing keeps holds every residue of the larger modulus,
//! with labels that gain input pieces at each link whatever the answer, so the pass costs at
//! least the size of that state. Measured on
//! `nested_moduli_eq_4096` with the constants of n = 6 mod 10 next to the root (an answer of
//! about 760 pieces at every n): 21.4 times the instructions from 16 to 128 links and 11.5
//! times from 64 to 512 while each guard rewrote that state; with the guards' input
//! restrictions waiting (`Parts1d`, REF-nested-moduli-state) 12.07 and 8.12, against
//! state growth (label pieces reaching the chain's input) of 12.1 and 8.84. Measured
//! T(8n)/T(n), the
//! larger of the instruction and byte ratios, over the 48 families of the scaling tests
//! (`l01_25_preimage_catalog::ref_memo`, load about 37 on 32 cores): at most 10.6
//! (`normal_abs_gap` at 16 links, the log term of the path copies of the persistent inverse
//! tree; timed at 1024 links its test measures 9.67, row REF-normal-abs-gap), 9.0 to
//! 10.4 on six more (`normal_min_gap`, `normal_round_down`,
//! `pathological_abs`, `normal_holey_guards`, `normal_mod_chain`, `normal_div_chain`), under 9 on
//! the rest; `output_grid` (four values demanded, 4n pieces) 8.0 from 64 to 512 links, and with
//! 64 and 512 values demanded at 1024 links (8 times the pieces) 5.0 times the instructions and
//! 5.7 times the bytes; `nested_moduli_eq_4096` 4.7 from 160 to 1280 links, multiples of 10 so
//! that both put the same constants next to the root. Main exceeds 13 on 24 of the 38 families it
//! finishes within 60 s (17.8 to 2,965), and 10 do not finish within 60 s. Main's answer dump
//! (182,747 calls): 182,327 the same, 420 finer, none coarser or unsound. Size against main:
//! 2,547 lines added and 117 removed, this section included.
//!
//! [`super::preimage`]: crate::preimage
//! [`exact_preimage`]: crate::preimage_ref::exact_preimage
//! [`witness`]: crate::preimage_ref::witness

use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Arc;

use zed_collections::index::to_u32;
use zed_kernel::{Prim, Shared, Term, Value, eval};

use End::{Fin, NegInf, PosInf};
use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::landmarks::Landmarks;
use zedc_lattice::revision::{self, Op, Tonicity, reduce_congruence};
use zedc_presburger::presburger::{self, Con, Formula, Lin, Refusal, Relation};
use zedc_stage::stage;

mod mod_chain;

use mod_chain::{
    MOST_CLASSES, ModLink, Pieces, ResidueMap, any_in, contains, estimate, gaps, hits, meet,
    normal, periodic, pieces_of, residues, set_of,
};

// The search helpers and the types they read are those of the solver (DRY-preimage-ref-oracle):
// this file is an independent oracle for the backward transfer, which stays a copy, and the
// box search around it (the classes, halving, running a point) is not what it checks.
pub use crate::preimage::{Classes, Demand, Domains, Listed, Point};
use crate::preimage::{
    NONE_LISTED, Search, Whole, classes_decide, enumerate, halve, is_point, run_point,
    within_classes,
};

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
    /// Naive version: the transfer read through the loop, once per iteration, which need not end;
    /// used: the stop, O(1) at the loop, with the whole box as the answer (necessary only).
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
// Proof (proofs audit, proofdoc4b). `eval` runs only after `stage::ends(t)` holds, so the
// claim rests on `ends` being sound (a `true` only for a term every run of which ends): that
// is zedc-stage's claim and its proof is at `stage::ends`, not here. A run that fails (a
// division by zero, a refused primitive) gives `None`, so the caller treats the term as not
// known, never as a wrong value. "Ends" bounds no time: a term shown to end may still run
// long (a finite loop over a large range); nothing here limits that. Callers: the two
// closed-term reads in `Tx` (`s.close(t, env, ..)` then `run_closed`).
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
/// lists, each holding no member the source does not list: a box over them may be
/// enumerated (`enumerate`).
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
    let mut tx = Tx::new();
    let root = tx.terms.add(term);
    preimage_in(&mut tx, root, term, inputs, listed, demand)
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
    // A two-input threshold chain is answered exactly by [`Tx::affine_threshold_pair`] in
    // O(n log n), before the landmarks, the forward images and the memo (`Tx::back_doubt`),
    // which visit its cell pairs in O(n^2). Listed inputs need no other path: `enumerate` takes
    // only a box with at most one input of several members, where the product of the
    // projections is the set of passing points, so the stage, exact by Theorem 1 at
    // `threshold_box`, answers it exactly with no relation (test
    // `ref_memo::listed_threshold_chains_are_answered_exactly`). A chain of guards on distinct
    // inputs is answered by [`Tx::independent_affine`] in O(n), where the memo visits its
    // combinations of arms; on such a box, every link but one has one arm, so Check 2 there
    // sees single values and decides exactness (test
    // `ref_memo::listed_independent_chains_are_answered_exactly`). A two-input chain of modular
    // links (`alternating_moduli`) is answered by [`Tx::mod_chain_pair`] in O(K n (log n + k)),
    // `K` its classes, with no table sized by a modulus. It runs before `independent_affine`,
    // which also takes a chain of one guard on `m` over a mod arm of `i` but keeps the whole
    // box there, where this stage gives the exact projections (test
    // `ref_memo::mod_chains_agree_with_the_interpreter`); its recognizer stops at the first arm
    // that is not modular, O(1) on the independent families. Its answer is taken for a listed
    // input only when exact, since `enumerate` needs every listed input and main's path tries
    // it when the box is not exact. `None` from all three is main's path.
    tx.start(inputs, Landmarks::none());
    let early = match tx.affine_threshold_pair(root, demand) {
        Some(found) => Some(found),
        None => tx
            .mod_chain_pair(root, demand)
            .filter(|(a, _)| a.exact || listed.is_empty())
            .or_else(|| tx.independent_affine(root, demand)),
    };
    if let Some((answer, relation)) = early {
        return Preimage {
            domains: tx.whole(&answer),
            exact: answer.exact,
            enumerated: false,
            stops: Vec::new(),
            relation,
            refusal: None,
        };
    }
    let marks = tx.landmarks(inputs, demand);
    tx.start(inputs, marks.clone());
    // Total forward containment already proves the whole box. This avoids building
    // inverse constraints for an answer known before any backward traversal.
    let periodic = if tx.fwd(root, ROOT).meets(demand) {
        Some((Res::all(), None))
    } else {
        tx.affine_guards(root, demand)
            .or_else(|| tx.periodic(root, demand))
            .or_else(|| tx.independent_reflections(root, demand))
            .or_else(|| tx.correlated(root, demand))
    };
    let back = match &periodic {
        Some((back, _)) => back.clone(),
        None => tx.back(root, ROOT, demand),
    };
    let mut r = Whole {
        dom: tx.whole(&back),
        exact: back.exact,
    };
    let doubt = back.doubt;
    let mut stops = std::mem::take(&mut tx.run.stops);
    let mut enumerated = false;
    if !r.exact && !is_empty(&r.dom) && periodic.is_none() {
        tx.start(&r.dom, marks);
        if tx.fwd(root, ROOT).meets(demand) {
            r.exact = true;
        }
    }
    let (mut relation, mut refusal) = (periodic.and_then(|(_, rel)| rel), None);
    if r.exact {
        relation = None;
    }
    if !r.exact
        && relation.is_none()
        && !is_empty(&r.dom)
        && let Some((rel, found)) = linear(tx, root, &r.dom, demand, doubt.as_ref())
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
        && let Some(e) = enumerate(term, &r.dom, listed, demand)
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
        tx.clear_translations();
        let first = tr.defs.len();
        let body = tx.formula(&mut tr, root, ROOT)?;
        out.push(Relation {
            body,
            defs: tr.defs[first..].to_vec(),
            bit_ands: Vec::new(),
        });
    }
    Some(out)
}

/// One link of a two-input threshold chain: the guard `axis <= cut` on input `axis` (0 the
/// base, 1 the other input) picks `low`, else `high`, each a map of the link's inner value.
struct ThresholdLink {
    axis: usize,
    cut: i128,
    low: ValTag,
    high: ValTag,
}

/// The values `lo..=hi` of one input, all of which fire the same links of their axis: those
/// before chain position `end` (see [`threshold_cells`]).
#[derive(Clone)]
struct ThresholdCell {
    end: usize,
    lo: End,
    hi: End,
}

/// The cells of input `axis` within `domain`, in increasing `end`. By Lemma 1 of
/// [`threshold_box`] a value fires a prefix of its axis's links; `end` is one past the chain
/// position of the last link it fires, or 0 when it fires none. Equal cuts give an empty cell,
/// and cells are clipped to the domain, so no cell holds a value the domain does not.
fn threshold_cells(
    links: &[ThresholdLink],
    axis: usize,
    domain: &(End, End),
    increasing: bool,
) -> Vec<ThresholdCell> {
    let mut cells = Vec::new();
    let mut edge = if increasing { NegInf } else { PosInf };
    let mut end = 0;
    let mut add = |end, lo: End, hi: End| {
        let lo = lo.max(domain.0.clone());
        let hi = hi.min(domain.1.clone());
        if lo <= hi {
            cells.push(ThresholdCell { end, lo, hi });
        }
    };
    for (j, link) in links
        .iter()
        .enumerate()
        .filter(|(_, link)| link.axis == axis)
    {
        let cut = End::from(link.cut);
        edge = if increasing {
            add(end, edge, cut.clone());
            cut.succ()
        } else {
            add(end, cut.succ(), edge);
            cut
        };
        end = j + 1;
    }
    if increasing {
        add(end, edge, PosInf);
    } else {
        add(end, NegInf, edge);
    }
    cells
}

/// Widens `out` to hold `lo..=hi`.
fn threshold_extrema(out: &mut Option<(End, End)>, lo: End, hi: End) {
    *out = Some(match out.take() {
        Some((a, b)) => (a.min(lo), b.max(hi)),
        None => (lo, hi),
    });
}

/// Whether every value `range` was widened by equals `v` (true when there was none).
fn threshold_uniform(range: &Option<(End, End)>, v: &End) -> bool {
    range.as_ref().is_none_or(|(lo, hi)| lo == v && hi == v)
}

/// The exact projections of `{(x, y) : value != target}` on the cells `x` (of the base input)
/// and `y`, and whether their product holds no failing point.
///
/// The proof is Theorem 1 of the PERF-ref-memo-multi-input cross-review, round 3 (Opus seat,
/// R3_OPUS.md sections 1.2-1.3, written for its `affine2_solve`), restated here for this code
/// (the Sol seat's `threshold_box`). Here the failing set is the one value `target`.
///
/// Setting. Links are numbered 0..n-1 from the base outward. Link j reads input s_j with cut
/// c_j, and its arms low_j (input <= c_j) and high_j are unit-slope bijections ([`ValTag`]).
/// These form a group under `compose` (`a.compose(b)` applies b first), and
/// [`ValTag::inverse`] is the inverse. The value at (x, y) is L_{n-1} ... L_0 (x), each L_j
/// the arm the guard picks.
///
/// Lemma 1 (prefix). If the cuts of one input do not decrease with j, the links of that input
/// where it exceeds the cut (it takes high, here called "fires") are a prefix of that input's
/// links. Proof: if v > c_j and k < j reads the same input, then c_k <= c_j < v. If the cuts do
/// not increase, the links where v <= c_j (low fires) are a prefix: v <= c_j <= c_k. The fired
/// arm is `on`, the other `off`. ∎
///
/// So x fires exactly the links of its input before a position a, its end (one past the last
/// link it fires, 0 when none), and y those of its input before its end b. Ends of the two
/// inputs differ unless both are 0, since each is one past a link of its own input.
///
/// Running products. P_j, X_j, Y_j and U_j are the composites of links 0..j-1 taking `on`
/// for both inputs, for x only, for y only and for neither (the loop below, all j <= n).
///
/// Lemma 2 (map of a cell pair). For x with end a and y with end b, the value is
/// U_n U_a^-1 X_a X_b^-1 P_b (x) when b <= a, and U_n U_b^-1 Y_b Y_a^-1 P_a (x) when a < b.
/// Proof for b <= a: a link j < b fires, whichever input it reads (an x-link has j < b <= a, a
/// y-link j < b), so links 0..b-1 compose to P_b. On b <= j < a the x-links fire and the
/// y-links do not, and X_a = (links b..a-1 in that state) X_b, so they compose to X_a X_b^-1.
/// On j >= a no link fires: U_n U_a^-1. The case a < b exchanges the inputs. ∎
///
/// Lemma 3 (one failing point). On a cell pair the value is a unit-slope bijection of x alone,
/// so exactly one integer x fails there, the root r(a, b). With T = U_n^-1(target),
/// w_a = X_a^-1 U_a (T), G_b = P_b^-1 X_b, v_b = Y_b^-1 U_b (T) and H_a = P_a^-1 Y_a,
/// inverting Lemma 2 gives r(a, b) = G_b(w_a) for b <= a and r(a, b) = H_a(v_b) for a < b. A
/// point fails iff x = r(a, b). ∎
///
/// Theorem 1. The first result is {x in cells : some y in cells passes}, the second likewise
/// for y, and the flag is true iff their product holds no failing point. Proof:
/// - x. The value depends on y only through its cell, and every cell is nonempty. So x with
///   end a fails for every y iff x = r(a, b) for every y cell b: iff all those roots are one
///   value, equal to x, iff their least and greatest are x. With G_b = (sigma_b, k_b) the roots
///   for b <= a are sigma_b w_a + k_b; for one sign they are least and greatest at the least
///   and greatest k_b, so the extrema of k_b by sign over the y cells with b <= a suffice. The
///   roots for b > a are H_a(v_b), H_a monotone, so the extrema of v_b over those cells map to
///   theirs. The y cells come in increasing end, so the first set is a prefix and the second
///   a suffix, and the x cells do too, so the prefix grows and the suffix shrinks as the
///   sweeps go. A cell loses at most its one root.
/// - y. A y cell b fails for every x iff each x equals r(a(x), b). Two points of one x cell
///   share r, so if any x cell has two points every y cell passes. Otherwise the x cells are
///   points x_i with ends a_i, and cell b fails iff k_b = x_i - sigma_b w_{a_i} for every
///   a_i >= b and v_b = H_{a_i}^-1(x_i) for every a_i < b: two "all equal one value" tests,
///   by suffix extrema (by sign) and prefix extrema.
/// - Flag. A failing point lies in the product iff, for some kept piece [lo, hi] of an x cell a
///   and kept y cell b, r(a, b) is in [lo, hi]: for b <= a, k_b in [lo - w_a, hi - w_a]
///   (sigma = +1) or [lo + w_a, hi + w_a] (sigma = -1); for a < b, v_b in H_a^-1([lo, hi]).
///   The two sweeps hold the kept y cells on one side of the split in ordered sets and ask
///   one range query per piece, so they see every (piece, cell) pair once. ∎
///
/// Checks: the PERF-ref-memo-multi-input round-3 brute-force sweeps found 0 mismatches on
/// 20000 random chains against an exact count, and caught the mutants that drop a sweep, keep
/// only the least constant, or (`late = true`) skip the y test. Test:
/// `l01_25_preimage_catalog::ref_memo::threshold_chains_match_the_interpreter_on_every_point`.
///
/// Prior work: the literature search of the PERF-ref-memo-multi-input cross-review (19
/// searches, 2026-11-21) found no method for the projections of this grid in less than one
/// visit per cell; the method here is from the cross-review's seats.
///
/// Complexity tradeoff: O(n log n) arithmetic operations and O(n) space for n links, the
/// output included. The products are O(n), the extrema sweeps O(n), and the flag sweeps
/// O(n log n), each of at most 2n + 2 pieces doing one `BTreeSet` insert and query. Each
/// constant is a signed sum of at most n literals, so it has at most B + log2(n) + 1 bits
/// for B-bit literals. Why: a method that visits each (x cell, y cell) pair is O(n^2), which
/// is what the memo did (`alternating_2var` read 25.2 from 64 to 512 links). Trigger: two
/// inputs, one interval each, guards `input <= c` with monotone cuts on each input, and
/// unit-slope arms; anything else goes to the later stages. COMPLEXITY.md
/// PERF-ref-memo-multi-input.
fn threshold_box(
    links: &[ThresholdLink],
    x: &[ThresholdCell],
    y: &[ThresholdCell],
    increasing: [bool; 2],
    target: &End,
) -> (Vec<ThresholdCell>, Vec<ThresholdCell>, bool) {
    let n = links.len();
    let mut p = ValTag::id();
    let mut mx = ValTag::id();
    let mut my = ValTag::id();
    let mut u = ValTag::id();
    let mut gx = Vec::with_capacity(n + 1);
    let mut hy = Vec::with_capacity(n + 1);
    let mut wx = Vec::with_capacity(n + 1);
    let mut uy = Vec::with_capacity(n + 1);
    for j in 0..=n {
        let pi = p.inverse();
        gx.push(pi.compose(&mx));
        hy.push(pi.compose(&my));
        wx.push(mx.inverse().compose(&u));
        uy.push(my.inverse().compose(&u));
        let Some(link) = links.get(j) else {
            break;
        };
        let (on, off) = if increasing[link.axis] {
            (&link.high, &link.low)
        } else {
            (&link.low, &link.high)
        };
        p = on.compose(&p);
        mx = (if link.axis == 0 { on } else { off }).compose(&mx);
        my = (if link.axis == 1 { on } else { off }).compose(&my);
        u = off.compose(&u);
    }
    let tail = u.inverse().map_end(target);
    let w = |a: usize| wx[a].map_end(&tail);
    let v = |b: usize| uy[b].map_end(&tail);
    let split = |a, b| b <= a;

    // x, by the first part of the proof: prefix extrema of k_b by sign, then suffix extrema of
    // v_b mapped by H_a.
    let mut roots = vec![None; x.len()];
    let mut q = 0;
    let mut offsets = [None, None];
    for (cell, root) in x.iter().zip(&mut roots) {
        while q < y.len() && split(cell.end, y[q].end) {
            let g = &gx[y[q].end];
            let k = Fin(g.1.clone());
            threshold_extrema(&mut offsets[usize::from(g.0)], k.clone(), k);
            q += 1;
        }
        let wa = w(cell.end);
        for (flip, ends) in offsets.iter().enumerate() {
            if let Some((lo, hi)) = ends {
                let signed = ValTag(flip == 1, Num::ZERO).map_end(&wa);
                if let Fin(k) = signed {
                    let add = ValTag(false, k);
                    threshold_extrema(root, add.map_end(lo), add.map_end(hi));
                }
            }
        }
    }
    let mut q = y.len();
    let mut suffix = None;
    let mut kept_x = Vec::with_capacity(x.len());
    for (cell, mut root) in x.iter().zip(roots).rev() {
        while q > 0 && !split(cell.end, y[q - 1].end) {
            q -= 1;
            let uv = v(y[q].end);
            threshold_extrema(&mut suffix, uv.clone(), uv);
        }
        if let Some((lo, hi)) = &suffix {
            let (lo, hi) = hy[cell.end].map_range(lo, hi);
            threshold_extrema(&mut root, lo, hi);
        }
        if let Some((lo, hi)) = root
            && lo == hi
            && cell.lo <= lo
            && lo <= cell.hi
        {
            // The cells are visited backward. Push the right piece first.
            if lo < cell.hi {
                kept_x.push(ThresholdCell {
                    end: cell.end,
                    lo: lo.succ(),
                    hi: cell.hi.clone(),
                });
            }
            if cell.lo < lo {
                kept_x.push(ThresholdCell {
                    end: cell.end,
                    lo: cell.lo.clone(),
                    hi: lo.pred(),
                });
            }
        } else {
            kept_x.push(cell.clone());
        }
    }
    kept_x.reverse();

    // y, by the second part of the proof, over the x cells (not the kept pieces).
    let kept_y: Vec<ThresholdCell> = if x.iter().any(|cell| cell.lo != cell.hi) {
        y.to_vec()
    } else {
        let mut suffixes = vec![[None, None]; x.len() + 1];
        for (i, cell) in x.iter().enumerate().rev() {
            let Fin(wa) = w(cell.end) else {
                unreachable!("w maps the finite target to a finite value")
            };
            let mut pair = suffixes[i + 1].clone();
            for (flip, offset) in [ValTag(false, -&wa), ValTag(false, wa)].iter().enumerate() {
                let k = offset.map_end(&cell.lo);
                threshold_extrema(&mut pair[flip], k.clone(), k);
            }
            suffixes[i] = pair;
        }
        let mut i = 0;
        let mut prefix = None;
        y.iter()
            .filter(|cell| {
                while i < x.len() && !split(x[i].end, cell.end) {
                    let z = hy[x[i].end].inverse().map_end(&x[i].lo);
                    threshold_extrema(&mut prefix, z.clone(), z);
                    i += 1;
                }
                let g = &gx[cell.end];
                !(threshold_uniform(&prefix, &v(cell.end))
                    && threshold_uniform(&suffixes[i][usize::from(g.0)], &Fin(g.1.clone())))
            })
            .cloned()
            .collect()
    };

    // The flag, by the third part of the proof: range queries on k_b by sign, then on v_b.
    let mut offsets = [BTreeSet::new(), BTreeSet::new()];
    let mut q = 0;
    for cell in &kept_x {
        while q < kept_y.len() && split(cell.end, kept_y[q].end) {
            let g = &gx[kept_y[q].end];
            offsets[usize::from(g.0)].insert(Fin(g.1.clone()));
            q += 1;
        }
        let Fin(wa) = w(cell.end) else {
            unreachable!("w maps the finite target to a finite value")
        };
        for (set, shift) in offsets.iter().zip([ValTag(false, -&wa), ValTag(false, wa)]) {
            let (lo, hi) = shift.map_range(&cell.lo, &cell.hi);
            if set.range(lo..=hi).next().is_some() {
                return (kept_x, kept_y, false);
            }
        }
    }
    let mut suffix = BTreeSet::new();
    let mut q = kept_y.len();
    for cell in kept_x.iter().rev() {
        while q > 0 && !split(cell.end, kept_y[q - 1].end) {
            q -= 1;
            suffix.insert(v(kept_y[q].end));
        }
        let (lo, hi) = hy[cell.end].inverse().map_range(&cell.lo, &cell.hi);
        if suffix.range(lo..=hi).next().is_some() {
            return (kept_x, kept_y, false);
        }
    }
    (kept_x, kept_y, true)
}

/// The relation `value != target` of a threshold chain over the inputs `names` (base first):
/// one auxiliary variable per link, defined as the link's `if`, so it holds exactly where the
/// term meets the demand. O(n) definitions of O(1) size.
fn threshold_relation(links: &[ThresholdLink], names: &[Arc<str>; 2], target: i64) -> Relation {
    let [x, y] = names
        .each_ref()
        .map(|name| Lin::atom(presburger::Atom::Sym(name.clone())));
    let inputs = [x.clone(), y];
    let mut value = x;
    let mut tr = Tr {
        defs: Vec::with_capacity(links.len()),
        products: false,
    };
    for link in links {
        let g = Formula::Con(Con::ge(&Lin::constant(link.cut), &inputs[link.axis]));
        let arm = |tag: &ValTag| {
            let shift = Lin::constant(tag.1.to_i128().expect("one literal offset"));
            value.times(if tag.0 { -1 } else { 1 }).plus(&shift)
        };
        let (low, high) = (arm(&link.low), arm(&link.high));
        let out = Lin::atom(presburger::Atom::Aux(to_u32(tr.defs.len(), "definitions")));
        let what = format!("if {g} then {low} else {high}");
        let def = Formula::or(vec![
            Formula::and(vec![g.clone(), Formula::Con(Con::eq(&out, &low))]),
            Formula::and(vec![Formula::negate(g), Formula::Con(Con::eq(&out, &high))]),
        ]);
        tr.aux(what, def);
        value = out;
    }
    Relation {
        body: Formula::negate(Formula::Con(Con::eq(&value, &Lin::constant(target)))),
        defs: tr.defs,
        bit_ands: Vec::new(),
    }
}

impl Tx<'_> {
    /// The exact answer for `chain != c` (or `chain == c` demanded false) where `chain` is a
    /// threshold chain on two inputs (the Sol seat's stage, PERF-ref-memo-multi-input round
    /// 3): each link is `if input <= c' { arm } else { arm }` (or `<`, `>`, `>=`), both arms
    /// unit-slope maps (`t`, `-t`, `t + c`, `t - c`, `c + t`, `c - t`) of one inner value, the
    /// innermost value the base input, the cuts of each input monotone in chain order, and each
    /// input one interval. `None` otherwise. Not exact means a relation, [`threshold_relation`],
    /// is attached. The proof is at [`threshold_box`].
    ///
    /// Complexity tradeoff: the walk is O(n): it reads each `If` once, by its id and literal
    /// operands, and never calls `fwd` or `lin`. A shallow copy of an `If` (both arms of the
    /// family builder read one `t`) has its own id but its children's ids, so
    /// [`Tx::same_value_node`] compares the two arms' inner values in O(1). Then
    /// [`threshold_box`] costs O(n log n).
    fn affine_threshold_pair(&self, root: Tid, demand: &Demand) -> Option<(Res, Option<Relation>)> {
        let Node::Prim(op, args) = self.node(root) else {
            return None;
        };
        if !matches!(
            (op, demand),
            (Prim::Ne, Demand::Bool(true)) | (Prim::Eq, Demand::Bool(false))
        ) || args.len() != 2
        {
            return None;
        }
        let (a, b) = (self.arg(args, 0), self.arg(args, 1));
        let (mut cur, target) = match (self.node(a), self.node(b)) {
            (_, Node::Int(d)) => (a, d),
            (Node::Int(d), _) => (b, d),
            _ => return None,
        };
        let mut variables = Vec::new();
        let mut links = Vec::new();
        while let Node::If(g, a, b) = self.node(cur) {
            let Node::Prim(cmp, args) = self.node(g) else {
                return None;
            };
            if args.len() != 2 {
                return None;
            }
            let (first, second) = (self.node(self.arg(args, 0)), self.node(self.arg(args, 1)));
            let (var, mut cut, cmp) = match (first, second) {
                (Node::Var(v), Node::Int(c)) => (v, i128::from(c), cmp),
                (Node::Int(c), Node::Var(v)) => (v, i128::from(c), mirror(cmp)),
                _ => return None,
            };
            // As `var <= cut`, with the arms exchanged for `>` and `>=`.
            let swap = match cmp {
                Prim::Le => false,
                Prim::Lt => {
                    cut -= 1;
                    false
                }
                Prim::Gt => true,
                Prim::Ge => {
                    cut -= 1;
                    true
                }
                _ => return None,
            };
            let axis = if let Some(axis) = variables.iter().position(|&v| v == var) {
                axis
            } else {
                if variables.len() == 2 {
                    return None;
                }
                variables.push(var);
                variables.len() - 1
            };
            let (an, av) = self.threshold_arm(a);
            let (bn, bv) = self.threshold_arm(b);
            if !self.same_value_node(an, bn) {
                return None;
            }
            let (low, high) = if swap { (bv, av) } else { (av, bv) };
            links.push(ThresholdLink {
                axis,
                cut,
                low,
                high,
            });
            cur = an;
        }
        let Node::Var(base) = self.node(cur) else {
            return None;
        };
        let base_name = self.name(base).clone();
        let other_name = if let Some(&other) = variables.iter().find(|&&v| v != base) {
            self.name(other).clone()
        } else {
            if self.cx.inputs.len() != 2 {
                return None;
            }
            self.cx
                .inputs
                .iter()
                .find(|(name, _)| *name != &base_name)?
                .0
                .clone()
        };
        if variables.len() == 2 && !variables.contains(&base) {
            return None;
        }
        // Axis 0 is the base. The base may have no guard (for example one link on `m`).
        if variables.first().is_some_and(|&v| v != base) {
            for link in &mut links {
                link.axis = 1 - link.axis;
            }
        }
        // From the base outward.
        links.reverse();
        let mut increasing = [true; 2];
        for (axis, rising) in increasing.iter_mut().enumerate() {
            let cuts = || {
                links
                    .iter()
                    .filter(|link| link.axis == axis)
                    .map(|link| link.cut)
            };
            if !cuts().is_sorted() {
                if !cuts().map(|cut| -cut).is_sorted() {
                    return None;
                }
                *rising = false;
            }
        }
        let names = [base_name, other_name];
        let x = self.cx.inputs.get(&names[0])?;
        let y = self.cx.inputs.get(&names[1])?;
        if x.len() > 1 || y.len() > 1 {
            return None;
        }
        if self.run.void {
            return Some((Res::none(), None));
        }
        let x_cells = threshold_cells(&links, 0, x.first()?, increasing[0]);
        let y_cells = threshold_cells(&links, 1, y.first()?, increasing[1]);
        let (proj_x, proj_y, exact) =
            threshold_box(&links, &x_cells, &y_cells, increasing, &End::of(target));
        if proj_x.is_empty() || proj_y.is_empty() {
            return Some((Res::none(), None));
        }
        let mut out = Res::all();
        out.exact = exact;
        out.vars = VarSet::Many;
        for ((name, domain), cells) in names.iter().zip([x, y]).zip([proj_x, proj_y]) {
            let proj = IntervalSet::from_pieces(cells.into_iter().map(|c| (c.lo, c.hi)).collect());
            if &proj != domain.as_ref() {
                out.dom.insert(name.clone(), Rc::new(proj));
            }
        }
        let relation = (!exact).then(|| threshold_relation(&links, &names, target));
        Some((out, relation))
    }

    /// The inner value of a threshold arm and the unit-slope map applied to it: `-t`, `c + t`,
    /// `c - t`, `t + c`, `t - c`, else `t` itself.
    fn threshold_arm(&self, t: Tid) -> (Tid, ValTag) {
        if let Node::Prim(op, args) = self.node(t) {
            if op == Prim::Neg && args.len() == 1 {
                return (self.arg(args, 0), ValTag::neg());
            }
            if matches!(op, Prim::Add | Prim::Sub) && args.len() == 2 {
                let (a, b) = (self.arg(args, 0), self.arg(args, 1));
                if let Node::Int(c) = self.node(a) {
                    return (
                        b,
                        if op == Prim::Sub {
                            ValTag::reflect(i128::from(c))
                        } else {
                            ValTag::shift(i128::from(c))
                        },
                    );
                }
                if let Node::Int(c) = self.node(b) {
                    let c = i128::from(c);
                    return (a, ValTag::shift(if op == Prim::Sub { -c } else { c }));
                }
            }
        }
        (t, ValTag::id())
    }

    /// Whether `a` and `b` have one value in every environment: the same node, two `If`s with
    /// the same children, or the same variable or literal. O(1).
    fn same_value_node(&self, a: Tid, b: Tid) -> bool {
        a == b
            || match (self.node(a), self.node(b)) {
                (Node::If(g, x, y), Node::If(h, u, v)) => (g, x, y) == (h, u, v),
                (Node::Var(x), Node::Var(y)) => x == y,
                (Node::Int(x), Node::Int(y)) => x == y,
                _ => false,
            }
    }
}

/// The end of a unit-slope path ([`Tx::affine_end_no_fwd`]): a constant, an input, or the first
/// node that is not a unit-slope step (an `If`, in a chain the independent stage reads).
#[derive(Clone, PartialEq, Eq)]
enum AffineBase {
    Const,
    Input(Arc<str>),
    Node(At),
}

/// One link of a chain [`Tx::independent_affine`] reads: the guard's input, the masks of its
/// two arms (the values of the input that take each), and each arm's unit-slope map, `None`
/// when its mask is empty.
type IndepLink = (
    Arc<str>,
    IntervalSet,
    IntervalSet,
    Option<ValTag>,
    Option<ValTag>,
);

impl Tx<'_> {
    /// Whether two path ends have one value: both constants, the same input, or two nodes in
    /// one environment with one value ([`Tx::same_value_node`]). O(1).
    fn same_affine_base(&self, a: &AffineBase, b: &AffineBase) -> bool {
        match (a, b) {
            (AffineBase::Const, AffineBase::Const) => true,
            (AffineBase::Input(x), AffineBase::Input(y)) => x == y,
            (AffineBase::Node(u), AffineBase::Node(v)) => {
                u == v || (u.1 == v.1 && self.same_value_node(u.0, v.0))
            }
            _ => false,
        }
    }

    /// The end of the unit-slope path from `u` and the map from the end's value to `u`'s:
    /// through `-t`, `t ± c`, `c ± t`, variables and lets, to a constant (base value 0), an
    /// input or an `If`. `None` at any other node, or at a variable bound to no input. Unlike
    /// [`Tx::affine_end`], it reads no forward fact and follows any number of inputs, which
    /// the independent stage needs. Each node and environment is visited once (`memo`), so
    /// the paths of a whole chain cost O(size of the chain).
    fn affine_end_no_fwd(
        &mut self,
        u: At,
        memo: &mut HashMap<At, (AffineBase, ValTag)>,
    ) -> Option<(AffineBase, ValTag)> {
        if let Some(v) = memo.get(&u) {
            return Some(v.clone());
        }
        let out = match self.node(u.0) {
            Node::Int(n) => (AffineBase::Const, ValTag::shift(i128::from(n))),
            Node::Lit(Value::Big(b)) => (AffineBase::Const, ValTag(false, Num::from(&**b))),
            Node::Var(x) => match self.lookup(u.1, x) {
                Some(to) => self.affine_end_no_fwd(to, memo)?,
                None => {
                    let name = self.name(x).clone();
                    if !self.cx.inputs.contains_key(&name) {
                        return None;
                    }
                    (AffineBase::Input(name), ValTag::id())
                }
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, u.1);
                self.affine_end_no_fwd((b, inner), memo)?
            }
            Node::If(..) => (AffineBase::Node(u), ValTag::id()),
            Node::Prim(Prim::Neg, args) if args.len() == 1 => {
                let (base, inner) = self.affine_end_no_fwd((self.arg(args, 0), u.1), memo)?;
                (base, ValTag::neg().compose(&inner))
            }
            Node::Prim(p @ (Prim::Add | Prim::Sub), args) if args.len() == 2 => {
                let (a, b) = (self.arg(args, 0), self.arg(args, 1));
                // A literal side is read directly: `constant_int` of the other side first
                // walks it for inputs (`mentions`), O(its size), on terms this stage declines.
                let (ca, cb) = match (self.node(a), self.node(b)) {
                    (Node::Int(c), _) => (Some(c), None),
                    (_, Node::Int(c)) => (None, Some(c)),
                    _ => (self.constant_int(a, u.1), self.constant_int(b, u.1)),
                };
                let (child, tag) = match (p, ca, cb) {
                    (Prim::Add, Some(c), _) => (b, ValTag::shift(i128::from(c))),
                    (Prim::Add, _, Some(c)) => (a, ValTag::shift(i128::from(c))),
                    (Prim::Sub, _, Some(c)) => (a, ValTag::shift(-i128::from(c))),
                    (Prim::Sub, Some(c), _) => (b, ValTag::reflect(i128::from(c))),
                    _ => return None,
                };
                let (base, inner) = self.affine_end_no_fwd((child, u.1), memo)?;
                (base, tag.compose(&inner))
            }
            _ => return None,
        };
        memo.insert(u, out.clone());
        Some(out)
    }

    /// Chains of guards on distinct inputs (`indep_varying`; PERF-ref-memo-multi-input part
    /// (b)): n links `t_j = if g_j(b_j) { T_{j,0}(t_{j-1}) } else { T_{j,1}(t_{j-1}) }`, links
    /// numbered from the base `t_0 = z` (an input, or a constant), each guard `g_j` reading one
    /// input `b_j`, the `b_j` distinct and none of them `z`, each arm `T` a unit-slope map
    /// `v -> ±v + k` ([`ValTag`]), and a demand whose complement E is empty or one interval.
    /// Arm `T_{j,s}` is *allowed* when its mask (the values of `b_j` that take it) is not empty.
    /// The answer is the exact projections, and the exactness flag when one of four checks
    /// decides it; `None` (main's path) otherwise.
    ///
    /// Independence. Every input but `z` is read by one guard only, so for any choice of one
    /// allowed arm per link, and any z, some point of the box takes exactly those arms from z.
    /// Every claim below about "some point" rests on this.
    ///
    /// Proof of the projections.
    /// 1. Doomed values. Let U_n = E and U_j = the meet, over the allowed arms T of link j, of
    ///    T^-1(U_{j+1}). A value v of t_j is in U_j iff every choice of arms after j fails from
    ///    v: by induction from n down, since by independence the arm of link j can be chosen
    ///    freely. Each T^-1 of an interval is an interval (T is a bijection of the integers
    ///    that keeps or reverses order), and a meet of intervals is an interval, so each U_j is
    ///    empty or one interval.
    /// 2. z. A value z is in the projection iff some point from z passes iff z is not in U_0
    ///    (step 1 at j = 0). So the projection is `dom(z) - U_0`, exact.
    /// 3. b_j. Let F_j be the values t_j takes over the box. A value w of b_j in the mask of
    ///    arm s is in the projection iff some v in F_j has T_{j,s}(v) outside U_{j+1}
    ///    (independence again: links before j are free, links after j by step 1), that is
    ///    iff F_j is not inside the interval W = T_{j,s}^-1(U_{j+1}). A set lies inside an
    ///    interval iff its least and greatest members do, and these are exact:
    ///    min F_{j+1} = min over allowed arms of `T(v)` at v = min F_j (T keeps order) or at
    ///    v = max F_j (T reverses it), likewise max, from `[min, max]` of `dom(z)`. So each
    ///    arm is *surviving* or not exactly, and the projection of b_j is the join of the
    ///    masks of its surviving arms.
    ///
    /// Proof of the flag. The box B is the product of the projections; by independence, the
    /// points of B are z in the z projection with any choice of one surviving arm per link,
    /// and B is exact iff no such point lands in E.
    /// - Check 1. If the z projection is one interval and each F'_j (the values over B, the
    ///   join of the images of F'_{j-1} under the surviving arms) stays one interval, F'_n is
    ///   exact, since the image of an interval under T is an interval and a join is the union:
    ///   B is exact iff F'_n misses E.
    /// - Check 2. The value at the root is `sigma z + K` for a sign sigma and a constant K
    ///   that depend on the arms. For each sign, the K reached form a set, kept as an
    ///   arithmetic progression `{lo, lo + step, ..., hi}` that contains it, marked exact when
    ///   it equals it ([`ApNum`]). A shift or reflection keeps both properties. A join takes
    ///   the step `g = gcd(a.step, b.step, |a.lo - b.lo|)`, so it contains both; it is exact
    ///   only in the cases where the union fills every multiple of g in `[lo, hi]`: two single
    ///   values; two progressions of step g that overlap or touch (`max lo <= min hi + g`); a
    ///   progression of step g and a value within g of it; two of step 2g, which then lie on
    ///   the two residues mod 2g, with both ends within g of each other. If neither sign can
    ///   reach E, B is exact. If an exact progression reaches E, B is not. Reaching is tested
    ///   per piece of the z projection: `s + lo + k step` in E for s in the piece and
    ///   `0 <= k <= (hi - lo) / step` reduces to k step in `[E.lo - lo - s.hi, E.hi - lo -
    ///   s.lo]`; the least such k is at most `(hi - lo) / step` because the piece lies in the
    ///   window where some K of `[lo, hi]` reaches E, and if it is negative k = 0 serves. The
    ///   same is done from the root down (suffix compositions), which reaches other cases.
    /// - Checks 3 and 4 only find failing points: the compositions of least and greatest
    ///   constant per sign, the all-first-surviving-arm choice and each choice that differs
    ///   from it at one link (Check 3), and a walk down from each end of `E ∩ [min F_n, max
    ///   F_n]` picking at each link a surviving arm whose preimage lies in `[min F_j, max F_j]`
    ///   (Check 4). Each is a choice of surviving arms and a z in the z projection whose value
    ///   is in E, so a point of B that fails: B is not exact.
    /// - Otherwise `None`: no check decided, and main's path answers. No exact check of this
    ///   cost exists unless P = NP: with z fixed to 0, guards `b_j <= 0` over `0..=1`, arms
    ///   `t + a_j` and `t` with every a_j nonzero, n >= 2 and the demand `t != S`, U_j is
    ///   empty for j < n (U_{n-1} = {S - a_n} meet {S}), so every arm survives, B is the
    ///   whole box, and B is exact iff no subset of the a_j sums to S. Subset sum is
    ///   NP-complete (Karp, "Reducibility among combinatorial problems", 1972,
    ///   doi:10.1007/978-1-4684-2001-2_9, problem "Knapsack"), so deciding exactness here is
    ///   coNP-hard (test `ref_memo::subset_sum_chains_are_exact_iff_no_subset_reaches_the_demand`).
    ///   ∎
    ///
    /// Complexity tradeoff: O(n) links visited once (a memo over the affine segments), O(n)
    /// interval and progression operations in each step and check, each on numbers of at most
    /// B + log2(n) + 1 bits for B-bit literals (a gcd costs a factor in the bits). Why: main's
    /// path visits the combinations of arms (`indep_varying` read 183 from 24 to 192 links on
    /// it, 7.99 here).
    /// Given up: exactness when no check decides, which is coNP-hard as proved above; main's
    /// path answers it at its own cost. Trigger: the shape of the term, never a size. Tests:
    /// `l01_25_preimage_catalog::ref_memo::independent_chains_match_the_interpreter_on_every_point`,
    /// `bench::ref_memo::indep_varying_scales`. COMPLEXITY.md PERF-ref-memo-multi-input (b).
    fn independent_affine(&mut self, root: Tid, d: &Demand) -> Option<(Res, Option<Relation>)> {
        // The complement of k disjoint, non-adjacent intervals has k - 1 gaps between them, so
        // for k >= 3 it is not one interval: decline before the O(k) copy and complement.
        if matches!(d, Demand::Ints(z) if z.len() > 2) {
            return None;
        }
        let (original, wanted) = self.integer_request_shape(root, d)?;
        let excl_set = IntervalSet::top().minus(&wanted);
        if excl_set.len() > 1 {
            return None;
        }
        let excl: Option<(End, End)> = excl_set.first().cloned();
        let mut memo: HashMap<At, (AffineBase, ValTag)> = HashMap::new();
        let (mut cur, mut tail_tag) = self.affine_end_no_fwd((original, ROOT), &mut memo)?;
        let mut seen = HashSet::new();
        let mut guard_names = HashSet::new();
        // Collected root-to-base, then reversed to base-to-root.
        let mut rev_links: Vec<IndepLink> = Vec::new();
        let base_var: Option<Arc<str>>;
        loop {
            match cur {
                AffineBase::Input(x) => {
                    if guard_names.contains(&x) {
                        return None;
                    }
                    base_var = Some(x);
                    break;
                }
                AffineBase::Const => {
                    base_var = None;
                    break;
                }
                AffineBase::Node(u) => {
                    if !seen.insert(u) {
                        return None;
                    }
                    let Node::If(g, a, b) = self.node(u.0) else {
                        return None;
                    };
                    let (gx, m0, m1) = if let Some((Coordinate::Input(gx), y, n)) =
                        self.difference_guard(g, u.1)
                    {
                        let dom_g = self.cx.inputs[&gx].clone();
                        let to_set = |m: ArmMask| {
                            m.map_or_else(|| (*dom_g).clone(), |(live, _)| (*live).clone())
                        };
                        (gx, to_set(y), to_set(n))
                    } else {
                        let yes = self.back_at(g, u.1, &Demand::Bool(true));
                        let no = self.back_at(g, u.1, &Demand::Bool(false));
                        if !yes.exact || !no.exact {
                            return None;
                        }
                        let VarSet::One(gx) = yes.vars.join(&no.vars) else {
                            return None;
                        };
                        let dom_g = self.cx.inputs.get(&gx)?;
                        let to_set = |r: &Res| {
                            if r.none {
                                IntervalSet::empty()
                            } else {
                                r.dom
                                    .get(&gx)
                                    .map_or_else(|| (**dom_g).clone(), |s| (**s).clone())
                            }
                        };
                        let (sy, sn) = (to_set(&yes), to_set(&no));
                        (gx, sy, sn)
                    };
                    if !guard_names.insert(gx.clone()) {
                        return None;
                    }
                    let (at, av) = self.affine_end_no_fwd((a, u.1), &mut memo)?;
                    let (bt, bv) = self.affine_end_no_fwd((b, u.1), &mut memo)?;
                    if !self.same_affine_base(&at, &bt) {
                        return None;
                    }
                    let t0 = (!m0.is_empty()).then(|| tail_tag.compose(&av));
                    let t1 = (!m1.is_empty()).then(|| tail_tag.compose(&bv));
                    rev_links.push((gx, m0, m1, t0, t1));
                    cur = at;
                    tail_tag = ValTag::id();
                }
            }
        }
        if rev_links.is_empty() {
            return None;
        }
        let mut links = rev_links;
        links.reverse();
        let n = links.len();
        let dom_z = match &base_var {
            Some(z) => (**self.cx.inputs.get(z)?).clone(),
            None => IntervalSet::single(0),
        };
        let (zlo, zhi) = dom_z.bounds()?;

        // Step 1a: Backward doomed intervals U_j (each <= 1 interval).
        let map_iv = |iv: &Option<(End, End)>, t: &ValTag| -> Option<(End, End)> {
            iv.as_ref().map(|(l, h)| t.map_range(l, h))
        };
        let meet_iv = |a: Option<(End, End)>, b: Option<(End, End)>| -> Option<(End, End)> {
            let ((al, ah), (bl, bh)) = (a?, b?);
            let (l, h) = (al.max(bl), ah.min(bh));
            (l <= h).then_some((l, h))
        };
        let mut u: Vec<Option<(End, End)>> = vec![None; n + 1];
        u[n] = excl.clone();
        for j in (0..n).rev() {
            let mut acc: Option<Option<(End, End)>> = None;
            for arm in [links[j].3.as_ref(), links[j].4.as_ref()]
                .into_iter()
                .flatten()
            {
                let pre = map_iv(&u[j + 1], &arm.inverse());
                acc = Some(match acc {
                    None => pre,
                    Some(old) => meet_iv(old, pre),
                });
            }
            u[j] = acc.flatten();
        }

        // Step 1b: Forward exact min/max of reachable values F_j.
        let mut f_bounds: Vec<(End, End)> = vec![(zlo.clone(), zhi.clone()); n + 1];
        for j in 0..n {
            let (pl, ph) = &f_bounds[j];
            let mut acc: Option<(End, End)> = None;
            for arm in [links[j].3.as_ref(), links[j].4.as_ref()]
                .into_iter()
                .flatten()
            {
                let (l, h) = arm.map_range(pl, ph);
                acc = Some(match acc {
                    None => (l, h),
                    Some((ol, oh)) => (ol.min(l), oh.max(h)),
                });
            }
            let Some(next) = acc else {
                return Some((Res::none(), None));
            };
            f_bounds[j + 1] = next;
        }

        // Exact projection onto z and every guard input b_j.
        let proj_z = match &u[0] {
            None => dom_z.clone(),
            Some((ul, uh)) => dom_z.minus(&IntervalSet::range(ul.clone(), uh.clone())),
        };
        if proj_z.is_empty() {
            return Some((Res::none(), None));
        }
        let iv_contains = |outer: &Option<(End, End)>, inner: &(End, End)| -> bool {
            outer
                .as_ref()
                .is_some_and(|(ol, oh)| ol <= &inner.0 && &inner.1 <= oh)
        };
        let mut surviving = Vec::with_capacity(n);
        for j in 0..n {
            let s0 = links[j]
                .3
                .as_ref()
                .is_some_and(|t| !iv_contains(&map_iv(&u[j + 1], &t.inverse()), &f_bounds[j]));
            let s1 = links[j]
                .4
                .as_ref()
                .is_some_and(|t| !iv_contains(&map_iv(&u[j + 1], &t.inverse()), &f_bounds[j]));
            surviving.push((s0, s1));
        }

        // The flag, in O(n) (the proof in the doc above), by four checks:
        // (1) Exact 1-interval forward sets F_j (Opus criterion, generalized to interval E);
        // (2) Forward & reverse Arithmetic Progression abstraction ApNum (Gemini criterion);
        // (3) Attained extrema + baseline + 1-flip witness scan (Sol criterion);
        // (4) Greedy backward witness reconstruction verified forward.
        let mut decided_exact: Option<bool> = None;

        // Check 1: Exact 1-interval forward sets F_j over narrowed box `proj_z x prod A'_j`.
        if proj_z.len() == 1 {
            let mut f = proj_z.clone();
            let mut single = true;
            for j in 0..n {
                let mut next = IntervalSet::empty();
                for (ok, arm) in [
                    (surviving[j].0, links[j].3.as_ref()),
                    (surviving[j].1, links[j].4.as_ref()),
                ] {
                    if ok {
                        next = next.join(&arm.unwrap().map_set(&f));
                    }
                }
                if next.len() > 1 {
                    single = false;
                    break;
                }
                f = next;
            }
            if single {
                let fails = excl.as_ref().is_some_and(|(el, eh)| {
                    !f.meet(&IntervalSet::range(el.clone(), eh.clone()))
                        .is_empty()
                });
                decided_exact = Some(!fails);
            }
        }

        // Check 2: Forward & reverse AP propagation when Check 1 did not decide.
        #[derive(Clone)]
        struct ApNum {
            lo: Num,
            hi: Num,
            step: Num,
            exact: bool,
        }
        impl ApNum {
            fn single(v: Num) -> Self {
                Self {
                    lo: v.clone(),
                    hi: v,
                    step: Num::ZERO,
                    exact: true,
                }
            }
            fn shift(&self, d: &Num) -> Self {
                Self {
                    lo: &self.lo + d,
                    hi: &self.hi + d,
                    step: self.step.clone(),
                    exact: self.exact,
                }
            }
            fn reflect(&self, c: &Num) -> Self {
                Self {
                    lo: c - &self.hi,
                    hi: c - &self.lo,
                    step: self.step.clone(),
                    exact: self.exact,
                }
            }
            fn join(a: Option<Self>, b: Option<Self>) -> Option<Self> {
                let (a, b) = match (a, b) {
                    (None, x) | (x, None) => return x,
                    (Some(a), Some(b)) => (a, b),
                };
                let lo = a.lo.clone().min(b.lo.clone());
                let hi = a.hi.clone().max(b.hi.clone());
                let g = a.step.gcd(&b.step).gcd(&(&a.lo - &b.lo).abs());
                if g.is_zero() {
                    return Some(Self::single(lo));
                }
                let two_g = &g + &g;
                let exact = if !a.exact || !b.exact {
                    false
                } else if a.step.is_zero() && b.step.is_zero() {
                    true
                } else if a.step == g && b.step == g {
                    a.lo.clone().max(b.lo.clone()) <= &(a.hi.clone().min(b.hi.clone())) + &g
                } else if a.step == g && b.step.is_zero() {
                    b.lo >= &a.lo - &g && b.lo <= &a.hi + &g
                } else if b.step == g && a.step.is_zero() {
                    a.lo >= &b.lo - &g && a.lo <= &b.hi + &g
                } else if a.step == two_g && b.step == two_g {
                    a.lo.clone().max(b.lo.clone()) <= &(a.hi.clone().min(b.hi.clone())) + &g
                        && (&a.lo - &b.lo).abs() <= g
                        && (&a.hi - &b.hi).abs() <= g
                } else {
                    false
                };
                Some(Self {
                    lo,
                    hi,
                    step: g,
                    exact,
                })
            }
        }

        // Check whether `{sigma * z + K | z in proj_z, K in ap}` meets `excl`.
        // Returns `(possible_in_ap, definite_when_exact)`.
        let ap_hits_excl = |sigma_neg: bool, ap: &Option<ApNum>| -> (bool, bool) {
            let (Some((el, eh)), Some(ap)) = (&excl, ap) else {
                return (false, false);
            };
            let (zlo, zhi) = if !sigma_neg {
                (
                    match el {
                        Fin(v) => Fin(v - &ap.hi),
                        e => e.clone(),
                    },
                    match eh {
                        Fin(v) => Fin(v - &ap.lo),
                        e => e.clone(),
                    },
                )
            } else {
                (
                    match eh {
                        Fin(v) => Fin(&ap.lo - v),
                        NegInf => PosInf,
                        PosInf => NegInf,
                    },
                    match el {
                        Fin(v) => Fin(&ap.hi - v),
                        NegInf => PosInf,
                        PosInf => NegInf,
                    },
                )
            };
            let sub = proj_z.meet(&IntervalSet::range(zlo, zhi));
            if sub.is_empty() {
                return (false, false);
            }
            if ap.step.is_zero() || ap.step == Num::ONE {
                return (true, ap.exact);
            }
            // Check residue congruence modulo `ap.step`.
            let (Fin(el_n), Fin(eh_n)) = (el, eh) else {
                return (true, ap.exact);
            };
            if &(eh_n - el_n) + &Num::ONE >= ap.step {
                return (true, ap.exact);
            }
            for (a, b) in sub.pieces() {
                let (sl, sh) = if !sigma_neg {
                    (a.clone(), b.clone())
                } else {
                    (-b, -a)
                };
                let (Fin(sl_n), Fin(sh_n)) = (&sl, &sh) else {
                    return (true, ap.exact);
                };
                if &(sh_n - sl_n) + &Num::ONE >= ap.step {
                    return (true, ap.exact);
                }
                let lo_num = &(el_n - &ap.lo) - sh_n;
                let hi_num = &(eh_n - &ap.lo) - sl_n;
                let k = (&(&lo_num + &ap.step) - &Num::ONE).div_floor(&ap.step);
                if &k * &ap.step <= hi_num {
                    return (true, ap.exact);
                }
            }
            (false, false)
        };

        let exact = if let Some(ex) = decided_exact {
            ex
        } else {
            let mut pref_pos: Vec<Option<ApNum>> = vec![None; n + 1];
            let mut pref_neg: Vec<Option<ApNum>> = vec![None; n + 1];
            pref_pos[0] = Some(ApNum::single(Num::ZERO));
            for j in 0..n {
                let (mut np, mut nn) = (None, None);
                for (ok, arm) in [
                    (surviving[j].0, links[j].3.as_ref()),
                    (surviving[j].1, links[j].4.as_ref()),
                ] {
                    if !ok {
                        continue;
                    }
                    let t = arm.unwrap();
                    if !t.0 {
                        np = ApNum::join(np, pref_pos[j].as_ref().map(|a| a.shift(&t.1)));
                        nn = ApNum::join(nn, pref_neg[j].as_ref().map(|a| a.shift(&t.1)));
                    } else {
                        np = ApNum::join(np, pref_neg[j].as_ref().map(|a| a.reflect(&t.1)));
                        nn = ApNum::join(nn, pref_pos[j].as_ref().map(|a| a.reflect(&t.1)));
                    }
                }
                pref_pos[j + 1] = np;
                pref_neg[j + 1] = nn;
            }
            let (p_poss, p_def) = ap_hits_excl(false, &pref_pos[n]);
            let (n_poss, n_def) = ap_hits_excl(true, &pref_neg[n]);
            if !p_poss && !n_poss {
                true
            } else if p_def || n_def {
                false
            } else {
                // Reverse (suffix) AP check in O(n).
                let (mut suf_pos, mut suf_neg): (Option<ApNum>, Option<ApNum>) =
                    (Some(ApNum::single(Num::ZERO)), None);
                for j in (0..n).rev() {
                    let (mut np, mut nn) = (None, None);
                    for (ok, arm) in [
                        (surviving[j].0, links[j].3.as_ref()),
                        (surviving[j].1, links[j].4.as_ref()),
                    ] {
                        if !ok {
                            continue;
                        }
                        let t = arm.unwrap();
                        let neg_k = -&t.1;
                        if !t.0 {
                            np = ApNum::join(np, suf_pos.as_ref().map(|a| a.shift(&t.1)));
                            nn = ApNum::join(nn, suf_neg.as_ref().map(|a| a.shift(&neg_k)));
                        } else {
                            np = ApNum::join(np, suf_neg.as_ref().map(|a| a.shift(&neg_k)));
                            nn = ApNum::join(nn, suf_pos.as_ref().map(|a| a.shift(&t.1)));
                        }
                    }
                    suf_pos = np;
                    suf_neg = nn;
                }
                let (sp_poss, sp_def) = ap_hits_excl(false, &suf_pos);
                let (sn_poss, sn_def) = ap_hits_excl(true, &suf_neg);
                if !sp_poss && !sn_poss {
                    true
                } else if sp_def || sn_def {
                    false
                } else {
                    // Check 3: Attained extrema + baseline + 1-flip witness scan (O(n)).
                    let tag_hits = |tag: &ValTag| -> bool {
                        excl.as_ref().is_some_and(|(el, eh)| {
                            let (pl, ph) = tag.inverse().map_range(el, eh);
                            !proj_z.meet(&IntervalSet::range(pl, ph)).is_empty()
                        })
                    };
                    let mut min_p: Option<ValTag> = Some(ValTag::id());
                    let mut max_p: Option<ValTag> = Some(ValTag::id());
                    let mut min_n: Option<ValTag> = None;
                    let mut max_n: Option<ValTag> = None;
                    let upd_min = |cur: &mut Option<ValTag>, cand: ValTag| {
                        if cur.as_ref().is_none_or(|c| cand.1 < c.1) {
                            *cur = Some(cand);
                        }
                    };
                    let upd_max = |cur: &mut Option<ValTag>, cand: ValTag| {
                        if cur.as_ref().is_none_or(|c| cand.1 > c.1) {
                            *cur = Some(cand);
                        }
                    };
                    for j in 0..n {
                        let (mut np_lo, mut np_hi, mut nn_lo, mut nn_hi) = (None, None, None, None);
                        for (ok, arm) in [
                            (surviving[j].0, links[j].3.as_ref()),
                            (surviving[j].1, links[j].4.as_ref()),
                        ] {
                            if !ok {
                                continue;
                            }
                            let t = arm.unwrap();
                            for cand in [&min_p, &max_p, &min_n, &max_n].into_iter().flatten() {
                                let c = t.compose(cand);
                                if !c.0 {
                                    upd_min(&mut np_lo, c.clone());
                                    upd_max(&mut np_hi, c);
                                } else {
                                    upd_min(&mut nn_lo, c.clone());
                                    upd_max(&mut nn_hi, c);
                                }
                            }
                        }
                        min_p = np_lo;
                        max_p = np_hi;
                        min_n = nn_lo;
                        max_n = nn_hi;
                    }
                    let mut found_fail = [&min_p, &max_p, &min_n, &max_n]
                        .into_iter()
                        .flatten()
                        .any(&tag_hits);
                    if !found_fail {
                        let mut suf = vec![ValTag::id(); n + 1];
                        for j in (0..n).rev() {
                            let base = if surviving[j].0 {
                                links[j].3.as_ref().unwrap()
                            } else {
                                links[j].4.as_ref().unwrap()
                            };
                            suf[j] = suf[j + 1].compose(base);
                        }
                        found_fail = tag_hits(&suf[0]);
                        let mut pref = ValTag::id();
                        for j in 0..n {
                            if found_fail {
                                break;
                            }
                            let base = if surviving[j].0 {
                                links[j].3.as_ref().unwrap()
                            } else {
                                links[j].4.as_ref().unwrap()
                            };
                            if surviving[j].0 && surviving[j].1 {
                                let alt = links[j].4.as_ref().unwrap();
                                if tag_hits(&suf[j + 1].compose(alt).compose(&pref)) {
                                    found_fail = true;
                                    break;
                                }
                            }
                            pref = base.compose(&pref);
                        }
                    }
                    // Check 4: Greedy backward witness from excl endpoints inside hull[n].
                    if !found_fail && let Some((el, eh)) = &excl {
                        let t_lo = el.clone().max(f_bounds[n].0.clone());
                        let t_hi = eh.clone().min(f_bounds[n].1.clone());
                        if t_lo <= t_hi {
                            for target in [t_lo, t_hi] {
                                if !matches!(target, Fin(_)) {
                                    continue;
                                }
                                let mut cur = target;
                                let mut ok = true;
                                for j in (0..n).rev() {
                                    let (hl, hh) = &f_bounds[j];
                                    let mut picked = None;
                                    for (s_ok, arm) in [
                                        (surviving[j].0, links[j].3.as_ref()),
                                        (surviving[j].1, links[j].4.as_ref()),
                                    ] {
                                        if !s_ok {
                                            continue;
                                        }
                                        let pre = arm.unwrap().inverse().map_end(&cur);
                                        if &pre >= hl && &pre <= hh {
                                            picked = Some(pre);
                                            break;
                                        }
                                    }
                                    if let Some(pre) = picked {
                                        cur = pre;
                                    } else {
                                        ok = false;
                                        break;
                                    }
                                }
                                if ok && proj_z.contains_end(&cur) {
                                    found_fail = true;
                                    break;
                                }
                            }
                        }
                    }
                    if found_fail {
                        false
                    } else {
                        // No check decided (coNP-hard in general, the doc above): main's path
                        // answers.
                        return None;
                    }
                }
            }
        };

        let mut out = Res::all();
        out.exact = exact;
        out.vars = VarSet::Many;
        if let Some(z) = base_var
            && proj_z != dom_z
        {
            out.dom.insert(z, Rc::new(proj_z));
        }
        for (j, (gx, m0, m1, _, _)) in links.into_iter().enumerate() {
            let mut keep = IntervalSet::empty();
            if surviving[j].0 {
                keep = keep.join(&m0);
            }
            if surviving[j].1 {
                keep = keep.join(&m1);
            }
            if keep != *self.cx.inputs[&gx] {
                out.dom.insert(gx, Rc::new(keep));
            }
        }
        let rel = if out.exact {
            None
        } else {
            Some(self.relation_within(original, &wanted)?)
        };
        Some((out, rel))
    }
}

/// The linear stage: the relation of the demand over the box `dom`, the box narrowed to its
/// projections and whether the box entails the relation, with the refusal that left the latter
/// undecided, or the refusal that left the projections undecided. `None` when the term
/// is outside the domain or the relation is refused. `doubt` is the transfer's doubted box
/// ([`Res::doubt`]): every point of `dom` outside it meets the demand.
#[allow(clippy::type_complexity)]
fn linear(
    tx: &mut Tx<'_>,
    root: Tid,
    dom: &Domains,
    demand: &Demand,
    doubt: Option<&Sets>,
) -> Option<(Relation, Result<(Domains, bool, Option<Refusal>), Refusal>)> {
    // `start` empties the memo, so every translation entry read below is made with this `tr`
    // (FAIL-ref-memo-stale-entries; `Tx::relation_within`, steps 1 and 2).
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
        bit_ands: Vec::new(),
    };
    let go = || -> Result<(Domains, bool, Option<Refusal>), Refusal> {
        let mut mentioned = rel.body.atoms();
        for (_, _, f) in &rel.defs {
            mentioned.extend(f.atoms());
        }
        let within = |d: &Domains| -> Formula {
            let parts = d
                .iter()
                .map(|(k, v)| presburger::member(&presburger::Atom::Sym(k.clone()), v))
                .collect();
            Formula::and(parts)
        };
        let whole = Formula::and(vec![rel.defined(), within(dom), rel.body.clone()]);
        let syms: Vec<presburger::Atom> = dom
            .keys()
            .map(|k| presburger::Atom::Sym(k.clone()))
            .filter(|a| mentioned.contains(a))
            .collect();
        if let Some(found) = doubt.and_then(|d| pinned_slice(&whole, dom, d, &mentioned)) {
            return Ok(found);
        }
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

/// The linear stage's answer where the doubted box `doubt` fixes every input the relation
/// mentions to one value `p` within `dom`: every point of `dom` outside the slice of `dom` at
/// `p` meets the demand, and whether the slice does is one decision, since the relation reads
/// no other input. `whole` is the relation met with `dom`. `None` when the box fixes no such
/// slice or the decision is refused, or when the slice fails and more than one mentioned
/// input takes other values in `dom`, for the general path.
///
/// Complexity tradeoff: naive version: the projection of the relation onto each input
/// ([`presburger::project_each`]) and the decision of its complement, which on a chain of n
/// nested `c - x` under guards that read one input is superlinear in the solver (measured
/// 178 ms and 3.3 s at 64 and 512 levels). Used: the slice is one point of the mentioned
/// inputs, so the relation met with it fixes every input and, through the definitions,
/// every auxiliary variable, and one decision answers, measured linear in n; the answer is
/// the exact preimage: `dom`, or `dom` less the slice when the slice fails, a box when every
/// mentioned input but one is fixed by `dom` too. Test
/// `l01_25_preimage_catalog::s22::constant_guarded_chains_scale`; COMPLEXITY.md row C48.
/// Given up: a doubted box that holds more than one value of a mentioned input, and a failing
/// slice with two inputs left free, take the general path, which costs what it did.
fn pinned_slice(
    whole: &Formula,
    dom: &Domains,
    doubt: &Sets,
    mentioned: &BTreeSet<presburger::Atom>,
) -> Option<(Domains, bool, Option<Refusal>)> {
    let mut p = Vec::new();
    for (k, v) in dom {
        if !mentioned.contains(&presburger::Atom::Sym(k.clone())) {
            continue;
        }
        let at = doubt.get(k).map_or_else(|| v.clone(), |d| d.meet(v));
        if !is_point(&at) {
            return None;
        }
        p.push((k, at));
    }
    // A name the relation mentions that is not an input leaves the slice more than a point.
    let syms = mentioned
        .iter()
        .filter(|a| matches!(a, presburger::Atom::Sym(_)))
        .count();
    if syms != p.len() {
        return None;
    }
    let slice = p
        .iter()
        .map(|(k, v)| presburger::member(&presburger::Atom::Sym((*k).clone()), v))
        .chain([whole.clone()])
        .collect();
    if presburger::decide(&Formula::and(slice)).ok()? {
        return Some((dom.clone(), true, None));
    }
    // The slice fails: the preimage is `dom` less the slice, whose projection onto an input
    // loses the input's value at `p` only where every other mentioned input is fixed by
    // `dom` to its value at `p`.
    let loose: Vec<&(&Arc<str>, IntervalSet)> = p.iter().filter(|(k, v)| dom[*k] != *v).collect();
    match loose[..] {
        [] => {
            let none = dom.keys().map(|k| (k.clone(), IntervalSet::empty()));
            Some((none.collect(), true, None))
        }
        [(k, v)] => {
            let mut out = dom.clone();
            out.insert((*k).clone(), dom[*k].minus(v));
            Some((out, true, None))
        }
        // `dom` less the slice is not a box; the general path projects it.
        _ => None,
    }
}

/// The translation of terms into the linear-relation domain: the definitions of the auxiliary
/// variables made so far.
struct Tr {
    defs: Vec<(u32, String, Formula)>,
    products: bool,
}

impl Tr {
    fn aux(&mut self, what: String, def: Formula) -> presburger::Atom {
        let n = to_u32(self.defs.len(), "definitions");
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

/// The revision table's operator for a primitive, with the constant exponent of `^`.
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
        Prim::Pow => Op::Pow(exponent?.into()),
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
    ints: Vec<Num>,
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

/// How many distinct inputs a subterm narrows or reads along live paths.
#[derive(Clone, Default, PartialEq, Eq)]
enum VarSet<K = Arc<str>> {
    #[default]
    Zero,
    One(K),
    Many,
}

impl<K: Clone + PartialEq> VarSet<K> {
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (VarSet::Zero, x) | (x, VarSet::Zero) => x.clone(),
            (VarSet::One(a), VarSet::One(b)) if a == b => VarSet::One(a.clone()),
            _ => VarSet::Many,
        }
    }
}

/// A result of the transfer: the box, by the inputs it narrows, so that a result takes the
/// space of what the term reads and not of every enclosing parameter. A name not in `dom` has
/// the whole of its domain.
#[derive(Clone)]
struct Res {
    dom: Sets,
    /// Whether the box holds no point.
    none: bool,
    exact: bool,
    /// When the box is not exact: `Some(d)` when every point of the box outside the box `d`
    /// meets the demand (and avoids the doubted values, [`Tx::back_doubt`]), `None` when no
    /// such box is known. Only the reflection of `c - x` leaves such points, which an
    /// enclosing guard may remove ([`Tx::meet`]).
    doubt: Option<Sets>,
    /// The inputs narrowed or read along live paths.
    vars: VarSet,
}

impl Res {
    fn all() -> Res {
        Res {
            dom: Sets::new(),
            none: false,
            exact: true,
            doubt: None,
            vars: VarSet::Zero,
        }
    }

    /// Marks the box not exact, with no box known to hold the points that fail.
    fn inexact(&mut self) {
        self.exact = false;
        self.doubt = None;
    }

    /// The box outside which every point meets the demand: `Some(None)` when that is every
    /// point, `Some(Some(d))` for `d`, `None` when no such box is known.
    fn doubted(&self) -> Option<Option<&Sets>> {
        if self.exact {
            Some(None)
        } else {
            self.doubt.as_ref().map(Some)
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
            vars: VarSet::Many,
            ..Res::all()
        }
    }
}

/// A unit-slope bijection `v -> (if self.0 { -v } else { v }) + self.1` on integer values.
#[derive(Clone)]
struct ValTag(bool, Num);

impl ValTag {
    fn id() -> Self {
        Self(false, Num::ZERO)
    }
    fn is_id(&self) -> bool {
        !self.0 && self.1.is_zero()
    }
    fn shift(delta: i128) -> Self {
        Self(false, Num::from(delta))
    }
    fn neg() -> Self {
        Self(true, Num::ZERO)
    }
    fn reflect(c: i128) -> Self {
        Self(true, Num::from(c))
    }
    fn compose(&self, inner: &Self) -> Self {
        let add = if self.0 {
            &self.1 - &inner.1
        } else {
            &self.1 + &inner.1
        };
        Self(self.0 ^ inner.0, add)
    }
    /// The inverse under [`ValTag::compose`]: `v -> -v + k` is its own inverse, and the
    /// inverse of `v -> v + k` is `v -> v - k`.
    fn inverse(&self) -> Self {
        if self.0 {
            self.clone()
        } else {
            Self(false, -&self.1)
        }
    }
    fn map_end(&self, e: &End) -> End {
        match (self.0, e) {
            (false, Fin(v)) => Fin(v + &self.1),
            (true, Fin(v)) => Fin(&self.1 - v),
            (false, e) => e.clone(),
            (true, NegInf) => PosInf,
            (true, PosInf) => NegInf,
        }
    }
    fn map_range(&self, lo: &End, hi: &End) -> (End, End) {
        if self.0 {
            (self.map_end(hi), self.map_end(lo))
        } else {
            (self.map_end(lo), self.map_end(hi))
        }
    }
    fn map_set(&self, z: &IntervalSet) -> IntervalSet {
        if self.is_id() {
            return z.clone();
        }
        let pieces: Vec<_> = if self.0 {
            z.pieces()
                .rev()
                .map(|(l, h)| self.map_range(l, h))
                .collect()
        } else {
            z.pieces().map(|(l, h)| self.map_range(l, h)).collect()
        };
        IntervalSet::from_pieces(pieces)
    }
}

/// Demand-independent structure of a single-input integer subterm ([`Tx::step_1d`]).
#[derive(Clone)]
struct Step1d {
    var: VarSet,
    guard: VarSet<Coordinate>,
    fwd: IntervalSet,
    kind: StepKind,
}

type HighImage = Option<(End, IntervalSet)>;
type ArmMask = Option<(Rc<IntervalSet>, Rc<IntervalSet>)>;
type BranchArm = Option<(At, ArmMask)>;

#[derive(Clone)]
enum StepKind {
    Round(i64, At),
    Leaf,
    Const(Value),
    Input,
    Forward(At),
    If(BranchArm, BranchArm),
    Shift(i128, At),
    Reflect(i64, At),
    Neg(At),
    Abs(At),
    MinMax(Prim, i64, At),
    Mul(i64, At),
    Div(i64, At),
    Mod(i64, IntervalSet, At),
    Pow(Num, IntervalSet, At),
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
    factors: HashMap<At, (Tid, Eid, Num)>,
    mentions: HashMap<At, Option<bool>>,
    constant: HashMap<At, Option<Value>>,
    fwd: HashMap<At, Fwd>,
    /// By term, scope and demand ([`Tx::back_at`]).
    back_at: HashMap<(At, Demand), Res>,
    /// Single-input integer subterm structure ([`Tx::step_1d`]).
    step_1d: HashMap<At, Option<Step1d>>,
    high_image: HashMap<(At, Arc<str>), HighImage>,
    /// By term, scope, demand and doubted values ([`Tx::back_doubt`]).
    back: HashMap<(At, Demand, IntervalSet), Res>,
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
        let ends = |s: &IntervalSet| -> Vec<Num> {
            s.pieces()
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
    // Proof (proofs audit, proofdoc4b). A `true` means the two terms are equal part by part:
    // every pair popped either is one number (one term, since a number stands for one term,
    // [`Terms`]), was seen before (skipping it is safe, since a pair that differs returns
    // `false` when it is first compared and ends the search), or matches one arm, whose kind,
    // name, literal, primitive and arity agree and whose parts are pushed. Literals agree only
    // when of one kind and one value, two floats bitwise (zed-kernel value.rs `number_eq`), so
    // `0.0` and `-0.0` differ. Names agree by their number, and a `Let` or `Lam` binds the same
    // names in both, so two equal terms read in one environment read the same bindings. Any
    // other pair of kinds, a `Follow` among them, gives `false`, which only loses a match. An
    // `Other` pair is compared by its given terms (`src`, `Some` for every number `add` makes;
    // a made term is never `Other`), by `Term`'s `==`, which reads the whole of both, so that
    // pair is looked into in full, corrected from "not looked into" for those parts.
    // "Each pair once": `seen` admits a pair once, and each admitted pair pushes its parts'
    // pairs once, so the work is O(the pairs reached), at most the product of the two terms'
    // part counts, and the term is a DAG, so the search ends. Caller:
    // `independent_reflections` (`c - plain` against `plain`).
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
            // Naive version: the call read again at each depth it may reach, which need not
            // end; used: the stop, O(1) at the call cycle, the inputs keeping their forward
            // intervals.
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
        let next = to_u32(self.run.sums.len(), "sums");
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
                out.vars = out.vars.join(&VarSet::One(k.clone()));
            }
        }
        if !out.exact {
            out.vars = VarSet::Many;
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

    /// Removes every translation entry, for a translation with a new numbering of auxiliary
    /// variables (see [`Tx::relation_within`]).
    fn clear_translations(&mut self) {
        let m = &mut self.run.memo;
        m.lin.clear();
        m.formula.clear();
        m.lin_calls.clear();
        m.formula_calls.clear();
        m.log.clear();
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
    ///
    /// Where both sides are exact but for the points of their doubted boxes ([`Res::doubt`]),
    /// the meet is exact but for those points that lie in it: a doubted box the other side
    /// (an enclosing guard's box among them) leaves empty is dropped, and with none left the
    /// meet is exact.
    fn meet(&self, a: Res, b: Res) -> Res {
        if self.empty(&a) || self.empty(&b) {
            return Res::none();
        }
        let doubts = match (a.doubted(), b.doubted()) {
            (Some(x), Some(y)) => Some([x.cloned(), y.cloned()]),
            _ => None,
        };
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
        let (exact, doubt) = match doubts {
            None => (false, None),
            Some(ds) => {
                let left = ds
                    .into_iter()
                    .flatten()
                    .filter_map(|d| self.doubt_in(d, &dom));
                match left.reduce(|x, y| hull(&x, &y)) {
                    None => (true, None),
                    Some(d) => (false, Some(d)),
                }
            }
        };
        let vars = a.vars.join(&b.vars);
        Res {
            dom,
            none: false,
            exact,
            doubt,
            vars,
        }
    }

    /// The doubted box `d` narrowed by the box `dom` in the names `d` narrows, or `None` when
    /// it holds no point of `dom`. A name `dom` alone narrows is left whole in `d`, which is
    /// still a box holding every doubted point; the time is that of `d`'s names.
    fn doubt_in(&self, mut d: Sets, dom: &Sets) -> Option<Sets> {
        if self.run.void {
            return None;
        }
        for (k, v) in &d.clone() {
            if let Some(w) = dom.get(k) {
                let met = v.meet(w);
                if met.is_empty() {
                    return None;
                }
                d.insert(k.clone(), Rc::new(met));
            }
        }
        Some(d)
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
        let vars = a.vars.join(&b.vars);
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
        // A point of a union that is a box lies in one side, so it meets the demand unless it
        // lies in that side's doubted box, which the hull of the two holds.
        let doubt = match (a.doubted(), b.doubted()) {
            (Some(Some(x)), Some(Some(y))) if boxed => Some(hull(x, y)),
            (Some(Some(x)), Some(None)) | (Some(None), Some(Some(x))) if boxed => Some(x.clone()),
            _ => None,
        };
        let exact = a.exact && b.exact && boxed;
        Res {
            dom,
            none: false,
            exact,
            doubt,
            vars,
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
                    Node::App(f, args)
                        if let Node::Lam(ps, body) = s.node(f)
                            && ps.len() == args.len() =>
                    {
                        for i in 0..args.len() {
                            s.constant(s.arg(args, i), env)?;
                        }
                        let inner = s.call_env(ps, args, env, env);
                        s.constant(body, inner)
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
    fn power(&mut self, t: Tid, env: Eid) -> Option<(Tid, Eid, Num)> {
        let (base, be, k) = self.factors(t, env);
        (k > Num::ONE).then_some((base, be, k))
    }

    // Count equal factors on the DAG instead of flattening them into a capped list.
    // Memoization shares repeated squarings and nested products; the count has O(depth)
    // bits even when the expanded product has exponentially many factors. The revision
    // table already accepts an arbitrary Num exponent. This removes the inherited 64
    // factor size switch without turning a multiplication chain into repeated scans.
    fn factors(&mut self, t: Tid, env: Eid) -> (Tid, Eid, Num) {
        self.cached(
            |m| &mut m.factors,
            (t, env),
            |s| {
                match s.node(t) {
                    Node::Var(x) if s.lookup(env, x).is_some() => {
                        let (bt, be) = s.lookup(env, x).unwrap();
                        return s.factors(bt, be);
                    }
                    Node::Prim(Prim::Mul, args) if args.len() == 2 => {
                        let (a, ae, ak) = s.factors(s.arg(args, 0), env);
                        let (b, be, bk) = s.factors(s.arg(args, 1), env);
                        let same = match (s.node(a), s.node(b)) {
                            (Node::Var(x), Node::Var(y)) => x == y,
                            _ => ae == be && s.same(a, b),
                        };
                        if same {
                            return (a, ae, &ak + &bk);
                        }
                    }
                    _ => {}
                }
                (t, env, Num::ONE)
            },
        )
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
                let x = Lin::atom(presburger::Atom::Aux(to_u32(tr.defs.len(), "definitions")));
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
                        // SOUND-div-exact: `c^0` fails where `c` does (DESIGN.md
                        // sec:failure), and a term translates only where it cannot fail, so
                        // the base must translate too: `(-4 div (1 + x))^0` fails at `x == -1`.
                        0 => {
                            arg(self, tr, 0)?;
                            Some(Lin::constant(1))
                        }
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
                        let n = to_u32(tr.defs.len(), "definitions");
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
                        let x =
                            Lin::atom(presburger::Atom::Aux(to_u32(tr.defs.len(), "definitions")));
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
                        match (!matches!(s.node(f), Node::Lam(..)))
                            .then(|| s.summon(ps, body, lam, args, env))
                            .flatten()
                        {
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
            return self.arith(Op::Pow(k.into()), &b, &b, false);
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
                    self.arith(Op::Pow(k.into()), &a, &a, false)
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
            ints: revision::forward(&o, &a.ints, &b.ints),
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
            |m| &mut m.back_at,
            ((t, env), d.clone()),
            |s| s.back_doubt(t, env, d, &IntervalSet::empty()),
        )
    }

    /// The box of the inputs where `t` meets the demand `d`, as [`Tx::back_at`] gives it,
    /// with the doubted values `dd`: values in `d` the enclosing terms do not accept (the
    /// holes of a `c - x`). The box is exact only where no point of it takes a value in `dd`;
    /// where the only points that may are those of a box `D`, the result is not exact and
    /// carries `D` ([`Res::doubt`]), which an enclosing guard may leave empty ([`Tx::meet`]).
    /// The doubted values are kept to those in `d` that `t` may take, so that the memo key
    /// does not hold values that cannot matter.
    ///
    // Complexity tradeoff: the old memo has O(n^2) demands on shared guarded
    // reflection chains. The independent inverse walk visits each reachable node once,
    // merging exact excluded-value constraints in a persistent value-ordered AVL
    // partition. An endpoint sweep handles affine guarded folds, including translation
    // staircases, so the former second input ordering and its conversions are removed.
    // The measured scalar, named-call, multi-input-frontier and common-difference
    // families cost about O(n log n). This is output-sensitive: an explicit staircase
    // selecting n isolated values can require n^2 output pieces.
    //
    // The shapes that keep the old memo, each measured by a family of
    // `l01_25_preimage_catalog::ref_memo` (PROOF-preimage-ref-chain-cost; T(8n)/T(n), the larger
    // of the instruction and byte ratios, load 46 to 68 on 32 cores):
    // - A step with no `StepKind`, in a term that reads one input: `i + i <= j`
    //   (`coef2_guard`) read 14.8 at 16 and 31.1 at 32 on the memo. `x + x` of one variable is
    //   now the product by 2 in `Tx::step_1d_at` (proof there): 7.9 to 8.0 at 16, 32 and 64.
    //   Any other step with no kind (`i * i`, a sum of two different subterms of `i`) still
    //   falls to the memo, with no bound proved.
    // - Guards on two or more inputs: `alternating_2var` (guards on `i` and `m` in turn) read
    //   13.2 at 16, 16.2 at 32 and 25.2 at 64 here; `indep_varying` (one bit input per guard)
    //   20.9 at 6, 12.1 at 12 and 183 at 24. With the guards of `alternating_2var` a point
    //   (i, m) has p failed links on `i` and q on `m`, and t = ±i + C(p, q) on each of the
    //   (n/2)^2 cells; a method that visits each cell is quadratic. A two-input threshold chain
    //   no longer reaches this memo: `Tx::affine_threshold_pair` answers it in O(n log n)
    //   (Theorem 1 at `threshold_box`), timed by `alternating_2var_scales` and
    //   `alt2var_m_scales`. Nor does a chain of guards on distinct inputs: `indep_varying`
    //   is answered by `Tx::independent_affine` in O(n), 7.99 at 24 (`indep_varying_scales`),
    //   or, when no check decides its exactness (coNP-hard, proof there), comes here.
    // - Nested remainders: in a term that reads one input they are settled by
    //   `State1d::modulo_bounded` (the `nested_moduli_*` families, cost in the header). Under
    //   guards on two inputs `alternating_moduli` read 12.1 at 4 and 101 at 8 on this memo; a
    //   two-input chain of links `c ± (t mod M)` no longer reaches it: `Tx::mod_chain_pair`
    //   answers it in O(K n (log n + k)) (proof in `preimage_ref/mod_chain.rs`), 7.88 at 64
    //   (`alternating_moduli_scales`), and 8.33 with moduli near 2^40 and 2^62
    //   (PERF-ref-memo-moduli-tables).
    // - Products and quotients that do not map pieces one to one (`State1d::inverse` for
    //   |c| > 1, a quotient by c < -1) visit every piece of the state: `normal_mul3_chain` read
    //   8.05 at 16 and `normal_div_neg2_chain` 11.8 at 16 and 8.3 at 128. Measured only: no
    //   bound on the pieces visited per link is proved.
    // Every family is timed (`ref_memo::UNTIMED_FAMILIES` is empty); the answers are checked
    // against the interpreter. Tests: `l01_25_preimage_catalog::ref_memo`
    // (the scaling of each family, main's changed answers, calls 22, 45 and 86). COMPLEXITY.md C56.
    fn back_doubt(&mut self, t: Tid, env: Eid, d: &Demand, dd: &IntervalSet) -> Res {
        let dd = match d {
            Demand::Ints(z) if !dd.is_empty() => dd.meet(z).meet(&self.fwd(t, env).ints),
            _ => IntervalSet::empty(),
        };
        let key = ((t, env), d.clone(), dd.clone());
        if let Some(r) = self.run.memo.back.get(&key) {
            return r.clone();
        }
        if let Demand::Ints(z) = d {
            if z.is_empty() {
                return Res::none();
            }
            if dd.is_empty()
                && let Some(s1d) = self.step_1d(t, env)
                && !matches!(s1d.kind, StepKind::Leaf)
                && let VarSet::One(Coordinate::Input(x)) = if s1d.guard == VarSet::Zero {
                    s1d.var.coordinates()
                } else {
                    s1d.guard
                }
            {
                return self.cached(|m| &mut m.back, key, |s| s.solve_1d((t, env), &x, z));
            }
        }
        self.cached(|m| &mut m.back, key, |s| s.back_in(t, env, d, &dd))
    }

    fn back_in(&mut self, t: Tid, env: Eid, d: &Demand, dd: &IntervalSet) -> Res {
        if let Demand::Ints(z) = d
            && z.is_empty()
        {
            return Res::none();
        }
        // A term that reads no input is decided by running it: its value in `dd` (which is
        // then its one value) meets the demand at no point of the box.
        if !matches!(self.node(t), Node::Var(_))
            && let Some(v) = self.constant(t, env)
        {
            return match d.holds(&v) {
                true if dd.is_empty() => Res::all(),
                true => Res::unknown(),
                false => Res::none(),
            };
        }
        let holds = |v: &Value| if d.holds(v) { Res::all() } else { Res::none() };
        match self.node(t) {
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => self.back_doubt(bt, be, d, dd),
                None => {
                    let x = self.name(x);
                    match (self.cx.inputs.get(x), d) {
                        (Some(dom), Demand::Ints(z)) => {
                            let met = dom.meet(z);
                            if met.is_empty() {
                                return Res::none();
                            }
                            let bad = met.meet(dd);
                            let mut r = Res::all();
                            r.vars = VarSet::One(x.clone());
                            if met != **dom {
                                r.dom.insert(x.clone(), Rc::new(met));
                            }
                            if !bad.is_empty() {
                                r.exact = false;
                                r.doubt = Some(Sets::unit(x.clone(), Rc::new(bad)));
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
                self.back_doubt(b, inner, d, dd)
            }
            Node::If(g, a, b) => {
                // An arm no input takes is not read, so its stops are not reported (DESIGN
                // L1.25, DOC-preimage-dead-arm-stops); proof at the same arm of
                // `preimage::Walk::back`.
                let gt = self.back_at(g, env, &Demand::Bool(true));
                let at = if self.empty(&gt) {
                    Res::none()
                } else {
                    self.back_doubt(a, env, d, dd)
                };
                let gf = self.back_at(g, env, &Demand::Bool(false));
                let bf = if self.empty(&gf) {
                    Res::none()
                } else {
                    self.back_doubt(b, env, d, dd)
                };
                let yes = self.meet(gt, at);
                let no = self.meet(gf, bf);
                self.union(yes, no)
            }
            Node::App(f, args) => match self.callee(f, env) {
                Ok(Callee::Lam(ps, body, lam)) if ps.len() == args.len() => {
                    self.through(t, body, Res::unknown(), |s, place| {
                        match (!matches!(s.node(f), Node::Lam(..)))
                            .then(|| s.summon(ps, body, lam, args, env))
                            .flatten()
                        {
                            // A summary is kept by demand alone; the doubted values are not
                            // followed into it.
                            Some(call) => {
                                let mut r = s.call_back(call, body, lam, args, env, d, place);
                                if !dd.is_empty() {
                                    r.inexact();
                                }
                                r
                            }
                            None => {
                                let inner = s.call_env(ps, args, lam, env);
                                s.back_doubt(body, inner, d, dd)
                            }
                        }
                    })
                }
                Ok(Callee::Prim(p)) => {
                    let c = self.terms.call(t, p, args);
                    self.back_doubt(c, env, d, dd)
                }
                Err(Some(name)) => self.stop(StopKind::Foreign(name), t),
                _ => self.stop(StopKind::Outside, t),
            },
            Node::Prim(p, args) => {
                if p.arity().is_some_and(|n| n != args.len()) {
                    return self.stop(StopKind::Outside, t);
                }
                self.back_prim(t, p, args, env, d, dd)
            }
            _ => self.stop(StopKind::Outside, t),
        }
    }

    fn back_prim(
        &mut self,
        t: Tid,
        p: Prim,
        args: Span,
        env: Eid,
        d: &Demand,
        dd: &IntervalSet,
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
                    if !strict {
                        r.inexact();
                    }
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
                Some(z) => self.back_arith(t, p, args, env, &z, dd),
                None => Res::none(),
            },
            Min | Max => match ints_of(d) {
                Some(z) => self.back_arith(t, p, args, env, &z, dd),
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
                        match (!matches!(s.node(f), Node::Lam(..)))
                            .then(|| s.summon(ps, body, lam, args, env))
                            .flatten()
                        {
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

    /// The arithmetic `t` in `z`, with the doubted values `dd` ([`Tx::back_doubt`]) moved to
    /// the operand by the same inverse as `z` where the catalog inverts the operator.
    fn back_arith(
        &mut self,
        t: Tid,
        p: Prim,
        args: Span,
        env: Eid,
        z: &IntervalSet,
        dd: &IntervalSet,
    ) -> Res {
        use Prim::*;
        let ints = |s: IntervalSet| Demand::Ints(s);
        if p == Mul
            && let Some((base, be, k)) = self.power(t, env)
        {
            return self.back_unary(Op::Pow(k.into()), base, be, z, dd);
        }
        let a = self.arg(args, 0);
        match p {
            Neg | Abs => {
                return self.back_unary(op(p, None).expect("scalar"), a, env, z, dd);
            }
            Pow => {
                let b = self.arg(args, 1);
                return match self.constant_int(b, env).map(u32::try_from) {
                    Some(Ok(k)) => self.back_unary(Op::Pow(k.into()), a, env, z, dd),
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
            (Add, Some(c), _) => {
                let c = -(c as i128);
                self.back_doubt(b, env, &ints(shift(z, c)), &shift(dd, c))
            }
            (Add, _, Some(c)) | (Sub, _, Some(c)) => {
                let c = if p == Add { -(c as i128) } else { c as i128 };
                self.back_doubt(a, env, &ints(shift(z, c)), &shift(dd, c))
            }
            (Sub, Some(c), _) => {
                // The forward image `r` of `{c} - z` caps the pieces of each sign region
                // (`revision::map2`), so it may merge pieces it moves across zero and hold values
                // `v` whose `c - v` is outside `z`: the holes, `r` less the reflection of `z`. The
                // box is that of `b` in `r`, which holds every input whose `c - b` lies in `z`; it
                // is exact only where no input in it has `b` in the holes (item
                // S22-exact-mislabel: the transfer marked such boxes exact whether or not one
                // did). So the holes are doubted values of `b`, with the reflection of the values
                // doubted here: an input with `b` in neither has `c - b` in `z` and not doubted.
                //
                // Complexity tradeoff: naive version: decide exactness by the back transfer of
                // the holes at each `c - x` as a demand of its own, met with the box of each
                // enclosing guard; in a chain of n nested `c - x` each level repeats that
                // transfer over everything below it with holes that differ from level to level,
                // O(n^2) terms followed with the memo (negative control, item S22-guard-exact:
                // 9.4 and 511 ms at 32 and 256 levels, 55 times). Used: on subterms reading two
                // or more inputs ([`Tx::back_in`]), the holes are carried down as one set of
                // doubted values with the demand ([`Tx::back_doubt`]), joined with the reflection
                // of those doubted above, and met with the guards' boxes once at the inputs
                // (`COMPLEXITY.md` row C43); on single-input subterms ([`Tx::solve_1d`]), the
                // reachable DAG is solved in one pass in a 1D partition state so cycling
                // reflections (`c = j mod 5`) do not multiply memo keys (`COMPLEXITY.md` row
                // C56, tests `l01_25_preimage_catalog::s22::guarded_holes_scale` and
                // `l01_25_preimage_catalog::ref_memo`). Given up:
                // the doubted values are not followed into a summarized call, a projection of two
                // operands that read inputs, `min` or `max` of two such operands, or a `mod`
                // whose inverse merges periods; there the box is reported not exact. On
                // multi-input chains a doubted box is the box hull of the doubted points, and
                // cycling reflections across shared multi-input branches remain O(n^2).
                let r = revision::forward(&Op::Sub, &IntervalSet::single(c), z);
                let holes = r.minus(&reflect(z, c as i128));
                let doubted = holes.join(&reflect(dd, c as i128));
                self.back_doubt(b, env, &ints(r), &doubted)
            }
            (Mul, Some(c), _) => self.back_doubt(b, env, &ints(times_pre(z, c)), &times_pre(dd, c)),
            (Mul, _, Some(c)) => self.back_doubt(a, env, &ints(times_pre(z, c)), &times_pre(dd, c)),
            (IntDiv, _, Some(c)) => self.back_doubt(a, env, &ints(div_pre(z, c)), &div_pre(dd, c)),
            (Mod, _, Some(c)) => {
                let fa = self.fwd(a, env).ints;
                let (s, exact) = mod_pre(z, c, &fa);
                let mut r = self.back_doubt(a, env, &ints(s), &mod_pre(dd, c, &fa).0);
                if !exact {
                    r.inexact();
                }
                r
            }
            (Min | Max, Some(c), _) => {
                let (s, ds) = (minmax_pre(p, z, c), minmax_pre(p, dd, c));
                self.back_doubt(b, env, &ints(s), &ds)
            }
            (Min | Max, _, Some(c)) => {
                let (s, ds) = (minmax_pre(p, z, c), minmax_pre(p, dd, c));
                self.back_doubt(a, env, &ints(s), &ds)
            }
            (Min | Max, None, None) if !dd.is_empty() => {
                // The doubted values are not followed into two operands.
                let mut r = self.back_arith(t, p, args, env, z, &IntervalSet::empty());
                r.inexact();
                r
            }
            (Min | Max, None, None) => {
                let f = self.fwd(t, env).ints;
                let zf = z.meet(&f);
                let (Some((flo, fhi)), Some((lo, hi))) = (f.bounds(), zf.bounds()) else {
                    return Res::none();
                };
                let up = IntervalSet::range(lo.clone(), fhi.clone()).is_subset(z);
                let down = IntervalSet::range(flo.clone(), hi.clone()).is_subset(z);
                // min ≥ lo: both are; max ≤ hi: both are. The other rays: either is, where the
                // other operand is an integer, since a failing operand fails the term (DESIGN.md
                // sec:failure). When the demand holds the whole forward range, both rays apply;
                // the upward one is taken.
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
                    if both {
                        return self.meet(ra, rb);
                    }
                    let ra = if self.fwd(b, env).fails {
                        let db = self.back_at(b, env, &ints(IntervalSet::top()));
                        self.meet(ra, db)
                    } else {
                        ra
                    };
                    let rb = if self.fwd(a, env).fails {
                        let da = self.back_at(a, env, &ints(IntervalSet::top()));
                        self.meet(rb, da)
                    } else {
                        rb
                    };
                    return self.union(ra, rb);
                }
                self.project(p, a, b, env, z)
            }
            // A demand holding every value of `a div b` or `a mod b`: the term meets it exactly
            // where it is defined, where `a` and `b` are integers and `b != 0` (the kernel fails
            // a quotient by 0 and no other, `zed_kernel::eval::int_binary`; DESIGN.md
            // sec:failure), exact when both preimages are. A demand holding no value of the term
            // has no input, which is exact too. With doubted values, or a demand holding some
            // values and not others, the projection below answers, not exact.
            // PREIMAGE-mod-defined, as `preimage::Walk::where_defined` (which the reduced
            // product's narrowing does not take; this reference transfer is not used there).
            // Test:
            // `l01_25_preimage_catalog::exact_oracle::a_quotient_read_where_it_is_defined_is_exact`.
            (IntDiv | Mod, _, None)
                if dd.is_empty() && self.fwd(t, env).ints.meet(z).is_empty() =>
            {
                Res::none()
            }
            (IntDiv | Mod, _, None) if dd.is_empty() && self.fwd(t, env).ints.is_subset(z) => {
                let nonzero = IntervalSet::top().minus(&IntervalSet::of(0, 0));
                let ra = self.back_at(a, env, &ints(IntervalSet::top()));
                let rb = self.back_at(b, env, &ints(nonzero));
                self.meet(ra, rb)
            }
            _ => self.project(p, a, b, env, z),
        }
    }

    /// `op(c)` in `z`, for an operator the revision table inverts exactly within the forward
    /// interval of `c`; the doubted values `dd` are moved to `c` by the same inverse, which
    /// holds every value of `c` the operator takes into them.
    fn back_unary(&mut self, o: Op, c: Tid, env: Eid, z: &IntervalSet, dd: &IntervalSet) -> Res {
        if matches!(&o, Op::Pow(k) if k.is_zero()) {
            // `c ^ 0` is 1 wherever `c` is an integer.
            let top = IntervalSet::top();
            let doubted = if dd.contains(1) {
                top.clone()
            } else {
                IntervalSet::empty()
            };
            return if z.contains(1) {
                self.back_doubt(c, env, &Demand::Ints(top), &doubted)
            } else {
                Res::none()
            };
        }
        let fc = self.fwd(c, env).ints;
        let zc = revision::backward(&o, 0, &fc, &fc, z);
        let doubted = if dd.is_empty() {
            IntervalSet::empty()
        } else {
            revision::backward(&o, 0, &fc, &fc, dd)
        };
        self.back_doubt(c, env, &Demand::Ints(zc), &doubted)
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
    fn project(&mut self, p: Prim, a: Tid, b: Tid, env: Eid, z: &IntervalSet) -> Res {
        let o = op(p, None).expect("binary scalar operator");
        let fa = self.fwd(a, env).ints;
        let fb = self.fwd(b, env).ints;
        let za = revision::backward(&o, 0, &fa, &fb, z);
        let zb = revision::backward(&o, 1, &fa, &fb, z);
        let ra = self.back_at(a, env, &Demand::Ints(za));
        let rb = self.back_at(b, env, &Demand::Ints(zb));
        let mut r = self.meet(ra, rb);
        if !self.empty(&r) {
            r.inexact();
        }
        r
    }

    fn both_ints(&mut self, a: Tid, b: Tid, env: Eid) -> Res {
        let top = Demand::Ints(IntervalSet::top());
        let ra = self.back_at(a, env, &top);
        let rb = self.back_at(b, env, &top);
        let mut r = self.meet(ra, rb);
        if !self.empty(&r) {
            r.inexact();
        }
        r
    }

    fn step_1d(&mut self, t: Tid, env: Eid) -> Option<Step1d> {
        (!self.run.void).then(|| {
            self.cached(
                |m| &mut m.step_1d,
                (t, env),
                |s| {
                    s.step_1d_at(t, env).or_else(|| {
                        let fwd = s.fwd(t, env).ints;
                        (!fwd.is_empty()).then(|| {
                            let guard = match s.node(t) {
                                Node::Prim(Prim::Add | Prim::Sub | Prim::Mul, args) => {
                                    let mut guard = VarSet::Zero;
                                    for i in 0..args.len() {
                                        let a = s.arg(args, i);
                                        guard = guard.join(
                                            &s.step_1d(a, env)
                                                .map_or(VarSet::Many, |sub| sub.guard),
                                        );
                                    }
                                    if guard == VarSet::Zero {
                                        guard
                                    } else {
                                        VarSet::Many
                                    }
                                }
                                _ => VarSet::Many,
                            };
                            Step1d {
                                var: VarSet::Many,
                                guard,
                                fwd,
                                kind: StepKind::Leaf,
                            }
                        })
                    })
                },
            )
        })?
    }

    fn step_1d_at(&mut self, t: Tid, env: Eid) -> Option<Step1d> {
        use Prim::*;
        let fwd = self.fwd(t, env).ints;
        let ok = |var, guard, kind| {
            Some(Step1d {
                var,
                guard,
                fwd: fwd.clone(),
                kind,
            })
        };
        if !matches!(self.node(t), Node::Var(_))
            && let Some(v) = self.constant(t, env)
        {
            return ok(VarSet::Zero, VarSet::Zero, StepKind::Const(v));
        }
        match self.node(t) {
            Node::Int(n) => ok(VarSet::Zero, VarSet::Zero, StepKind::Const(Value::Int(n))),
            Node::Bool(b) => ok(VarSet::Zero, VarSet::Zero, StepKind::Const(Value::Bool(b))),
            Node::Lit(v) => ok(VarSet::Zero, VarSet::Zero, StepKind::Const(v.clone())),
            Node::Var(x) => match self.lookup(env, x) {
                Some((bt, be)) => ok(
                    self.step_1d(bt, be)?.var,
                    self.step_1d(bt, be)?.guard,
                    StepKind::Forward((bt, be)),
                ),
                None => {
                    let name = self.name(x).clone();
                    self.cx.inputs.contains_key(&name).then(|| Step1d {
                        var: VarSet::One(name),
                        guard: VarSet::Zero,
                        fwd,
                        kind: StepKind::Input,
                    })
                }
            },
            Node::Let(n, e, b) => {
                let inner = self.let_env(n, e, env);
                ok(
                    self.step_1d(b, inner)?.var,
                    self.step_1d(b, inner)?.guard,
                    StepKind::Forward((b, inner)),
                )
            }
            Node::If(g, a, b) => {
                let (mut guard, yes, no, mut var) =
                    if let Some((coord, yes, no)) = self.difference_guard(g, env) {
                        let vars = match &coord {
                            Coordinate::Input(x) => VarSet::One(x.clone()),
                            Coordinate::Difference(..) => VarSet::Many,
                        };
                        let live = |m: &ArmMask| m.as_ref().is_none_or(|(s, _)| !s.is_empty());
                        (
                            VarSet::One(coord),
                            live(&yes).then_some(((a, env), yes)),
                            live(&no).then_some(((b, env), no)),
                            vars,
                        )
                    } else {
                        let gt = self.back_at(g, env, &Demand::Bool(true));
                        let gf = self.back_at(g, env, &Demand::Bool(false));
                        if !(self.empty(&gt) || gt.exact) || !(self.empty(&gf) || gf.exact) {
                            return None;
                        }
                        let mask = |r: &Res| -> ArmMask {
                            let (k, m) = r.dom.iter().next()?;
                            let dom = &self.cx.inputs[k];
                            let live = m.meet(dom);
                            let cover = bridge_outside(&live, dom);
                            Some((Rc::new(live), Rc::new(cover)))
                        };
                        let vars = gt.vars.join(&gf.vars);
                        (
                            vars.coordinates(),
                            (!self.empty(&gt)).then(|| ((a, env), mask(&gt))),
                            (!self.empty(&gf)).then(|| ((b, env), mask(&gf))),
                            vars,
                        )
                    };
                let (sa, sb) = (self.step_1d(a, env)?, self.step_1d(b, env)?);
                if yes.is_some() {
                    var = var.join(&sa.var);
                    guard = guard.join(&sa.guard)
                }
                if no.is_some() {
                    var = var.join(&sb.var);
                    guard = guard.join(&sb.guard)
                }
                if guard == VarSet::Many {
                    return None;
                }
                ok(var, guard, StepKind::If(yes, no))
            }
            Node::App(f, args) => match self.callee(f, env).ok()? {
                Callee::Lam(ps, body, lam)
                    if ps.len() == args.len()
                        && (matches!(self.node(f), Node::Lam(..))
                            || matches!(self.node(body), Node::Prim(..) | Node::Var(_))) =>
                {
                    if self.run.active.contains_key(&body)
                        || !(0..args.len()).all(|i| self.mentions(self.arg(args, i), env).is_some())
                    {
                        return None;
                    }
                    let inner = self.call_env(ps, args, lam, env);
                    self.run.active.insert(body, self.run.active.len());
                    let sub = self.step_1d(body, inner);
                    self.run.active.remove(&body);
                    let sub = sub?;
                    ok(sub.var, sub.guard, StepKind::Forward((body, inner)))
                }
                Callee::Prim(p) => {
                    let c = self.terms.call(t, p, args);
                    ok(
                        self.step_1d(c, env)?.var,
                        self.step_1d(c, env)?.guard,
                        StepKind::Forward((c, env)),
                    )
                }
                Callee::Lam(..) => None,
            },
            Node::Prim(p, args) if p.arity().is_none_or(|n| n == args.len()) => {
                if p == IntDiv
                    && let Some(c) = self.constant_int(self.arg(args, 1), env)
                    && c != 0
                    && let Node::Prim(Mul, inner) = self.node(self.arg(args, 0))
                    && inner.len() == 2
                {
                    let (a, b) = (self.arg(inner, 0), self.arg(inner, 1));
                    let base = if self.constant_int(a, env) == Some(c) {
                        Some(b)
                    } else if self.constant_int(b, env) == Some(c) {
                        Some(a)
                    } else {
                        None
                    };
                    if let Some(base) = base {
                        let sub = self.step_1d(base, env)?;
                        return ok(sub.var, sub.guard, StepKind::Forward((base, env)));
                    }
                }
                if p == Mul {
                    let (a, b) = (self.arg(args, 0), self.arg(args, 1));
                    let pair = if let Some(c) = self.constant_int(a, env) {
                        Some((c, b))
                    } else {
                        self.constant_int(b, env).map(|c| (c, a))
                    };
                    if let Some((c, q)) = pair
                        && c != 0
                        && let Node::Prim(IntDiv, inner) = self.node(q)
                        && inner.len() == 2
                        && self.constant_int(self.arg(inner, 1), env) == Some(c)
                    {
                        let base = self.arg(inner, 0);
                        let sub = self.step_1d(base, env)?;
                        return ok(sub.var, sub.guard, StepKind::Round(c, (base, env)));
                    }
                }
                if p == Mul
                    && let Some((base, be, k)) = self.power(t, env)
                {
                    let sub = self.step_1d(base, be)?;
                    return ok(sub.var, sub.guard, StepKind::Pow(k, sub.fwd, (base, be)));
                }
                let a = self.arg(args, 0);
                match p {
                    Neg | Abs => {
                        let sub = self.step_1d(a, env)?;
                        let kind = if p == Neg {
                            StepKind::Neg((a, env))
                        } else {
                            StepKind::Abs((a, env))
                        };
                        ok(sub.var, sub.guard, kind)
                    }
                    Pow => {
                        let k = u32::try_from(self.constant_int(self.arg(args, 1), env)?).ok()?;
                        let sub = self.step_1d(a, env)?;
                        ok(
                            sub.var,
                            sub.guard,
                            StepKind::Pow(Num::from(i64::from(k)), sub.fwd, (a, env)),
                        )
                    }
                    Add | Sub | Mul | IntDiv | Mod | Min | Max => {
                        let b = self.arg(args, 1);
                        let (ca, cb) = (self.constant_int(a, env), self.constant_int(b, env));
                        let (child, kind) = match (p, ca, cb) {
                            (Add, Some(c), _) => {
                                ((b, env), StepKind::Shift(-(c as i128), (b, env)))
                            }
                            (Add, _, Some(c)) => {
                                ((a, env), StepKind::Shift(-(c as i128), (a, env)))
                            }
                            (Sub, _, Some(c)) => ((a, env), StepKind::Shift(c as i128, (a, env))),
                            (Sub, Some(c), _) => ((b, env), StepKind::Reflect(c, (b, env))),
                            (Mul, Some(c), _) => ((b, env), StepKind::Mul(c, (b, env))),
                            (Mul, _, Some(c)) => ((a, env), StepKind::Mul(c, (a, env))),
                            (IntDiv, _, Some(c)) => ((a, env), StepKind::Div(c, (a, env))),
                            (Mod, _, Some(c)) => {
                                ((a, env), StepKind::Mod(c, self.fwd(a, env).ints, (a, env)))
                            }
                            (Min | Max, Some(c), _) => ((b, env), StepKind::MinMax(p, c, (b, env))),
                            (Min | Max, _, Some(c)) => ((a, env), StepKind::MinMax(p, c, (a, env))),
                            // `x + x` with both arguments one variable read in one environment
                            // (PROOF-preimage-ref-chain-cost, family `coef2_guard`): the two
                            // reads are the same value v, and v + v = 2 v for every integer v, so
                            // the step is the product by 2, whose inverse in the one-input state
                            // is exact. Without this arm the sum has no step, the guard
                            // `i + i <= j` gets an inexact box, and the whole chain fell back to
                            // the memo of `Tx::back_doubt`: 14.8 times the instructions from 16
                            // to 128 links and 31.1 from 32 to 256 (load 59.9 and 67.5). Only
                            // variables are compared: equal larger subterms would need a walk of
                            // both at every sum (O(size) each), and no family has one. Test:
                            // `ref_memo::every_family_the_benchmarks_time_is_answered_soundly_at_small_sizes`
                            // (answers checked against the interpreter) and the bench
                            // `coef2_guard_scales`.
                            (Add, None, None)
                                if matches!(
                                    (self.node(a), self.node(b)),
                                    (Node::Var(x), Node::Var(y)) if x == y
                                ) =>
                            {
                                ((a, env), StepKind::Mul(2, (a, env)))
                            }
                            _ => return None,
                        };
                        ok(
                            self.step_1d(child.0, child.1)?.var,
                            self.step_1d(child.0, child.1)?.guard,
                            kind,
                        )
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    // Complexity tradeoff: one pass over the DAG in topological order, each node's state a
    // persistent value-ordered AVL tree of excluded values (`PartitionNode`). A rebuilt set of
    // pieces at each step would cost O(p) per step, O(n^2) on a chain of n links; the tree
    // costs O(log p) per step when each operation at a step follows a bounded number of
    // root-to-leaf paths, O(n log n) in all. The join primitives are those of Blelloch,
    // Ferizovic and Sun, "Just join for parallel ordered sets" (SPAA 2016,
    // doi:10.1145/2935764.2935768; the full comment is at the head of zed-kernel
    // `treap_set.rs`): `tree_node` joins
    // trees of heights h1, h2 in O(|h1 - h2| + 1) and keeps the AVL bound, height at most
    // 1.44 log2(p + 2) for p nodes; `tree_restrict` is their split, two paths;
    // `tree_apply` and `tree_push` are O(1).
    //
    // Proof of O(log n) per link on `normal_round_down` (COMPLEXITY.md K124:
    // `t_j = if i <= j { t } else { 6j + 2 - (t / 2) * 2 }`, `i` in [-10^6, 10^6], query
    // `t_n != 0`). The then arm `t` and the copy of `t` in the else arm are two DAG nodes with
    // the same children, so each link has four nodes: A_j (reached through then arms), B_j
    // (reached through the `Round`), a `Reflect` and a `Round` (a probe counted 4n + 1 nodes
    // visited). By induction from the root, before the step at link j:
    //   (1) A_j's tree is one node, key [0, 0], its label in (-inf, j + 1] (an input
    //       i <= j + 1 takes the then arm at every later link, so t_n = t_j, and t_j = 0 is
    //       the one excluded value);
    //   (2) every label in B_j's tree lies in [j + 2, inf) (B_j is reached only through the
    //       else arm of link j + 1), and every key is [2k, 2k + 1] (a preimage of `Round`);
    //   (3) B_j has at most 3 (n - j) + 1 nodes (each link adds one, and each clip of k
    //       pieces cuts at most k - 1 nodes in two).
    // The root is the base: one node [0, 0], its label the whole domain. Step at link j:
    //   `restrict_x` on A_j's one node is O(1). On B_j both masks, i <= j and i > j, find the
    //   root's span outside or inside them by (2): O(1), B_j's then part empty, its else part
    //   B_j itself. A_{j-1} gets A_j's then part, one node, label (-inf, j]: (1) holds at
    //   j - 1. The `Reflect` node gets B_j joined with A_j's else part, one node, label
    //   {j + 1}: one insertion, O(log p). `Reflect` by 6j + 2, even, is a tag, O(1), and maps
    //   [2k, 2k + 1] to [odd, even] and [0, 0] to [6j + 2, 6j + 2]. Each `clip_values` is one
    //   `tree_restrict` per piece of the step's forward image plus a join, O(k log p), and
    //   trims at most 2k nodes. `Round` by 2: a subtree whose bounds (each lo and hi + 1) all
    //   have one residue mod 2 is shifted by a tag in O(1) (`tree_round`); only the node from
    //   [0, 0] and the at most 2k nodes the `Round` node's clip trimmed have bounds of both
    //   residues, so the recursion follows at most 2k + 1 paths, O(k log p), and every key is
    //   again [2k', 2k' + 1]; the labels lie in [j + 1, inf): (2) holds at j - 1.
    // So a link costs O(k log p) with p = O(n), O(n log n) in all, once k and the pieces of a
    // label (met or joined at each node touched) are bounded. Both are, at every n
    // (PROOF-round-down-piece-bound):
    //   (k) Write M = 10^6, X_j = the forward image of t_j, c = 6j + 2. Claim: X_j is one
    //   interval [L_j, H_j] with L_j <= -M and H_j >= M, and H_j >= c + M - 1 for j >= 1.
    //   X_0 = [-M, M]. Step j, with X_{j-1} = [L, H]: `revision::forward` splits an operand
    //   at 0 (`split_signs`), maps each pair of parts by `corners`, and caps each sign region
    //   of the image to `most`, the most pieces either operand has in one region (`map2`),
    //   1 here, before `from_pieces` merges touching pieces. `t / 2`: the parts [L, -1],
    //   [0, 0], [1, H] give pieces ending at -1 or 0, the piece [0, 0], and one starting at 0
    //   or 1, so one region each, merged into one interval [A, B], A <= L / 2 rounded down
    //   or up (A <= -1 as L <= -2), B >= floor(H / 2) >= 1. `* 2`: [A, -1], [0, 0], [1, B]
    //   give [2A, -2], [0, 0], [2, 2B], one per region, not touching: k = 3, the only node
    //   with more than one piece. `c - _` (not the one-piece fast path, the operand having 3):
    //   the pieces [c - 2B, c - 2], [c, c], [c + 2, c - 2A], split at 0, each region capped
    //   to one piece, give the interval [c - 2B, c - 2A]: k = 1. The `If` joins it with
    //   [L, H]. As c - 2A > 0 > L, the union is one interval when c - 2B <= H + 1, and
    //   2B >= H - 1 reduces that to c <= 2H, true as H >= M >= 4 at j = 1 and
    //   H >= 6(j - 1) + 2 + M - 1 >= 3j + 1 after. So X_j = [min(L, c - 2B), max(H,
    //   c - 2A)], and -2A >= -L - 1 >= M - 1 gives H_j >= c + M - 1. A guard that cannot
    //   fail (j >= M) leaves X_j = X_{j-1}. So k <= 3 at every node, k = 3 only at `Round`.
    //   (labels) Each operation of the walk is the exact inverse of its node on the relation
    //   {(value, input)}: `restrict_x` meets labels with the arm's interval of inputs,
    //   `union` joins them, `Reflect` and `Round` move keys only, and `clip_values` drops
    //   values outside the node's forward image, which holds every value the node takes.
    //   So the label of v at a node N is the set of inputs x in [-M, M] that reach N and
    //   whose remaining links map v to 0. At A_j (x <= j + 1, then arms after): {x <= j + 1}
    //   at v = 0, else empty: one piece. At B_j, the `Round` and `Reflect` of link j + 1
    //   (x >= j + 2): the remaining links are f_m(y) = 6m + 2 - 2 floor(y / 2) for
    //   m = j + 1 .. min(x - 1, n), a count fixed by x. From B_j with r = 2 floor(v / 2),
    //   a_1 = 6j + 8 - r, then every value is even and a_2s = r + 6s (s >= 1),
    //   a_2s+1 = 6j + 6s + 8 - r (s >= 0): 0 is met at r = -6s <= -6 or r = 6j + 6s + 8 >= 8,
    //   two disjoint sets, each one-to-one in s. So at most one count m of links ends at
    //   0, and the label is the x with that count: one x for m < n - j, and all of
    //   [n + 1, M] for m = n - j, one piece either way. `Reflect` at value w is B_j's case
    //   one link later with w itself among the counts (count 0 at w = 0; 2 floor(w / 2)
    //   in r's place after), and `Round` at u is `Reflect` at c - u; the same reading gives
    //   one piece. So every label, and every meet or join of two at a node touched (both
    //   labels of one value, whose union is again that value's label), has one piece.
    // Tests: `ref_memo::the_round_down_chain_keeps_three_pieces_and_one_piece_labels` and
    // `bench::ref_memo::normal_round_down_keeps_its_pieces_at_large_sizes` read both maxima
    // (`counts::inverse_most`) at every n to 128 and at 1024, 2048, 4096 and 8192: 3 and 1.
    // Before this proof the bound rested on a probe at n = 16, 128, 1024 and 8192 (p = n, heights
    // 5, 8, 11 and 14, nodes built per step at most 12, 32, 53 and 74, about 5.3 times the height).
    //
    // Proof of O(log n) per link on `normal_min_gap` (COMPLEXITY.md K138,
    // PROOF-min-gap-log-per-link: `t_j = if i <= j { t } else { c_j - min(t, 20) }`,
    // c_j = j mod 5 + 4 in [4, 8], `i` in [-M, M] with M = 10^6, demand `<= -3 or >= 3`). The
    // root's tree is one node, key [-2, 2] (top minus the demand), label [-M, M].
    //   DAG. `Terms::add` numbers a `Shared` child once (`id`) and each argument of a `Prim`
    //   anew (`ids`), so `chain`'s then arm `t` and its copy inside the `Min` are two nodes with
    //   the same children, and link j has four: A_j (then arms), B_j (the copy, under link
    //   j + 1's `Min`), S_j (`c_j - _`, a `Reflect`, the else arm of A_j and B_j) and M_j
    //   (`min(_, 20)`, child B_{j-1}). A_j's parents are A_{j+1} and B_{j+1}; S_j's are A_j and
    //   B_j; M_j's is S_j; B_{j-1}'s is M_j.
    //   Links j >= M. The guard i <= j cannot fail: `difference_guard` gives the else arm an
    //   empty live set, `step_1d_at` drops it, and X_j = X_{j-1}; such a link visits A_j alone,
    //   label [-M, M], O(1). Let m = min(n, M - 1); the links j <= m are those below.
    //   Forward images are one interval each (k = 1): X_j = [-M, H_j] at A_j and B_j with
    //   H_j = max(H_{j-1}, c_j + M), so c_j + M <= H_j <= M + 8 for j >= 1; [-M, 20] at M_j;
    //   [c_j - 20, c_j + M] at S_j.
    // By induction from A_m down, at the step of each node of link j <= m, after its clip
    // (live = cover and inexact empty at every node: `init` sets them so, the masks meet live
    // and cover alike, `union` joins them alike, and there is no `Mod` or `Pow`):
    //   (A) A_j's tree is one node [-2, 2], label [-M, j + 1] ([-M, M] at j = m), and its live
    //       set is [-M, j + 1] ([-M, M] at m). The `If` meets both with i <= j (one-piece sets,
    //       O(1)), giving [-M, j] for A_{j-1}, and with i > j, giving {j + 1} ([m + 1, M] at
    //       j = m) for S_j.
    //   (B) B_j's live set is [j + 2, M] and every label of B_j lies in it (B_j is reached
    //       only through link j + 1's else arm), so the mask i <= j misses the root's `span`
    //       and i > j covers it: O(1). B_j's then part has an empty live set and `push` drops
    //       it, so A_{j-1} gets A_j's then part alone; B_j's else part is B_j itself. S_j's
    //       `union` joins the live sets {j + 1} and [j + 2, M] into one piece [j + 1, M], which
    //       M_j and B_{j-1} keep: (B) holds at j - 1.
    //   (C) B_j has at most 15 nodes, and S_j and M_j too (TEST-min-gap-b-node-bound). Write
    //       K(T) for the values that some key of tree T holds. `tree_node` drops a node whose
    //       label is empty; the other constructor, `tree_raw`, is called by `tree_balance` on
    //       labels of nodes that exist and by `val_from_iter`. Every caller of `val_from_iter`
    //       gives it nonempty labels: `State1d::init` the range [lo, hi] of the root;
    //       `inverse` (the reflection) the label `xs` of a node that exists; `replace_slices`
    //       the range of a slice; `modulo_*` serve `Mod` only. Its values are the pieces of an
    //       `IntervalSet`, each nonempty, and an empty set gives no node. So every key has a
    //       nonempty label; keys are disjoint nonempty integer ranges, so nodes <= |K(T)|. The
    //       operations act on K as on sets: `tree_union`
    //       gives K(a) | K(b) (`ad.join(&data)` and `ad` are nonempty), `tree_restrict` K & [lo,
    //       hi], `tree_restrict_input` a subset of K, the reflection c - K, and `minmax` (Min, 20)
    //       gives (K & (-inf, 19]) | ([20, inf) if 20 in K). Let K_j = K(B_j) after its clip and
    //       W = [-2, 2], A_j's key. S_j unions A_j's else part (K = W) with B_j's, clips to
    //       [c - 20, c + M] and reflects; M_j clips to [-M, 20] and takes `minmax`; B_{j-1} clips
    //       to [-M, H_{j-1}]. With c = c_j: if K_j | W lies in [c - 19, c + M], then 20 is not in
    //       c - (K_j | W), no node [20, inf) is made, and
    //         K_{j-1} = c - (K_j | W).                                                    (*)
    //       Let r = j mod 5, so c_j = r + 4, and let I_r = [d_r - 7, d_r + 7], 15 integers, with
    //       d = (d_0, ..., d_4) = (1, 4, 2, 5, 3): I_0 = [-6, 8], I_1 = [-3, 11], I_2 = [-5, 9],
    //       I_3 = [-2, 12], I_4 = [-4, 10]. Each I_r contains W and lies in [-6, 12], inside
    //       [c - 19, c + M] for every c in [4, 8]. And c_r - d_r = d_{(r-1) mod 5}: 4 - 1 = 3,
    //       5 - 4 = 1, 6 - 2 = 4, 7 - 5 = 2, 8 - 3 = 5; so c_r - I_r = I_{(r-1) mod 5}, as the
    //       reflection keeps the width. Claim K_j in I_{j mod 5}. Base: B_{m-1} starts from S_m,
    //       which holds A_m's else part alone, so K_{m-1} = c_m - W, which lies in
    //       c_m - I_{m mod 5}
    //       = I_{(m-1) mod 5}. Step: if K_j lies in I_r, then K_j | W lies in I_r, (*) applies,
    //       and K_{j-1} lies in c_r - I_r = I_{(r-1) mod 5}. So B_j has at most |I_r| = 15 nodes;
    //       at S_j the tree before the reflection has K_j | W in I_r and after it c - (K_j | W),
    //       and M_j keeps that, so at most 15 there too; A_j has one node. Trees of O(1) nodes and
    //       height. 15 is the least width that works for all five: the centers d_r are forced by
    //       c_r - d_r = d_{r-1} around the cycle of five (d_0 = 2 - d_0), and I_3 must reach
    //       -2 from d_3 = 5. It is also reached: `counts::if_tree_nodes` reads 15 at every n from
    //       11 to 128 and at 1024 (ref_memo::the_min_gap_chain_keeps_b_to_fifteen_nodes,
    //       bench::ref_memo::normal_min_gap_keeps_its_b_nodes_at_1024; both fail at 14). The
    //       earlier bound, 37 nodes from cuts in [-15, 20], also held, but with no node count
    //       behind it.
    //   (D) labels are made only by A's else parts ({k + 1} at link k < m, [m + 1, M] at m),
    //       joined only at S_k, met (shrinking) by the masks and copied by `val_at`. So a label
    //       at B_j is a union of some of {j + 2}, ..., {m} and [m + 1, M], and at S_j or M_j of
    //       some of {j + 1}, ..., {m} and [m + 1, M]: at most m - j + 1 pieces (n / 2 measured).
    // Step costs. `back_doubt` calls `step_1d` on the root first, which fills the memo for
    // every node the walk reaches, so each call in the walk is a lookup and a clone of
    // `Arc`/`Rc` fields, O(1). Each `clip_values` is one `tree_restrict` on a tree of O(1)
    // nodes, labels copied by their `Arc` roots. `Reflect` is a tag, O(1); every node a tag
    // reaches has passed a clip, so its key and the key it was made with lie in [-M, M + 8],
    // and its `lazy` maps one to the other, an offset within 2 (M + 8) (the node [20, inf) that
    // `minmax` makes has `lazy` the identity and is clipped at B_{j-1} before any tag). `minmax`
    // is a `tree_restrict`, a `val_at` and a join of trees on disjoint ranges, O(1), no label
    // work. The one step that grows is the union at S_j of A_j's else part (one node [-2, 2],
    // label {j + 1}) with B_j: whichever path `tree_union` takes (disjoint ranges, no label
    // join; equal keys; the single node as the tree of greater or equal height; or the split
    // around B_j's root), it follows only the subtrees whose range meets [-2, 2], O(1) tree
    // work, and joins label
    // {j + 1} with each label of the at most 5 keys of B_j that meet [-2, 2]. Each such label
    // lies in [j + 2, M], so `IntervalSet::join`'s two `is_subset` tests stop at once (the
    // one-piece fast path, or the first step of the walk) and `union` of one piece with p
    // pieces costs O(log p) time and new nodes (Blelloch, Ferizovic and Sun 2016,
    // doi:10.1145/2935764.2935768, interval.rs `union`). So a link costs O(log n) time and
    // bytes, O(n log n) in all. The leaves (`Input` at A_0 and B_0) run once in `solve_1d`:
    // `eval_diagonal` costs O(n log n) (a seek per node, O(1) nodes by (C), then the sort in
    // `from_pieces` of at most 15 (m + 1) + 1 pieces by (D)). The proof covers
    // `inverse_states` only, as K124 does, not the rest of `preimage_in`.
    // Measured (BENCH-ref-memo-normal-min-gap-bytes): first-run bytes per link rise by 4,065
    // to 4,947 at each doubling from 128 to 8192 and the rise does not grow, as O(log n) path
    // copies of labels predict; the largest label has n / 2 pieces.
    fn inverse_states(
        &mut self,
        root: At,
        dom: &IntervalSet,
        z: &IntervalSet,
    ) -> (Vec<(At, Step1d, State1d)>, bool) {
        let mut order = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = vec![(root, false)];
        while let Some((u, done)) = stack.pop() {
            if done {
                order.push(u);
                continue;
            }
            if !seen.insert(u) {
                continue;
            }
            stack.push((u, true));
            match self.step_1d(u.0, u.1).expect("inverse step").kind {
                StepKind::Const(_) | StepKind::Input | StepKind::Leaf => {}
                StepKind::If(a, b) => {
                    for (c, _) in [a, b].into_iter().flatten() {
                        stack.push((c, false));
                    }
                }
                StepKind::Forward(c)
                | StepKind::Shift(_, c)
                | StepKind::Reflect(_, c)
                | StepKind::Neg(c)
                | StepKind::Abs(c)
                | StepKind::MinMax(_, _, c)
                | StepKind::Mul(_, c)
                | StepKind::Div(_, c)
                | StepKind::Mod(_, _, c)
                | StepKind::Pow(_, _, c)
                | StepKind::Round(_, c) => stack.push((c, false)),
            }
        }
        order.reverse();
        // Physical domain holes are intersected once at the leaves. Covers are exact
        // on that domain, so carrying their hull through exact scalar steps is harmless.
        // Approximate remainder inverses retain the physical live set for their doubt.
        let has_mod = order.iter().any(|u| {
            matches!(
                self.step_1d(u.0, u.1).expect("inverse step").kind,
                StepKind::Mod(..)
            )
        });
        let propagation_dom = if has_mod {
            dom.clone()
        } else {
            dom.bounds().map_or_else(IntervalSet::empty, |(lo, hi)| {
                IntervalSet::range(lo.clone(), hi.clone())
            })
        };
        let mut states = HashMap::from([(
            root,
            State1d::init(&propagation_dom, &IntervalSet::top().minus(z)),
        )]);
        let push = |states: &mut HashMap<At, State1d>, c, next: State1d| {
            if !next.live.is_empty() {
                let next = match states.remove(&c) {
                    Some(old) => old.union(next),
                    None => next,
                };
                states.insert(c, next);
            }
        };
        let mut unbranched = HashSet::from([root]);
        let mut empty_inexact = false;
        let mut leaves = Vec::new();
        for u in order {
            let Some(st) = states.remove(&u).filter(|s| !s.live.is_empty()) else {
                continue;
            };
            let step = self.step_1d(u.0, u.1).expect("inverse step");
            #[cfg(feature = "counts")]
            crate::preimage::counts::note_inverse(0, step.fwd.len());
            // Why the clip drops no input (31b60eac9, the bound of product and quotient demands
            // by their forward image): `step.fwd` is the node's forward image from `Tx::fwd`
            // (`step_1d`), which holds every value the node takes at every input of the domain;
            // that `Tx::fwd` is sound (the forward transfer below "Forward transfer") is a
            // premise here, not shown at this site. An excluded pair (value v, input x) with v
            // outside it names a value no run reaches the node with, so no input's answer
            // reads that pair; dropping it changes no label of a value the node takes.
            // Without the clip, a product with no
            // exact inverse passed on every value but the excluded ones (calls 22, 45 and 86 of
            // main's dump came out coarser). Test:
            // `l01_25_preimage_catalog::ref_memo::calls_22_45_and_86_keep_main_s_answer_or_a_finer_one`
            // and the dump tests `the_changed_answers_of_main_s_dump_are_kept_or_made_finer_*`;
            // they check those calls only, and cannot catch an unsound forward image.
            let st = st.clip_values(&step.fwd);
            #[cfg(feature = "counts")]
            if matches!(step.kind, StepKind::If(..)) {
                crate::preimage::counts::note_if_tree_nodes(|| tree_nodes(&st.excl));
            }
            let top = unbranched.contains(&u);
            let mut child = |c, next| {
                if top {
                    unbranched.insert(c);
                }
                push(&mut states, c, next)
            };
            match step.kind.clone() {
                StepKind::Const(_) | StepKind::Input | StepKind::Leaf => leaves.push((u, step, st)),
                StepKind::If(a, b) => {
                    for (c, mask) in [a, b].into_iter().flatten() {
                        push(&mut states, c, st.restrict_x(&mask));
                    }
                }
                StepKind::Forward(c) => child(c, st),
                StepKind::Shift(k, c) => child(c, st.apply_tag(&ValTag::shift(k))),
                StepKind::Reflect(k, c) => child(c, st.reflect(k)),
                StepKind::Neg(c) => child(c, st.apply_tag(&ValTag::neg())),
                StepKind::Abs(c) => child(c, st.abs()),
                StepKind::MinMax(p, k, c) => child(c, st.minmax(p, k)),
                StepKind::Mul(k, c) => child(c, st.mul(k)),
                StepKind::Div(k, c) => child(c, st.div(k)),
                StepKind::Mod(k, fc, c) => {
                    let (next, inexact) = st.modulo(k, &step.fwd, &fc);
                    empty_inexact |= top && inexact;
                    child(c, next);
                }
                StepKind::Pow(k, fc, c) => child(c, st.pow(k, &step.fwd, &fc)),
                StepKind::Round(k, c) => child(c, st.round(k)),
            }
        }
        (leaves, empty_inexact)
    }
    fn solve_1d(&mut self, root: At, x: &Arc<str>, z: &IntervalSet) -> Res {
        let dom = self.cx.inputs[x].clone();
        if dom.is_empty() || z.is_empty() {
            return Res::none();
        }
        let (leaves, empty_inexact) = self.inverse_states(root, &dom, z);
        let mut out = Res::none();
        for (u, step, st) in leaves {
            let met = match step.kind {
                StepKind::Const(Value::Int(n)) => {
                    Some(st.live.minus(&st.xs_at_value(&Num::from(n))))
                }
                StepKind::Const(Value::Big(b)) => {
                    Some(st.live.minus(&st.xs_at_value(&Num::from(&*b))))
                }
                StepKind::Const(_) => continue,
                StepKind::Input if step.var == VarSet::One(x.clone()) => Some(st.eval_diagonal()),
                _ => None,
            };
            if let Some(met) = met {
                let met = met.meet(&dom);
                if met.is_empty() {
                    continue;
                }
                let mut r = Res::all();
                r.vars = VarSet::One(x.clone());
                if met != *dom {
                    r.dom.insert(x.clone(), Rc::new(met.clone()));
                }
                if !st.inexact.meet(&met).is_empty() {
                    r.inexact();
                }
                out = self.union(out, r);
            } else {
                for (lo, hi, ex) in st.to_slices() {
                    let live = st.live.meet(&IntervalSet::range(lo, hi)).meet(&dom);
                    if live.is_empty() {
                        continue;
                    }
                    let mut mask = Res::all();
                    mask.vars = VarSet::One(x.clone());
                    mask.dom.insert(x.clone(), Rc::new(live.clone()));
                    // A frontier accepts only its attainable forward values minus exclusions.
                    // Complementing in top reintroduces unreachable values, weakening HC4.
                    // One interval-set difference per frontier slice; no extra DAG walk.
                    let b = self.back_at(u.0, u.1, &Demand::Ints(step.fwd.minus(&ex)));
                    let mut r = self.meet(mask, b);
                    if !st.inexact.meet(&live).is_empty() {
                        r.inexact();
                    }
                    out = self.union(out, r);
                }
            }
        }
        if out.none && empty_inexact {
            out.inexact();
        }
        out
    }
}

// ---- Input-labelled inverse intervals -----------------------------------------
type Tree = Option<Arc<PartitionNode>>;
type Slice1d = (End, End, IntervalSet);

type Contents = IntervalSet;

#[derive(Clone)]
struct PartitionNode {
    lo: End,
    hi: End,
    min_lo: End,
    max_hi: End,
    span: (End, End),
    /// The cuts of the subtree, in the node's coordinates: made by [`node_boundaries`] when
    /// `tree_round` first reads them, then kept through tags (`tree_apply`) and scaling
    /// (`tree_division`) like the keys.
    boundaries: OnceCell<Boundaries>,
    height: usize,
    data: Contents,
    lazy: ValTag,
    left: Tree,
    right: Tree,
}
impl PartitionNode {
    fn key(&self) -> (End, End) {
        (self.lo.clone(), self.hi.clone())
    }
}
#[derive(Clone)]
struct Boundaries {
    anchor: Option<Num>,
    step: Num,
}
impl Default for Boundaries {
    fn default() -> Self {
        Self {
            anchor: None,
            step: Num::ZERO,
        }
    }
}
impl Boundaries {
    fn key(lo: &End, hi: &End) -> Self {
        let mut out = Self::default();
        for e in [lo.clone(), hi.succ()] {
            if let Fin(n) = e {
                out = out.join(&Self {
                    anchor: Some(n),
                    step: Num::ZERO,
                });
            }
        }
        out
    }
    fn join(&self, other: &Self) -> Self {
        match (&self.anchor, &other.anchor) {
            (None, _) => other.clone(),
            (_, None) => self.clone(),
            (Some(a), Some(b)) => Self {
                anchor: Some({
                    #[cfg(feature = "counts")]
                    crate::preimage::counts::note_boundary_gcds(2);
                    a.clone()
                }),
                step: self.step.gcd(&other.step).gcd(&(a - b)),
            },
        }
    }
    fn apply(&mut self, tag: &ValTag) {
        if let Some(a) = &self.anchor {
            self.anchor = Some(if tag.0 {
                &(&tag.1 + &Num::ONE) - a
            } else {
                a + &tag.1
            });
        }
    }
}
/// The cuts of the subtree at `n`, in `n`'s coordinates: every finite `lo` and `hi + 1` of its
/// nodes, as an anchor (one of them) and a step (the gcd of their differences). Only
/// `tree_round` reads them, so they are made here on its first read and kept in the node
/// (REF-boundaries-gate); a node built and never rounded takes no gcd. Before, `tree_parts`
/// joined them at every node built, two gcds a node, on chains with no `Round` at all.
///
/// Proof that `tree_round` reads the same answer as with the cuts joined at every build:
/// 1. Both describe the same set of points P: the keys of the subtree, each child's mapped
///    through `n.lazy` (`apply`), since `tree_apply` maps a node's own key at once and its
///    children's only through the tag it composes into `lazy`. Tags are shifts `x + s` and
///    reflections `s + 1 - x`, scaling (`tree_division`) is `x * c`; each maps `lo` and
///    `hi + 1` to the mapped key's `lo` and `hi + 1`, so mapping the cuts maps P.
/// 2. `join` keeps step = gcd of all differences of P, whatever the order and grouping of the
///    joins: gcd(step_a, step_b, a - b) for a in A, b in B is the gcd of the differences
///    within A, within B, and between them (each difference between them is a - b plus a
///    combination of the steps). Shifts and reflections keep every |difference|, and scaling
///    by c multiplies each by c, as `apply` and `tree_division` do to the step.
/// 3. The anchor is some point of P, which may differ between the two orders; `tree_round`
///    reads it only when m divides the step, that is, when all of P is one residue mod m,
///    and then reads only `anchor mod m`, the same for every point of P.
/// 4. A node keeps its cuts once made, and `tree_parts` makes every changed node anew, so a
///    kept value is never that of an older subtree.
///
/// Complexity tradeoff: each node instance computes its cuts at most once, from its children's
/// kept cuts, two gcds and a tag; a node copied by `Arc::make_mut` before the first read
/// computes them in each copy that is read. So `tree_round` costs at most what the joins at
/// every build cost before (each node `tree_parts` built joined them once), and nothing on a
/// chain that never rounds. Recursion is as deep as the AVL height, O(log p). Test:
/// `ref_memo::only_a_chain_with_a_round_takes_gcds_for_the_cuts`, and the answers of every
/// family against main's in `ref_memo::every_family_keeps_main_s_answers_through_the_inverse_tree_changes`.
fn node_boundaries(n: &PartitionNode) -> &Boundaries {
    n.boundaries.get_or_init(|| {
        let mut b = Boundaries::key(&n.lo, &n.hi);
        for c in [&n.left, &n.right].into_iter().flatten() {
            let mut cb = node_boundaries(c).clone();
            cb.apply(&n.lazy);
            b = b.join(&cb);
        }
        b
    })
}
fn ceil_grid(e: &End, m: &Num) -> End {
    match e {
        Fin(n) => {
            let negative = -n;
            let q = -&negative.div_floor(m);
            Fin(&q * m)
        }
        other => other.clone(),
    }
}
fn tree_round(tree: Tree, m: &Num) -> Tree {
    // Reuse uniquely owned nodes; shared branches still copy on write. This
    // preserves the same grid inverse and reduces measured round-down byte R
    // from 9.70 to 9.50 (16..128), without changing the asymptotic traversal.
    let n = tree.as_ref()?;
    let boundaries = node_boundaries(n);
    if boundaries.step.rem_euclid(m).is_zero() {
        let residue = boundaries
            .anchor
            .as_ref()
            .map_or(Num::ZERO, |a| a.rem_euclid(m));
        let shift = (-&residue).rem_euclid(m);
        return tree_apply(tree, &ValTag(false, shift));
    }
    let mut arc = tree?;
    let n = Arc::make_mut(&mut arc);
    let data = n.data.clone();
    let left = tree_round(tree_apply(n.left.take(), &n.lazy), m);
    let right = tree_round(tree_apply(n.right.take(), &n.lazy), m);
    let (lo, hi) = (ceil_grid(&n.lo, m), ceil_grid(&n.hi.succ(), m).pred());
    if lo > hi {
        tree_join(left, right)
    } else if tree_height(&left).abs_diff(tree_height(&right)) <= 1 {
        *n = tree_parts((lo, hi), data, left, right);
        Some(arc)
    } else {
        tree_node((lo, hi), data, left, right)
    }
}
impl State1d {
    fn round(self, c: i64) -> Self {
        let mut st = self;
        st.excl = tree_round(st.excl, &Num::from(c.unsigned_abs() as i128));
        st
    }
}

fn tree_height(t: &Tree) -> usize {
    t.as_ref().map_or(0, |n| n.height)
}
/// The nodes of `t`, O(p) for p nodes; the recursion is as deep as the AVL height, O(log p).
#[cfg(feature = "counts")]
fn tree_nodes(t: &Tree) -> usize {
    t.as_ref()
        .map_or(0, |n| 1 + tree_nodes(&n.left) + tree_nodes(&n.right))
}
// A positive Euclidean quotient has ordered, disjoint inverse intervals. Map the
// existing balanced tree in place structurally instead of collecting it and
// reinserting every interval (linear visits instead of p log p reinsertion work).
// The endpoints follow a=q*c+r, 0<=r<c; no paper or production method is used.
// With ownership reuse, measured normal_div_chain byte R is 8.22 (was 12.03)
// and allocation R 7.79 (was 12.07), at 16..128 links.
fn tree_division(t: Tree, c: &Num) -> Tree {
    let mut arc = t?;
    let n = Arc::make_mut(&mut arc);
    let lower = |e: &End| match e {
        Fin(v) => Fin(v * c),
        e => e.clone(),
    };
    let upper = |e: &End| match e {
        Fin(v) => Fin(&(&(v + &Num::ONE) * c) - &Num::ONE),
        e => e.clone(),
    };
    n.left = tree_division(tree_apply(n.left.take(), &n.lazy), c);
    n.right = tree_division(tree_apply(n.right.take(), &n.lazy), c);
    n.lazy = ValTag::id();
    n.lo = lower(&n.lo);
    n.hi = upper(&n.hi);
    n.min_lo = lower(&n.min_lo);
    n.max_hi = upper(&n.max_hi);
    if let Some(b) = n.boundaries.get_mut() {
        b.anchor = b.anchor.as_ref().map(|a| a * c);
        b.step = &b.step * c;
    }
    Some(arc)
}
fn tree_parts((lo, hi): (End, End), data: Contents, left: Tree, right: Tree) -> PartitionNode {
    #[cfg(feature = "counts")]
    crate::preimage::counts::note_inverse(1, data.len());
    let (xlo, xhi) = data.bounds().expect("nonempty input labels");
    let (mut xlo, mut xhi) = (xlo.clone(), xhi.clone());
    for n in [&left, &right].into_iter().flatten() {
        xlo = xlo.min(n.span.0.clone());
        xhi = xhi.max(n.span.1.clone());
    }
    PartitionNode {
        boundaries: OnceCell::new(),
        min_lo: left
            .as_ref()
            .map_or_else(|| lo.clone(), |n| n.min_lo.clone()),
        max_hi: right
            .as_ref()
            .map_or_else(|| hi.clone(), |n| n.max_hi.clone()),
        lo,
        hi,
        span: (xlo, xhi),
        height: 1 + tree_height(&left).max(tree_height(&right)),
        data,
        lazy: ValTag::id(),
        left,
        right,
    }
}
fn tree_raw(key: (End, End), data: Contents, left: Tree, right: Tree) -> Tree {
    Some(Arc::new(tree_parts(key, data, left, right)))
}
fn tree_apply(tree: Tree, tag: &ValTag) -> Tree {
    if tag.is_id() {
        return tree;
    }
    let mut arc = tree?;
    let n = Arc::make_mut(&mut arc);
    if let Some(b) = n.boundaries.get_mut() {
        b.apply(tag);
    }
    (n.lo, n.hi) = tag.map_range(&n.lo, &n.hi);
    (n.min_lo, n.max_hi) = tag.map_range(&n.min_lo, &n.max_hi);
    if tag.0 {
        std::mem::swap(&mut n.left, &mut n.right);
    }
    n.lazy = tag.compose(&n.lazy);
    Some(arc)
}
fn tree_push(n: &PartitionNode) -> (Contents, Tree, Tree) {
    let data = n.data.clone();
    (
        data,
        tree_apply(n.left.clone(), &n.lazy),
        tree_apply(n.right.clone(), &n.lazy),
    )
}
fn tree_balance(key: (End, End), data: Contents, left: Tree, right: Tree) -> Tree {
    if tree_height(&left) > tree_height(&right) + 1 {
        let l = left.as_ref().unwrap();
        let (ld, ll, lr) = tree_push(l);
        if tree_height(&ll) >= tree_height(&lr) {
            return tree_raw(l.key(), ld, ll, tree_raw(key, data, lr, right));
        }
        let m = lr.as_ref().unwrap();
        let (md, ml, mr) = tree_push(m);
        return tree_raw(
            m.key(),
            md,
            tree_raw(l.key(), ld, ll, ml),
            tree_raw(key, data, mr, right),
        );
    }
    if tree_height(&right) > tree_height(&left) + 1 {
        let r = right.as_ref().unwrap();
        let (rd, rl, rr) = tree_push(r);
        if tree_height(&rr) >= tree_height(&rl) {
            return tree_raw(r.key(), rd, tree_raw(key, data, left, rl), rr);
        }
        let m = rl.as_ref().unwrap();
        let (md, ml, mr) = tree_push(m);
        return tree_raw(
            m.key(),
            md,
            tree_raw(key, data, left, ml),
            tree_raw(r.key(), rd, mr, rr),
        );
    }
    tree_raw(key, data, left, right)
}
fn tree_node(key: (End, End), data: Contents, left: Tree, right: Tree) -> Tree {
    if data.is_empty() {
        return tree_join(left, right);
    }
    if tree_height(&left) > tree_height(&right) + 1 {
        let l = left.as_ref().unwrap();
        let (ld, ll, lr) = tree_push(l);
        return tree_balance(l.key(), ld, ll, tree_node(key, data, lr, right));
    }
    if tree_height(&right) > tree_height(&left) + 1 {
        let r = right.as_ref().unwrap();
        let (rd, rl, rr) = tree_push(r);
        return tree_balance(r.key(), rd, tree_node(key, data, left, rl), rr);
    }
    tree_raw(key, data, left, right)
}
fn tree_single(lo: End, hi: End, data: Contents) -> Tree {
    if lo > hi {
        None
    } else {
        tree_node((lo, hi), data, None, None)
    }
}
fn tree_join(a: Tree, b: Tree) -> Tree {
    match (a, b) {
        (None, t) | (t, None) => t,
        (Some(a), Some(b)) if a.height >= b.height => {
            let (ad, al, ar) = tree_push(&a);
            tree_node(a.key(), ad, al, tree_join(ar, Some(b)))
        }
        (Some(a), Some(b)) => {
            let (bd, bl, br) = tree_push(&b);
            tree_node(b.key(), bd, tree_join(Some(a), bl), br)
        }
    }
}
fn strictly_below(lo: &End) -> Option<(End, End)> {
    (*lo != NegInf).then(|| (NegInf, lo.pred()))
}
fn strictly_above(hi: &End) -> Option<(End, End)> {
    (*hi != PosInf).then(|| (hi.succ(), PosInf))
}
fn tree_restrict(tree: &Tree, lo: &End, hi: &End) -> Tree {
    let n = tree.as_ref()?;
    if lo > hi || hi < &n.min_lo || lo > &n.max_hi {
        return None;
    }
    if lo <= &n.min_lo && &n.max_hi <= hi {
        return tree.clone();
    }
    let (data, left, right) = tree_push(n);
    let l = (lo < &n.lo).then(|| tree_restrict(&left, lo, hi)).flatten();
    let r = (hi > &n.hi)
        .then(|| tree_restrict(&right, lo, hi))
        .flatten();
    if hi < &n.lo || lo > &n.hi {
        return tree_join(l, r);
    }
    tree_node(
        (lo.clone().max(n.lo.clone()), hi.clone().min(n.hi.clone())),
        data,
        l,
        r,
    )
}
fn tree_restrict_set(t: &Tree, s: &IntervalSet) -> Tree {
    s.pieces()
        .fold(None, |out, (l, h)| tree_join(out, tree_restrict(t, l, h)))
}
fn tree_collect(t: &Tree, out: &mut Vec<(End, End, Contents)>) {
    tree_collect_at(t, &ValTag::id(), out)
}
// Read-only in-order walk under a pending tag. Composing the tag on the way down,
// instead of pushing it into copies of shared children (`tree_push`), allocates
// only the output: O(p) time, no node copies. Measured in R3_SEAT.md Q2.
fn tree_collect_at(t: &Tree, tag: &ValTag, out: &mut Vec<(End, End, Contents)>) {
    let Some(n) = t else { return };
    let inner = tag.compose(&n.lazy);
    let (l, r) = if tag.0 {
        (&n.right, &n.left)
    } else {
        (&n.left, &n.right)
    };
    tree_collect_at(l, &inner, out);
    let (lo, hi) = tag.map_range(&n.lo, &n.hi);
    out.push((lo, hi, n.data.clone()));
    tree_collect_at(r, &inner, out);
}
fn tree_union(a: Tree, b: Tree) -> Tree {
    let (a, b) = match (a, b) {
        (None, t) | (t, None) => return t,
        (Some(a), Some(b)) => (a, b),
    };
    if Arc::ptr_eq(&a, &b) {
        return Some(a);
    }
    // Equal cuts need no splitting, temporary interval tree or collection pass.
    // Merge corresponding subtrees directly; this preserves the AVL ordering.
    if a.lo == b.lo && a.hi == b.hi {
        let (ad, al, ar) = tree_push(&a);
        let (bd, bl, br) = tree_push(&b);
        return tree_node(
            a.key(),
            ad.join(&bd),
            tree_union(al, bl),
            tree_union(ar, br),
        );
    }
    if a.max_hi < b.min_lo {
        return tree_join(Some(a), Some(b));
    }
    if b.max_hi < a.min_lo {
        return tree_join(Some(b), Some(a));
    }
    let (a, b) = if a.height >= b.height { (a, b) } else { (b, a) };
    let (ad, al, ar) = tree_push(&a);
    let b = Some(b);
    let bl = strictly_below(&a.lo).and_then(|(l, h)| tree_restrict(&b, &l, &h));
    let br = strictly_above(&a.hi).and_then(|(l, h)| tree_restrict(&b, &l, &h));
    let (nl, nr) = (tree_union(al, bl), tree_union(ar, br));
    let Some(mid) = tree_restrict(&b, &a.lo, &a.hi) else {
        return tree_node(a.key(), ad, nl, nr);
    };
    let mut parts = Vec::new();
    tree_collect(&Some(mid), &mut parts);
    let (mut out, mut cur) = (None, a.lo.clone());
    for (lo, hi, data) in parts {
        if cur < lo {
            out = tree_join(out, tree_single(cur, lo.pred(), ad.clone()));
        }
        out = tree_join(out, tree_single(lo, hi.clone(), ad.join(&data)));
        if hi == PosInf {
            return tree_join(tree_join(nl, out), nr);
        }
        cur = hi.succ();
    }
    if cur <= a.hi {
        out = tree_join(out, tree_single(cur, a.hi.clone(), ad));
    }
    tree_join(tree_join(nl, out), nr)
}
fn tree_restrict_input(t: &Tree, mask: &IntervalSet) -> Tree {
    let n = t.as_ref()?;
    let (lo, hi) = mask.bounds()?;
    if hi < &n.span.0 || lo > &n.span.1 {
        return None;
    }
    // One logarithmic interval lookup replaces two temporary sets at each tree
    // node. A connected span is covered iff its first intersecting piece covers
    // both ends; it is disjoint iff that piece starts after the span.
    let (ml, mh) = mask.piece_at_or_above(&n.span.0)?;
    if ml <= &n.span.0 && &n.span.1 <= mh {
        return t.clone();
    }
    if ml > &n.span.1 {
        return None;
    }
    let (data, l, r) = tree_push(n);
    tree_node(
        n.key(),
        data.meet(mask),
        tree_restrict_input(&l, mask),
        tree_restrict_input(&r, mask),
    )
}
fn coalesce_slice(out: &mut Vec<Slice1d>, lo: End, hi: End, ex: IntervalSet) {
    if let Some((_, h, e)) = out.last_mut()
        && h.succ() == lo
        && *e == ex
    {
        *h = hi
    } else {
        out.push((lo, hi, ex))
    }
}
fn val_from_set(s: &IntervalSet, xs: &IntervalSet) -> Tree {
    val_from_iter(
        &mut s.pieces().map(|(l, h)| (l.clone(), h.clone(), xs.clone())),
        s.len(),
    )
}
// Disjoint ordered intervals need only one balanced construction, not repeated
// AVL unions. Elementary sorted-tree construction; O(p) nodes, no paper used.
fn val_from_sorted(p: &[(End, End, IntervalSet)]) -> Tree {
    val_from_iter(&mut p.iter().cloned(), p.len())
}
fn val_from_iter(it: &mut impl Iterator<Item = (End, End, IntervalSet)>, len: usize) -> Tree {
    if len == 0 {
        return None;
    }
    let mid = len / 2;
    let left = val_from_iter(it, mid);
    let (lo, hi, xs) = it.next().expect("ordered value interval");
    tree_raw((lo, hi), xs, left, val_from_iter(it, len - mid - 1))
}
fn val_at(t: &Tree, v: &End) -> IntervalSet {
    let mut t = t.clone();
    while let Some(n) = t {
        if v >= &n.lo && v <= &n.hi {
            return n.data.clone();
        }
        let (_, l, r) = tree_push(&n);
        t = if v < &n.lo { l } else { r };
    }
    IntervalSet::empty()
}
// The inputs x whose own value x is excluded: x in label(v) with v = x. A subtree
// whose value range misses the hull of its input labels (`span`) holds no such x
// and is skipped; a visited node lists only its label pieces inside its value
// interval (one O(log p) seek), so no temporary sets or node copies are built.
fn val_diagonal(t: &Tree, tag: &ValTag, out: &mut Vec<(End, End)>) {
    let Some(n) = t else { return };
    let (min, max) = tag.map_range(&n.min_lo, &n.max_hi);
    if max < n.span.0 || min > n.span.1 {
        return;
    }
    let inner = tag.compose(&n.lazy);
    val_diagonal(&n.left, &inner, out);
    val_diagonal(&n.right, &inner, out);
    let (lo, hi) = tag.map_range(&n.lo, &n.hi);
    for (a, b) in n.data.pieces_from(&lo).take_while(|(a, _)| *a <= hi) {
        out.push((a.clone().max(lo.clone()), b.clone().min(hi.clone())));
    }
}
#[derive(Clone, Default)]
struct State1d {
    live: IntervalSet,
    cover: IntervalSet,
    inexact: IntervalSet,
    excl: Tree,
}
fn bridge_outside(a: &IntervalSet, dom: &IntervalSet) -> IntervalSet {
    let mut dp = dom.pieces().peekable();
    let mut out: Vec<(End, End)> = Vec::new();
    let mut prev_dom: Option<(usize, End)> = None;
    let mut dom_idx = 0usize;
    for (alo, ahi) in a.pieces() {
        while dp.peek().is_some_and(|(_, dhi)| *dhi < *alo) {
            dp.next();
            dom_idx += 1;
        }
        let Some(&(dlo, _)) = dp.peek() else { break };
        let can_bridge = prev_dom.as_ref().is_some_and(|(p_idx, p_dhi)| {
            *p_idx + 1 == dom_idx && out.last().is_some_and(|(_, ohi)| p_dhi == ohi) && dlo == alo
        });
        if can_bridge {
            out.last_mut().expect("non-empty").1 = ahi.clone();
        } else {
            out.push((alo.clone(), ahi.clone()));
        }
        while dp.peek().is_some_and(|(_, dhi)| *dhi < *ahi) {
            dp.next();
            dom_idx += 1;
        }
        prev_dom = dp.peek().map(|&(_, dhi)| (dom_idx, dhi.clone()));
    }
    IntervalSet::from_pieces(out)
}

fn live_at_slices(slices: &[Slice1d], live: &IntervalSet) -> Vec<IntervalSet> {
    let lp: Vec<&(End, End)> = live.pieces().collect();
    let mut idx = 0usize;
    let mut out = Vec::with_capacity(slices.len());
    for (slo, shi, _) in slices {
        while idx < lp.len() && &lp[idx].1 < slo {
            idx += 1;
        }
        let (mut ps, mut j) = (Vec::new(), idx);
        while j < lp.len() && &lp[j].0 <= shi {
            let (lo, hi) = (slo.max(&lp[j].0).clone(), shi.min(&lp[j].1).clone());
            if lo <= hi {
                ps.push((lo, hi));
            }
            if &lp[j].1 <= shi {
                idx = j + 1;
            }
            j += 1;
        }
        out.push(IntervalSet::from_pieces(ps));
    }
    out
}

impl State1d {
    fn init(dom: &IntervalSet, excl: &IntervalSet) -> Self {
        let Some((lo, hi)) = dom.bounds() else {
            return Self::default();
        };
        Self {
            live: dom.clone(),
            cover: IntervalSet::range(lo.clone(), hi.clone()),
            excl: val_from_set(excl, &IntervalSet::range(lo.clone(), hi.clone())),
            ..Self::default()
        }
    }
    fn restrict_x(&self, mask: &ArmMask) -> Self {
        let Some((live, cover)) = mask else {
            return self.clone();
        };
        Self {
            live: self.live.meet(cover),
            cover: self.cover.meet(cover),
            inexact: self.inexact.meet(live),
            excl: tree_restrict_input(&self.excl, cover),
        }
    }
    fn union(self, other: Self) -> Self {
        if self.live.is_empty() {
            return other;
        }
        if other.live.is_empty() {
            return self;
        }
        Self {
            live: self.live.join(&other.live),
            cover: self.cover.join(&other.cover),
            inexact: self.inexact.join(&other.inexact),
            excl: tree_union(self.excl, other.excl),
        }
    }
    fn apply_tag(mut self, tag: &ValTag) -> Self {
        self.excl = tree_apply(self.excl, tag);
        self
    }
    fn clip_values(mut self, range: &IntervalSet) -> Self {
        self.excl = tree_restrict_set(&self.excl, range);
        self
    }
    fn reflect(self, c: i64) -> Self {
        // The affine endpoint sweep covers translation staircases (output_grid),
        // so the remaining inverse tree can use value order throughout.
        self.apply_tag(&ValTag::reflect(c as i128))
    }
    fn abs(self) -> Self {
        let mut st = self;
        let pos = tree_restrict(&st.excl, &End::of(0), &PosInf);
        st.excl = tree_union(pos.clone(), tree_apply(pos, &ValTag::neg()));
        st
    }
    fn minmax(self, p: Prim, c: i64) -> Self {
        let mut st = self;
        let e = End::of(c);
        let (lo, hi, rl, rh) = if p == Prim::Min {
            (NegInf, e.pred(), e.clone(), PosInf)
        } else {
            (e.succ(), PosInf, NegInf, e.clone())
        };
        st.excl = tree_union(
            tree_restrict(&st.excl, &lo, &hi),
            tree_single(rl, rh, val_at(&st.excl, &e)),
        );
        st
    }
    fn inverse(self, f: impl Fn(&IntervalSet) -> IntervalSet) -> Self {
        let mut st = self;
        let mut raw = Vec::new();
        tree_collect(&st.excl, &mut raw);
        st.excl = raw.into_iter().fold(None, |out, (l, h, xs)| {
            tree_union(out, val_from_set(&f(&IntervalSet::range(l, h)), &xs))
        });
        st
    }
    fn mul(self, c: i64) -> Self {
        match c {
            1 => self,
            -1 => self.apply_tag(&ValTag::neg()),
            _ => self.inverse(|s| times_pre(s, c)),
        }
    }
    fn div(self, c: i64) -> Self {
        match c {
            0 => Self::default(),
            1 => self,
            -1 => self.apply_tag(&ValTag::neg()),
            c if c > 0 => {
                let mut st = self;
                st.excl = tree_division(st.excl, &Num::from(c));
                st
            }
            _ => self.inverse(|s| div_pre(s, c)),
        }
    }
    fn pow(self, k: Num, _fwd: &IntervalSet, fc: &IntervalSet) -> Self {
        if k.is_zero() {
            let cover = self.cover.minus(&self.xs_at_value(&Num::ONE));
            let live = self.live.meet(&cover);
            let raw = cover
                .pieces()
                .map(|(l, h)| (l.clone(), h.clone(), IntervalSet::empty()))
                .collect();
            let mut st = self;
            st.live = live;
            st.cover = cover;
            return st.replace_slices(raw);
        }
        self.inverse(|z| revision::backward(&Op::Pow(k.clone().into()), 0, fc, fc, z))
    }
    fn to_slices(&self) -> Vec<Slice1d> {
        let mut events: BTreeMap<End, Vec<(bool, IntervalSet)>> = BTreeMap::new();
        let mut raw = Vec::new();
        tree_collect(&self.excl, &mut raw);
        for (lo, hi, xs) in raw {
            let set = IntervalSet::range(lo, hi);
            for (xlo, xhi) in xs.pieces() {
                events
                    .entry(xlo.clone())
                    .or_default()
                    .push((true, set.clone()));
                if *xhi != PosInf {
                    events
                        .entry(xhi.succ())
                        .or_default()
                        .push((false, set.clone()));
                }
            }
        }
        for (lo, hi) in self.cover.pieces() {
            events.entry(lo.clone()).or_default();
            if *hi != PosInf {
                events.entry(hi.succ()).or_default();
            }
        }
        let mut events = events.into_iter().peekable();
        let mut ex = IntervalSet::empty();
        let mut out = Vec::new();
        while let Some((lo, at)) = events.next() {
            for add in [false, true] {
                for (_, s) in at.iter().filter(|(a, _)| *a == add) {
                    ex = if add { ex.join(s) } else { ex.minus(s) };
                }
            }
            let hi = events.peek().map_or(PosInf, |(next, _)| next.pred());
            let cell = self.cover.meet(&IntervalSet::range(lo, hi));
            for (lo, hi) in cell.pieces() {
                coalesce_slice(&mut out, lo.clone(), hi.clone(), ex.clone());
            }
        }
        out
    }
    fn replace_slices(mut self, raw: Vec<Slice1d>) -> Self {
        let mut cover = Vec::new();
        let mut kept = Vec::new();
        self.excl = None;
        for (lo, hi, ex) in raw {
            if ex == IntervalSet::top() {
                continue;
            }
            cover.push((lo.clone(), hi.clone()));
            coalesce_slice(&mut kept, lo, hi, ex);
        }
        self.cover = IntervalSet::from_pieces(cover);
        self.live = self.live.meet(&self.cover);
        for (lo, hi, ex) in kept {
            self.excl = tree_union(self.excl, val_from_set(&ex, &IntervalSet::range(lo, hi)));
        }
        self
    }
    fn modulo(mut self, c: i64, _fwd: &IntervalSet, fa: &IntervalSet) -> (Self, bool) {
        if c == 0 {
            return (Self::default(), false);
        }
        let slices = self.to_slices();
        let xs = live_at_slices(&slices, &self.live);
        let top = IntervalSet::top();
        let mut any = false;
        let raw = slices
            .into_iter()
            .zip(xs)
            .map(|((lo, hi, ex), xs)| {
                let (mut nz, mut exact) = (IntervalSet::empty(), true);
                for (lo, hi) in fa.pieces() {
                    let (s, ok) = mod_pre(
                        &top.minus(&ex),
                        c,
                        &IntervalSet::range(lo.clone(), hi.clone()),
                    );
                    nz = nz.join(&s);
                    exact &= ok;
                }
                if !exact && !xs.is_empty() {
                    any = true;
                    self.inexact = self.inexact.join(&xs);
                }
                (lo, hi, top.minus(&nz))
            })
            .collect();
        (self.replace_slices(raw), any)
    }
    fn xs_at_value(&self, n: &Num) -> IntervalSet {
        val_at(&self.excl, &Fin(n.clone()))
    }
    fn eval_diagonal(&self) -> IntervalSet {
        let mut bad = Vec::new();
        val_diagonal(&self.excl, &ValTag::id(), &mut bad);
        self.live.minus(&IntervalSet::from_pieces(bad))
    }
}

impl Tx<'_> {
    // Elementary composition of affine bijections, independent of production's
    // summaries. Compress only unary affine/forward edges, once per DAG node.
    fn affine_end(&mut self, u: At, memo: &mut HashMap<At, (At, ValTag)>) -> (At, ValTag) {
        if let Some(v) = memo.get(&u) {
            return v.clone();
        }
        let edge = match self.step_1d(u.0, u.1).map(|s| s.kind) {
            Some(StepKind::Forward(c)) => Some((c, ValTag::id())),
            Some(StepKind::Shift(k, c)) => Some((c, ValTag::shift(-k))),
            Some(StepKind::Reflect(k, c)) => Some((c, ValTag::reflect(k as i128))),
            Some(StepKind::Neg(c)) => Some((c, ValTag::neg())),
            _ => None,
        };
        let out = match edge {
            None => (u, ValTag::id()),
            Some((c, tag)) => {
                let (base, inner) = self.affine_end(c, memo);
                (base, tag.compose(&inner))
            }
        };
        memo.insert(u, out.clone());
        out
    }

    // Sweep guard endpoints and maintain the composition of the selected affine
    // links in an array segment tree. Each endpoint changes one link in O(log n);
    // inversion on each disjoint input cell writes only its answer pieces. Thus
    // O(n log n + output) scalar work and O(n + output) allocated storage, without
    // persistent AVL path copies. No input points or Boolean choices are run.
    // No paper is used: this is substitution of interval masks and bijections.
    // Measured scored R at 64..512: interleaved 8.01, let 7.99; the input-order
    // tree is no longer needed for the translation-only output_grid staircase.
    fn affine_guards(&mut self, root: Tid, demand: &Demand) -> Option<(Res, Option<Relation>)> {
        let (root, z) = self.integer_request(root, demand)?;
        let VarSet::One(x) = self.step_1d(root, ROOT)?.var else {
            return None;
        };
        let dom = self.cx.inputs[&x].clone();
        let mut memo = HashMap::new();
        let (mut u, mut prefix) = self.affine_end((root, ROOT), &mut memo);
        let mut events = Vec::new();
        let mut count: usize = 0;
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(u) {
                return None;
            }
            match self.step_1d(u.0, u.1)?.kind {
                StepKind::Input => break,
                StepKind::If(Some((c, _)), None) | StepKind::If(None, Some((c, _))) => {
                    let (base, tag) = self.affine_end(c, &mut memo);
                    u = base;
                    prefix = prefix.compose(&tag);
                }
                StepKind::If(Some((a, am)), Some((b, bm))) => {
                    let (at, av) = self.affine_end(a, &mut memo);
                    let (bt, bv) = self.affine_end(b, &mut memo);
                    // A shallow kernel clone has another root id but shared
                    // child ids. Recognize that equality in O(1), without a
                    // repeated structural comparison of the remaining chain.
                    if at != bt
                        && !(at.1 == bt.1
                            && match (self.node(at.0), self.node(bt.0)) {
                                (Node::If(g, a, b), Node::If(h, c, d)) => (g, a, b) == (h, c, d),
                                (Node::Var(a), Node::Var(b)) => a == b,
                                _ => false,
                            })
                    {
                        return None;
                    }
                    for (mask, tag) in [(am, av), (bm, bv)] {
                        let cover = mask.as_ref().map_or(&*dom, |(_, c)| &**c);
                        for (lo, _) in cover.pieces() {
                            events.push((lo.clone(), count, prefix.compose(&tag)));
                        }
                    }
                    count += 1;
                    u = at;
                    prefix = ValTag::id();
                }
                _ => return None,
            }
        }
        if count == 0 {
            return None;
        }
        events.sort_by(|a, b| a.0.cmp(&b.0));
        let size = count.next_power_of_two();
        let mut tree = vec![ValTag::id(); size * 2];
        let mut pieces = Vec::new();
        let mut events = events.into_iter().peekable();
        while let Some((lo, index, tag)) = events.next() {
            let mut updates = vec![(index, tag)];
            while events.peek().is_some_and(|e| e.0 == lo) {
                let (_, i, t) = events.next().unwrap();
                updates.push((i, t));
            }
            for (index, tag) in updates {
                let mut at = size + index;
                tree[at] = tag;
                while at > 1 {
                    at /= 2;
                    tree[at] = tree[at * 2].compose(&tree[at * 2 + 1]);
                }
            }
            let hi = events.peek().map_or(PosInf, |e| e.0.pred());
            let tag = tree[1].compose(&prefix);
            let inv = tag.inverse();
            // Physical holes are clipped once after the sweep. Guard covers are
            // exact on that domain; work inside a hole cannot affect its answer.
            let cell = IntervalSet::range(lo, hi);
            pieces.extend(inv.map_set(&z).meet(&cell).pieces().cloned());
        }
        let met = IntervalSet::from_pieces(pieces).meet(&dom);
        if met.is_empty() {
            return Some((Res::none(), None));
        }
        let mut r = Res::all();
        r.vars = VarSet::One(x.clone());
        if met != *dom {
            r.dom.insert(x, Rc::new(met));
        }
        Some((r, None))
    }

    /// Independent choices of the same involution have only two effects: identity
    /// and reflection. Project these effects directly rather than eliminating n
    /// auxiliary variables. No paper or production summary is used: this is the
    /// elementary identity R(R(v)) = v. Distinct guard inputs are essential.
    /// Cost O(n log n + n*d), d the demand's interval count; no points are run.
    fn independent_reflections(
        &mut self,
        root: Tid,
        d: &Demand,
    ) -> Option<(Res, Option<Relation>)> {
        let (mut t, wanted) = self.integer_request(root, d)?;
        let original = t;
        let mut seen = HashSet::new();
        let mut names = HashSet::new();
        let mut guards = Vec::new();
        let mut center = None;
        while let Node::If(g, a, b) = self.node(t) {
            if !seen.insert(t) {
                return None;
            }
            let mut reflected = None;
            for (plain, other, flip) in [(a, b, false), (b, a, true)] {
                if let Node::Prim(Prim::Sub, args) = self.node(other)
                    && args.len() == 2
                    && self.same(self.arg(args, 1), plain)
                    && let Some(c) = self.constant_int(self.arg(args, 0), ROOT)
                {
                    reflected = Some((plain, c, flip));
                    break;
                }
            }
            let (plain, c, flip) = reflected?;
            if center.is_some_and(|old| old != c) {
                return None;
            }
            center = Some(c);
            let yes = self.back_at(g, ROOT, &Demand::Bool(!flip));
            let no = self.back_at(g, ROOT, &Demand::Bool(flip));
            if !yes.exact || !no.exact {
                return None;
            }
            let VarSet::One(x) = yes.vars.join(&no.vars) else {
                return None;
            };
            if !names.insert(x.clone()) {
                return None;
            }
            let domain = self.cx.inputs.get(&x)?;
            let mask = |r: &Res| {
                if r.none {
                    IntervalSet::empty()
                } else {
                    r.dom
                        .get(&x)
                        .map_or_else(|| (**domain).clone(), |s| (**s).clone())
                }
            };
            let (a, b) = (mask(&yes), mask(&no));
            guards.push((x, a, b));
            t = plain;
        }
        let c = center?;
        let Node::Var(name) = self.node(t) else {
            return None;
        };
        if self.lookup(ROOT, name).is_some() {
            return None;
        }
        let x = self.name(name).clone();
        if names.contains(&x) {
            return None;
        }
        let dom = self.cx.inputs.get(&x)?.clone();
        let allowed = [wanted.clone(), reflect(&wanted, c as i128)];
        let feasible = [
            !dom.meet(&allowed[0]).is_empty(),
            !dom.meet(&allowed[1]).is_empty(),
        ];
        let mut forced = 0usize;
        let mut free = 0usize;
        for (_, a, b) in &guards {
            match (a.is_empty(), b.is_empty()) {
                (true, true) => return Some((Res::none(), None)),
                (true, false) => forced ^= 1,
                (false, false) => free += 1,
                _ => {}
            }
        }
        let mut out = Res::all();
        let mut projected = IntervalSet::empty();
        for (parity, set) in allowed.iter().enumerate() {
            if free != 0 || parity == forced {
                projected = projected.join(&dom.meet(set));
            }
        }
        if projected.is_empty() {
            return Some((Res::none(), None));
        }
        out.dom.insert(x, Rc::new(projected.clone()));
        let (mut remaining, mut parity) = (0usize, 0usize);
        for (x, a, b) in guards {
            let both = !a.is_empty() && !b.is_empty();
            let others_free = free - usize::from(both);
            let others_forced = forced ^ usize::from(a.is_empty());
            let accepts = |p: usize| {
                others_free != 0 && (feasible[0] || feasible[1]) || feasible[others_forced ^ p]
            };
            let a = if accepts(0) { a } else { IntervalSet::empty() };
            let b = if accepts(1) { b } else { IntervalSet::empty() };
            remaining += usize::from(!a.is_empty() && !b.is_empty());
            parity ^= usize::from(a.is_empty());
            out.dom.insert(x, Rc::new(a.join(&b)));
        }
        out.exact =
            (0..=1).all(|p| remaining == 0 && p != parity || projected.is_subset(&allowed[p]));
        out.vars = VarSet::Many;
        let rel = if out.exact {
            None
        } else {
            Some(self.relation_within(original, &wanted)?)
        };
        Some((out, rel))
    }

    /// The relation `original` lies in `wanted`, translated with a new numbering of auxiliary
    /// variables, partway through a run.
    ///
    /// Proof that the relation is the one `original` states (FAIL-ref-memo-stale-entries):
    /// 1. A translation `Tr` numbers its auxiliary variables 0, 1, ... in the order it makes
    ///    them, and `Aux(k)` means the k-th definition of that `Tr`. Each definition fixes its
    ///    variable as a function of the inputs: `x = a` under `g` and `x = b` under `not g`
    ///    ([`Tx::lin_at`], `If`), or the quotient and remainder of one division.
    /// 2. A memo entry (`lin`, `formula`, `lin_calls`, `formula_calls`) holds the translation
    ///    a `Tr` made, with that `Tr`'s numbers, and the memo does not record which `Tr` made
    ///    it. So an entry that names `Aux(k)` is right only with the definitions of the `Tr`
    ///    that made it.
    /// 3. Earlier in this run, [`Tx::difference_guard`] translates with its own `Tr` and keeps
    ///    entries that name no auxiliary variable (its own proof). An earlier call of this
    ///    function may also have left entries with its own numbering. Without step 4, `lin`
    ///    here would reuse such an entry and return `Aux(k)`, which our new `Tr` defines
    ///    differently or not at all. On `if (i mod 2) <= 0 { m } else { 1 - m }`, with
    ///    i, m in [0, 1], the relation then held at (0, 0) and (1, 1), where the term is 0
    ///    (ref_memo.rs, `a_relation_built_partway_through_a_run_holds_only_where_its_term_does`).
    /// 4. So we empty the four translation tables and their log first. Then every entry
    ///    `lin` reads was made with our `tr`, and by steps 1 and 2 the returned linear term
    ///    is the value of `original` under the definitions `tr.defs` that we return with it.
    /// 5. Emptying the log cannot cut short an undo in progress: [`Tx::forget`] marks are
    ///    held only by `lin`, `formula`, `call_key` and `difference_guard` while they run, and
    ///    no translation reaches this function (`lin` and `formula` call only the
    ///    translation's helpers; none of them calls a stage). Callers: only
    ///    `independent_reflections`, a stage of `preimage_in`.
    ///
    /// Complexity tradeoff: the translation done before this call by `difference_guard` is
    /// lost, so `original` is translated again from nothing, O(|term DAG|) once per call, as
    /// [`relations`] does for each term. Keeping the old entries would need each entry to
    /// carry its `Tr` and every read to check it, which costs more in the common run than
    /// one translation per relation.
    fn relation_within(&mut self, original: Tid, wanted: &IntervalSet) -> Option<Relation> {
        self.clear_translations();
        let mut tr = Tr {
            defs: Vec::new(),
            products: false,
        };
        let value = self.lin(&mut tr, original, ROOT)?;
        Some(Relation {
            body: presburger::within(&value, wanted),
            defs: tr.defs,
            bit_ands: Vec::new(),
        })
    }

    /// The integer term and the set its value must lie in: the term itself under an integer
    /// demand, or the non-constant side of a comparison with a constant, with the ray the
    /// comparison asks for. Its value is checked to be an integer by the forward analysis,
    /// which [`Tx::integer_request_shape`] leaves out.
    fn integer_request(&mut self, root: Tid, d: &Demand) -> Option<(Tid, IntervalSet)> {
        let (t, z) = self.integer_request_shape(root, d)?;
        if matches!(d, Demand::Bool(_)) && !self.fwd(t, ROOT).is_int() {
            return None;
        }
        Some((t, z))
    }

    /// [`Tx::integer_request`] without the forward check: for a stage that proves the value an
    /// integer from the shape it reads (`independent_affine`, whose unit-slope paths end at
    /// integer inputs or literals). O(1) beyond `constant_int` and the copy of an `Ints` demand.
    fn integer_request_shape(&mut self, root: Tid, d: &Demand) -> Option<(Tid, IntervalSet)> {
        Some(match d {
            Demand::Ints(z) => (root, z.clone()),
            Demand::Bool(w) => {
                let Node::Prim(mut p, args) = self.node(root) else {
                    return None;
                };
                if !matches!(
                    p,
                    Prim::Eq | Prim::Ne | Prim::Le | Prim::Lt | Prim::Ge | Prim::Gt
                ) || args.len() != 2
                {
                    return None;
                }
                if !w {
                    p = negate(p)
                }
                let (a, b) = (self.arg(args, 0), self.arg(args, 1));
                if let Some(c) = self.constant_int(b, ROOT) {
                    (a, ray(p, c))
                } else {
                    let c = self.constant_int(a, ROOT)?;
                    (b, ray(mirror(p), c))
                }
            }
        })
    }
    fn periodic(&mut self, root: Tid, d: &Demand) -> Option<(Res, Option<Relation>)> {
        let (root, z) = self.integer_request(root, d)?;
        let shape = self.step_1d(root, ROOT)?;
        let VarSet::One(x) = shape.var else {
            return None;
        };
        let mut order = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = vec![((root, ROOT), false)];
        let (mut modular, mut guarded) = (false, false);
        while let Some((u, done)) = stack.pop() {
            if done {
                order.push(u);
                continue;
            }
            if !seen.insert(u) {
                continue;
            }
            stack.push((u, true));
            match self.step_1d(u.0, u.1)?.kind {
                StepKind::Input | StepKind::Const(Value::Int(_) | Value::Big(_)) => {}
                StepKind::Forward(c)
                | StepKind::Shift(_, c)
                | StepKind::Reflect(_, c)
                | StepKind::Neg(c) => stack.push((c, false)),
                StepKind::If(a, b) => {
                    guarded = true;
                    for (c, _) in [a, b].into_iter().flatten() {
                        stack.push((c, false));
                    }
                }
                StepKind::Mod(k, _, c) if k != 0 => {
                    modular = true;
                    stack.push((c, false));
                }
                _ => return None,
            }
        }
        if !modular || !guarded {
            return None;
        }
        order.reverse();
        let dom = self.cx.inputs[&x].clone();
        let mut states = HashMap::from([(
            (root, ROOT),
            HashMap::from([(
                None,
                Parts1d::of(State1d::init(&dom, &IntervalSet::top().minus(&z))),
            )]),
        )]);
        let push =
            |states: &mut HashMap<At, HashMap<Option<u64>, Parts1d>>, (at, mode), next: Parts1d| {
                if !next.live.is_empty() {
                    let modes = states.entry(at).or_default();
                    let next = match modes.remove(&mode) {
                        Some(old) => old.union(next),
                        None => next,
                    };
                    modes.insert(mode, next);
                }
            };
        let (mut met, mut regular) = (IntervalSet::empty(), IntervalSet::empty());
        // IntervalSet caches do not change equality or hashing.
        #[allow(clippy::mutable_key_type)]
        let mut clauses: HashMap<(u64, IntervalSet), IntervalSet> = HashMap::new();
        let mut exact = true;
        for u in order {
            let modes = states.remove(&u).unwrap_or_default();
            for (mode, st) in modes {
                if st.live.is_empty() {
                    continue;
                }
                // This checked periodic language is total (nonzero moduli).
                // With no excluded values every input label already succeeds;
                // do not redistribute it through the remaining guard DAG.
                // A part left by a waiting mask may hold no pair; the steps below then exclude
                // nothing, as this shortcut does.
                if st.parts.is_empty() {
                    regular = regular.join(&st.live);
                    continue;
                }
                let step = self.step_1d(u.0, u.1)?;
                let tagged = |st: Parts1d, tag: &ValTag| match mode {
                    None => st.map_trees(|t| tree_apply(t, tag)),
                    Some(m) => st.map_trees(|t| tree_residue_tag(t, tag, &Num::from(m as i128))),
                };
                match step.kind {
                    StepKind::Forward(c) => push(&mut states, (c, mode), st),
                    StepKind::Shift(k, c) => {
                        push(&mut states, (c, mode), tagged(st, &ValTag::shift(k)))
                    }
                    StepKind::Reflect(k, c) => push(
                        &mut states,
                        (c, mode),
                        tagged(st, &ValTag::reflect(k as i128)),
                    ),
                    StepKind::Neg(c) => push(&mut states, (c, mode), tagged(st, &ValTag::neg())),
                    StepKind::If(a, b) => {
                        for (c, mask) in [a, b].into_iter().flatten() {
                            push(&mut states, (c, mode), st.restrict_x(&mask));
                        }
                    }
                    StepKind::Mod(k, fc, c) => {
                        let m = k.unsigned_abs();
                        let all =
                            IntervalSet::range(End::of(0), Fin(&Num::from(m as i128) - &Num::ONE));
                        match mode {
                            Some(old) if old == m || m % old == 0 => {
                                push(&mut states, (c, mode), st)
                            }
                            Some(old) if m < old => {
                                push(&mut states, (c, Some(m)), Parts1d::of(st.clip_values(&all)))
                            }
                            Some(old) => {
                                // Restrict an incompatible residual period to the proved
                                // high-branch image before attempting its interval inverse.
                                // This settles local small ranges instead of projecting
                                // the complete guarded chain through Presburger.
                                let all = self
                                    .high_image(u, &x)
                                    .filter(|(lower, _)| {
                                        st.live.bounds().is_some_and(|(lo, _)| lo >= lower)
                                    })
                                    .map_or(all.clone(), |(_, r)| all.meet(&r));
                                let next = st.settle().modulo_bounded(modulus_i64(old), &all)?;
                                push(&mut states, (c, Some(m)), Parts1d::of(next));
                            }
                            None => {
                                let fc = self
                                    .high_image(c, &x)
                                    .filter(|(lower, _)| {
                                        st.live.bounds().is_some_and(|(lo, _)| lo >= lower)
                                    })
                                    .map_or(fc, |(_, r)| r);
                                let st = st.settle();
                                if let Some(next) = st.clone().modulo_exact(k, &fc) {
                                    push(&mut states, (c, None), Parts1d::of(next));
                                } else {
                                    let next = Parts1d::of(st.clip_values(&all));
                                    push(&mut states, (c, Some(m)), next);
                                }
                            }
                        }
                    }
                    StepKind::Const(v) => {
                        let n = Num::of_integer(&v)
                            .unwrap_or_else(|| unreachable!("a constant step holds an int"));
                        let n =
                            mode.map_or_else(|| n.clone(), |m| n.rem_euclid(&Num::from(m as i128)));
                        let st = st.settle();
                        regular = regular.join(&st.live.minus(&st.xs_at_value(&n)));
                    }
                    StepKind::Input => match (mode, st.settle()) {
                        (None, st) => regular = regular.join(&st.eval_diagonal()),
                        (Some(m), st) => {
                            let modulus = Num::from(m as i128);
                            let all = IntervalSet::range(End::of(0), Fin(&modulus - &Num::ONE));
                            for (lo, hi, ex) in st.to_slices() {
                                let cell = st.live.meet(&IntervalSet::range(lo, hi));
                                if cell.is_empty() {
                                    continue;
                                }
                                let allowed = all.minus(&ex);
                                if allowed.is_empty() {
                                    continue;
                                }
                                let out = period_pre(&allowed, modulus_i64(m), &cell);
                                if out.is_empty() {
                                    continue;
                                }
                                if residue_image(&out, &modulus).is_subset(&allowed) {
                                    regular = regular.join(&out);
                                } else {
                                    exact = false;
                                    met = met.join(&out);
                                    let old = clauses.entry((m, allowed)).or_default();
                                    *old = old.join(&cell);
                                }
                            }
                        }
                    },
                    _ => unreachable!("the periodic structure was checked"),
                }
            }
        }
        met = met.join(&regular);
        if met.is_empty() {
            return Some((Res::none(), None));
        }
        let mut r = Res::all();
        r.vars = VarSet::One(x.clone());
        r.exact = exact;
        if met != *dom {
            r.dom.insert(x.clone(), Rc::new(met));
        }
        let relation = if exact {
            None
        } else {
            let moduli: BTreeSet<_> = clauses.keys().map(|(m, _)| *m).collect();
            let mut defs = Vec::new();
            let mut ids = HashMap::new();
            for m in moduli {
                let n = to_u32(defs.len(), "definitions");
                let q = Lin::atom(presburger::Atom::Aux(n));
                let rem = Lin::atom(presburger::Atom::Aux(n + 1));
                let a = Lin::atom(presburger::Atom::Sym(x.clone()));
                let mi = m as i128;
                let def = Formula::and(vec![
                    Formula::Con(Con::eq(&a, &q.times(mi).plus(&rem))),
                    Formula::Con(Con::ge(&rem, &Lin::constant(0))),
                    Formula::Con(Con::ge(&Lin::constant(mi - 1), &rem)),
                ]);
                defs.push((n, format!("{x} div {mi}"), def));
                defs.push((n + 1, format!("{x} mod {mi}"), Formula::top()));
                ids.insert(m, n + 1);
            }
            let mut parts: Vec<_> = clauses
                .into_iter()
                .map(|((m, allowed), cell)| {
                    Formula::and(vec![
                        presburger::member(&presburger::Atom::Sym(x.clone()), &cell),
                        presburger::member(&presburger::Atom::Aux(ids[&m]), &allowed),
                    ])
                })
                .collect();
            parts.push(presburger::member(
                &presburger::Atom::Sym(x.clone()),
                &regular,
            ));
            Some(Relation {
                body: Formula::or(parts),
                defs,
                bit_ands: Vec::new(),
            })
        };
        Some((r, relation))
    }
}

impl Tx<'_> {
    fn high_image(&mut self, u: At, x: &Arc<str>) -> Option<(End, IntervalSet)> {
        self.cached(
            |m| &mut m.high_image,
            (u, x.clone()),
            |s| {
                let domain = s.cx.inputs.get(x)?.clone();
                let (dlo, dhi) = domain.bounds()?;
                let step = s.step_1d(u.0, u.1)?;
                match step.kind {
                    StepKind::Input if step.var == VarSet::One(x.clone()) => {
                        Some((dlo.clone(), (*domain).clone()))
                    }
                    StepKind::Const(Value::Int(n)) => Some((dlo.clone(), IntervalSet::single(n))),
                    StepKind::Const(Value::Big(b)) => Some((
                        dlo.clone(),
                        IntervalSet::range(Fin(Num::from(&*b)), Fin(Num::from(&*b))),
                    )),
                    StepKind::Forward(c) => s.high_image(c, x),
                    StepKind::Shift(k, c) => {
                        let (lo, r) = s.high_image(c, x)?;
                        Some((lo, ValTag::shift(-k).map_set(&r)))
                    }
                    StepKind::Reflect(k, c) => {
                        let (lo, r) = s.high_image(c, x)?;
                        Some((lo, ValTag::reflect(k as i128).map_set(&r)))
                    }
                    StepKind::Neg(c) => {
                        let (lo, r) = s.high_image(c, x)?;
                        Some((lo, ValTag::neg().map_set(&r)))
                    }
                    StepKind::Mod(k, _, c) if k != 0 => {
                        let (lo, r) = s.high_image(c, x)?;
                        Some((lo, residue_image(&r, &Num::from(k.unsigned_abs() as i128))))
                    }
                    StepKind::If(a, b) => {
                        let (c, mask) = [a, b].into_iter().flatten().find(|(_, m)| {
                            m.as_ref().is_none_or(|(_, cover)| cover.contains_end(dhi))
                        })?;
                        let lower = match mask {
                            None => dlo.clone(),
                            Some((_, cover)) => cover.pieces().next_back()?.0.clone(),
                        };
                        let (lo, r) = s.high_image(c, x)?;
                        Some((lo.max(lower), r))
                    }
                    _ => None,
                }
            },
        )
    }
}
impl State1d {
    // Exact inversion on a syntactic remainder range, never an input domain.
    // The quotient bands, rather than input points or individual residues, are
    // intersected with the excluded intervals. Cost is proportional to the
    // resulting bands (at most ceil(m/old) per excluded interval for literals
    // m and old), independent of the width of the physical input domain.
    // This is elementary interval substitution, not Presburger elimination.
    // C17's physical-domain approximation in mod_pre is unchanged. This new
    // expansion is bounded by a syntactic remainder range, not the input width;
    // its numeric cost can still be exponential in the bits of a modulus literal.
    // Adopts Opus R2's sorted listing, then merges adjacent equal-labelled
    // intervals. No paper or production summary is used for this construction.
    // For p listed pieces this costs O(p log p) sorting, O(p) comparisons and
    // O(p) tree nodes, plus label-equality cost; no per-piece tree unions.
    // Measured long [7,64] allocation/byte R: 8.30/8.61 (128..1024),
    // 7.86/7.91 (1024..8192). This is not a bound for arbitrary modulus literals.
    fn modulo_bounded(self, c: i64, within: &IntervalSet) -> Option<Self> {
        if within.is_empty() {
            return Some(Self::default());
        }
        let m = Num::from(c.unsigned_abs() as i128);
        let range = residue_image(within, &m);
        let mut st = self.clip_values(&range);
        let mut raw = Vec::new();
        tree_collect(&st.excl, &mut raw);
        let mut listed = Vec::new();
        for (lo, hi, xs) in raw {
            if range.bounds().is_some_and(|(a, b)| &lo <= a && b <= &hi) {
                listed.extend(
                    within
                        .pieces()
                        .map(|(l, h)| (l.clone(), h.clone(), xs.clone())),
                );
                continue;
            }
            for (a, b) in within.pieces() {
                let (Fin(a), Fin(b)) = (a, b) else {
                    return None;
                };
                let mut q = a.div_floor(&m);
                let last = b.div_floor(&m);
                while q <= last {
                    let base = &q * &m;
                    let (Fin(lo), Fin(hi)) = (&lo, &hi) else {
                        return None;
                    };
                    let l = (a.clone()).max(&base + lo);
                    let h = (b.clone()).min(&base + hi);
                    if l <= h {
                        listed.push((Fin(l), Fin(h), xs.clone()));
                    }
                    q = &q + &Num::ONE;
                }
            }
        }
        listed.sort_by(|a, b| a.0.cmp(&b.0));
        // Adjacent exclusions with equal input labels are one interval. In
        // particular, full residue coverage must not retain one tree node per
        // historical cut. Linear coalescing after sorting preserves the set.
        listed.dedup_by(|a, b| {
            if b.1.succ() == a.0 && b.2 == a.2 {
                b.1 = a.1.clone();
                true
            } else {
                false
            }
        });
        st.excl = val_from_sorted(&listed);
        Some(st)
    }

    fn modulo_exact(self, c: i64, within: &IntervalSet) -> Option<Self> {
        if within.is_empty() {
            return Some(Self::default());
        }
        let range = residue_image(within, &Num::from(c.unsigned_abs() as i128));
        let mut st = self.clip_values(&range);
        let mut raw = Vec::new();
        tree_collect(&st.excl, &mut raw);
        let mut tree = None;
        for (lo, hi, xs) in raw {
            let wanted = IntervalSet::range(lo, hi);
            let mut inv = IntervalSet::empty();
            for (lo, hi) in within.pieces() {
                let (s, exact) = mod_pre(&wanted, c, &IntervalSet::range(lo.clone(), hi.clone()));
                if !exact {
                    return None;
                }
                inv = inv.join(&s);
            }
            tree = tree_union(tree, val_from_set(&inv, &xs));
        }
        st.excl = tree;
        Some(st)
    }
}

fn modulus_i64(m: u64) -> i64 {
    i64::try_from(m).unwrap_or(i64::MIN)
}

fn period_pre(rem: &IntervalSet, c: i64, within: &IntervalSet) -> IntervalSet {
    if rem.is_empty() {
        return IntervalSet::empty();
    }
    let m = Num::from(c.unsigned_abs() as i128);
    let (a, b) = rem.bounds().expect("nonempty residues");
    let (Fin(a), Fin(b)) = (a, b) else {
        unreachable!("residues are finite")
    };
    let period = |k: &Num| ValTag(false, k * &m).map_set(rem);
    let mut out = IntervalSet::empty();
    for (lo, hi) in within.pieces() {
        let (k0, k1) = (
            match lo {
                Fin(n) => Some(n.div_floor(&m)),
                _ => None,
            },
            match hi {
                Fin(n) => Some(n.div_floor(&m)),
                _ => None,
            },
        );
        let cell = IntervalSet::range(lo.clone(), hi.clone());
        let mut part = IntervalSet::empty();
        if let Some(k) = &k0 {
            part = part.join(&period(k));
        }
        if let Some(k) = &k1 {
            part = part.join(&period(k));
        }
        if k0
            .as_ref()
            .zip(k1.as_ref())
            .is_none_or(|(l, h)| h > &(l + &Num::ONE))
        {
            let ml = k0
                .as_ref()
                .map_or(NegInf, |k| Fin(&(&(k + &Num::ONE) * &m) + a));
            let mh = k1
                .as_ref()
                .map_or(PosInf, |k| Fin(&(&(k - &Num::ONE) * &m) + b));
            part = part.join(&IntervalSet::range(ml, mh));
        }
        out = out.join(&part.meet(&cell));
    }
    out
}

fn residue_image(s: &IntervalSet, m: &Num) -> IntervalSet {
    let all = IntervalSet::range(End::of(0), Fin(m - &Num::ONE));
    let mut out = IntervalSet::empty();
    for (lo, hi) in s.pieces() {
        let (Fin(lo), Fin(hi)) = (lo, hi) else {
            return all;
        };
        if hi - lo >= m - &Num::ONE {
            return all;
        }
        let (a, b) = (lo.rem_euclid(m), hi.rem_euclid(m));
        let part = if lo.div_floor(m) == hi.div_floor(m) {
            IntervalSet::range(Fin(a), Fin(b))
        } else {
            IntervalSet::range(End::of(0), Fin(b))
                .join(&IntervalSet::range(Fin(a), Fin(m - &Num::ONE)))
        };
        out = out.join(&part);
        if out == all {
            return out;
        }
    }
    out
}

/// `tree` under `tag` with its values taken back into the residues `0..m`.
fn tree_residue_tag(tree: Tree, tag: &ValTag, m: &Num) -> Tree {
    let tag = ValTag(tag.0, tag.1.rem_euclid(m));
    let t = &tree_apply(tree, &tag);
    let lo = tree_apply(
        tree_restrict(t, &NegInf, &End::of(-1)),
        &ValTag(false, m.clone()),
    );
    let mid = tree_restrict(t, &End::of(0), &Fin(m - &Num::ONE));
    let hi = tree_apply(
        tree_restrict(t, &Fin(m.clone()), &PosInf),
        &ValTag(false, -m),
    );
    tree_union(tree_union(lo, mid), hi)
}

/// A [`State1d`] of the periodic pass ([`Tx::periodic`]) whose input restrictions wait: its
/// excluded pairs are those of each part, the part's tree with every label met with the part's
/// mask (`None`: no mask). [`Parts1d::settle`] applies the masks and returns the [`State1d`].
///
/// Why (REF-nested-moduli-state): on `nested_moduli_eq_4096` the state below a link's guard
/// holds every residue of 4096, s = 4096 value pieces whose labels hold most inputs. Applied at
/// once, the two arms of each `i == j` guard rewrite every label that holds `j` (the `j`
/// arm keeps them, the other arm cuts `j` out), and the arm of `j`, s pieces labelled `{j}`,
/// is united back into the state two steps later: O(s log l) for labels of l pieces at each
/// link, with s growing to 4096 over the first links and l growing with n (21.4 times the
/// instructions from 16 to 128 links, 11.47 from 64 to 512; 12.07 and 8.12 with the masks
/// waiting, COMPLEXITY.md REF-nested-moduli-state). Waiting, a guard costs one mask meet per
/// part; the
/// other arm reaches its `mod 7` before any union, and its clip to seven values
/// ([`Parts1d::clip_values`]) leaves seven pieces per part to restrict; the arm of `j` reaches
/// the next union as one part, which waits there too.
///
/// Why the answer is unchanged: a mask acts on labels, every step that waits acts on values
/// only (a tag, a clip), and a union is taken label by label, so restricting before or after
/// those steps gives the same pairs: `restrict(T, M)` then a value map `f` excludes `(f v, x)`
/// for `x ∈ label(v) ∩ M`, and `f` then `restrict` excludes the same pairs; `restrict(A ∪ B, M)`
/// = `restrict(A, M) ∪ restrict(B, M)` pair by pair. Every other step reads the settled state.
/// The consumers read sets (labels and value ranges), not the cut of the tree into nodes,
/// except where adjacent equal labels are merged anyway (`to_slices`, the listing of
/// `modulo_bounded`). Tests: the `ref_memo` tests of `l01_25_preimage_catalog`, which compare
/// this pass with the interpreter and with main, and the dump tests.
//
// Complexity tradeoff (COMPLEXITY.md REF-nested-moduli-state): naive, every guard applies its
// masks at once (`State1d::restrict_x`),
// O(s) per guard for a state of s pieces whose labels cross the mask. Used: masks wait, O(p)
// mask meets per guard for p parts and O(p log s) per tag (`tree_residue_tag`), and a
// clip settles its p clipped parts. A union settles the parts whose mask is not a single input
// (so a chain of interval guards cannot double its parts at each link; it pays the naive cost
// there), keeps the single-input parts, and unites the unmasked ones, so p is one plus the
// single-input parts carried since the last clip or union. A chain of n `i == j` guards with
// no clip between them carries up to n such parts, O(n²) part steps where the naive cost is
// O(n s); on `nested_moduli_eq_4096` p is at most 3.
#[derive(Clone, Default)]
struct Parts1d {
    live: IntervalSet,
    cover: IntervalSet,
    inexact: IntervalSet,
    parts: Vec<(Arc<PartitionNode>, Option<IntervalSet>)>,
}

impl Parts1d {
    fn of(st: State1d) -> Self {
        Self {
            live: st.live,
            cover: st.cover,
            inexact: st.inexact,
            parts: st.excl.map(|t| (t, None)).into_iter().collect(),
        }
    }
    fn settle(self) -> State1d {
        let excl = settle_parts(self.parts);
        State1d {
            live: self.live,
            cover: self.cover,
            inexact: self.inexact,
            excl,
        }
    }
    /// [`State1d::restrict_x`], the masks met with the arm's cover and left to wait. A part
    /// whose labels (inside its tree's `span`) the mask misses goes; one whose labels it holds
    /// loses its mask, since the labels stay as they are.
    fn restrict_x(&self, mask: &ArmMask) -> Self {
        let Some((live, cover)) = mask else {
            return self.clone();
        };
        let parts = (self.parts.iter())
            .filter_map(|(t, m)| {
                let m = m
                    .as_ref()
                    .map_or_else(|| (**cover).clone(), |m| m.meet(cover));
                let (ml, mh) = m.piece_at_or_above(&t.span.0)?;
                if ml > &t.span.1 {
                    return None;
                }
                let held = ml <= &t.span.0 && &t.span.1 <= mh;
                Some((t.clone(), (!held).then_some(m)))
            })
            .collect();
        Self {
            live: self.live.meet(cover),
            cover: self.cover.meet(cover),
            inexact: self.inexact.meet(live),
            parts,
        }
    }
    /// [`State1d::union`]. When both sides hold parts, the parts masked by more than one input
    /// and the unmasked ones are settled into one unmasked part; the single-input parts wait.
    fn union(self, other: Self) -> Self {
        if self.live.is_empty() {
            return other;
        }
        if other.live.is_empty() {
            return self;
        }
        let both = !self.parts.is_empty() && !other.parts.is_empty();
        let mut parts = self.parts;
        parts.extend(other.parts);
        if both {
            let single = |m: &Option<IntervalSet>| {
                m.as_ref()
                    .and_then(|m| m.only())
                    .is_some_and(|(lo, hi)| lo == hi)
            };
            let (wait, now): (Vec<_>, Vec<_>) = parts.into_iter().partition(|(_, m)| single(m));
            parts = wait;
            parts.extend(settle_parts(now).map(|t| (t, None)));
        }
        Self {
            live: self.live.join(&other.live),
            cover: self.cover.join(&other.cover),
            inexact: self.inexact.join(&other.inexact),
            parts,
        }
    }
    fn map_trees(mut self, f: impl Fn(Tree) -> Tree) -> Self {
        self.parts = (self.parts.into_iter())
            .filter_map(|(t, m)| Some((f(Some(t))?, m)))
            .collect();
        self
    }
    fn clip_values(self, range: &IntervalSet) -> State1d {
        self.map_trees(|t| tree_restrict_set(&t, range)).settle()
    }
}

/// The tree of the pairs of `parts`, each tree restricted to its mask, united.
fn settle_parts(parts: Vec<(Arc<PartitionNode>, Option<IntervalSet>)>) -> Tree {
    parts.into_iter().fold(None, |out, (t, m)| {
        let t = Some(t);
        tree_union(
            out,
            match m {
                None => t,
                Some(m) => tree_restrict_input(&t, &m),
            },
        )
    })
}

#[derive(Clone, PartialEq, Eq)]
enum Coordinate {
    Input(Arc<str>),
    Difference(Arc<str>, Arc<str>),
}
impl VarSet {
    fn coordinates(&self) -> VarSet<Coordinate> {
        match self {
            Self::Zero => VarSet::Zero,
            Self::Many => VarSet::Many,
            Self::One(x) => VarSet::One(Coordinate::Input(x.clone())),
        }
    }
}
fn sum_sets(a: &IntervalSet, b: &IntervalSet) -> IntervalSet {
    let mut out = Vec::new();
    for (al, ah) in a.pieces() {
        for (bl, bh) in b.pieces() {
            let lo = match (al, bl) {
                (Fin(a), Fin(b)) => Fin(a + b),
                _ => NegInf,
            };
            let hi = match (ah, bh) {
                (Fin(a), Fin(b)) => Fin(a + b),
                _ => PosInf,
            };
            out.push((lo, hi));
        }
    }
    IntervalSet::from_pieces(out)
}
impl Tx<'_> {
    fn coordinate_domain(&self, c: &Coordinate) -> IntervalSet {
        match c {
            Coordinate::Input(x) => (*self.cx.inputs[x]).clone(),
            Coordinate::Difference(a, b) => sum_sets(
                &self.cx.inputs[a],
                &ValTag::neg().map_set(&self.cx.inputs[b]),
            ),
        }
    }
    fn difference_guard(&mut self, g: Tid, env: Eid) -> Option<(Coordinate, ArmMask, ArmMask)> {
        let Node::Prim(p, args) = self.node(g) else {
            return None;
        };
        if !matches!(
            p,
            Prim::Eq | Prim::Ne | Prim::Le | Prim::Lt | Prim::Ge | Prim::Gt
        ) || args.len() != 2
        {
            return None;
        }
        let (a, b) = (self.arg(args, 0), self.arg(args, 1));
        if !self.fwd(a, env).is_int() || !self.fwd(b, env).is_int() {
            return None;
        }
        let diff = self.terms.diff(g, args);
        // FAIL-ref-memo-stale-entries. This translation runs partway through a run, with a `Tr`
        // of its own, and it keeps no definition. Proof that what it leaves in the memo names
        // no auxiliary variable of its own, so a later translation with another `Tr` cannot
        // read one (see `relation_within`, steps 1 and 2, for why that would be wrong):
        // 1. When `tr` ends with a definition, or the translation fails, `forget(logged)`
        //    removes every entry made since `logged`, which is every entry this call made.
        // 2. Otherwise `tr.defs` is empty at the end. A definition made and then dropped
        //    within the call was dropped by `call_key` or `formula_at` truncating `tr.defs`
        //    to a mark, and they forget at once every entry made since that mark, so each
        //    entry that names it is gone. So no kept entry names an `Aux` of `tr`.
        // 3. An entry this call reused may name an `Aux` of the run's earlier `Tr` (only
        //    `linear`, after its `start`, or `relation_within`; each run has at most one such
        //    `Tr`, since both begin with an empty memo). An entry made here from it names that
        //    same numbering, so it agrees with its definitions. The result is used only when
        //    every atom is a `Sym` (the loop below), and an `Aux` that cancels in the
        //    difference is one value of the inputs (step 1 of `relation_within`), so the
        //    coordinate is exact.
        let logged = self.run.memo.log.len();
        let mut tr = Tr {
            defs: Vec::new(),
            products: false,
        };
        let lin = self.lin(&mut tr, diff, env);
        let Some(lin) = lin.filter(|_| tr.defs.is_empty()) else {
            self.forget(logged);
            return None;
        };
        if !matches!(lin.terms.len(), 1 | 2) {
            return None;
        }
        let mut plus = None;
        let mut minus = None;
        for (atom, k) in &lin.terms {
            let presburger::Atom::Sym(x) = atom else {
                return None;
            };
            if *k == Int::from(1) {
                plus = Some(x.clone());
            } else if *k == Int::from(-1) {
                minus = Some(x.clone());
            } else {
                return None;
            }
        }
        let (coord, reverse) = if lin.terms.len() == 1 {
            match (plus, minus) {
                (Some(x), None) => (Coordinate::Input(x), false),
                (None, Some(x)) => (Coordinate::Input(x), true),
                _ => return None,
            }
        } else {
            let (plus, minus) = (plus?, minus?);
            let reverse = plus > minus;
            (
                if reverse {
                    Coordinate::Difference(minus, plus)
                } else {
                    Coordinate::Difference(plus, minus)
                },
                reverse,
            )
        };
        let dom = self.coordinate_domain(&coord);
        let offset = Num::from(&lin.constant);
        let yes = ValTag(false, -&offset).map_set(&ray(p, 0));
        let yes = if reverse {
            ValTag::neg().map_set(&yes)
        } else {
            yes
        };
        let mask = |s: IntervalSet| {
            let live = s.meet(&dom);
            Some((Rc::new(live), Rc::new(s)))
        };
        Some((
            coord,
            mask(yes.clone()),
            mask(IntervalSet::top().minus(&yes)),
        ))
    }
    fn correlated(&mut self, root: Tid, demand: &Demand) -> Option<(Res, Option<Relation>)> {
        let (root, z) = self.integer_request(root, demand)?;
        let shape = self.step_1d(root, ROOT)?;
        let VarSet::One(coord @ Coordinate::Difference(..)) = shape.guard else {
            return None;
        };
        let Coordinate::Difference(a, b) = &coord else {
            unreachable!()
        };
        let mut seen = HashSet::new();
        let mut todo = vec![(root, ROOT)];
        while let Some(u) = todo.pop() {
            if !seen.insert(u) {
                continue;
            }
            match self.step_1d(u.0, u.1)?.kind {
                StepKind::Leaf | StepKind::Mod(..) => return None,
                StepKind::Pow(ref k, ..) if k.is_zero() => return None,
                StepKind::Input | StepKind::Const(_) => {}
                StepKind::If(y, n) => {
                    for (c, _) in [y, n].into_iter().flatten() {
                        todo.push(c)
                    }
                }
                StepKind::Forward(c)
                | StepKind::Shift(_, c)
                | StepKind::Reflect(_, c)
                | StepKind::Neg(c)
                | StepKind::Abs(c)
                | StepKind::MinMax(_, _, c)
                | StepKind::Mul(_, c)
                | StepKind::Div(_, c)
                | StepKind::Pow(_, _, c)
                | StepKind::Round(_, c) => todo.push(c),
            }
        }
        let domain = self.coordinate_domain(&coord);
        let (leaves, inexact) = self.inverse_states((root, ROOT), &domain, &z);
        if inexact {
            return None;
        }
        let (da, db) = (&*self.cx.inputs[a], &*self.cx.inputs[b]);
        let (mut pa, mut pb, mut covered) = (
            IntervalSet::empty(),
            IntervalSet::empty(),
            IntervalSet::empty(),
        );
        let mut rules = Vec::new();
        for (_, step, st) in leaves {
            if !st.inexact.is_empty() {
                return None;
            }
            let constant = match &step.kind {
                StepKind::Const(v) => {
                    let Some(n) = Num::of_integer(v) else {
                        continue;
                    };
                    Some(n)
                }
                _ => None,
            };
            let name = if constant.is_some() {
                a.clone()
            } else {
                let VarSet::One(x) = step.var else {
                    return None;
                };
                if x != *a && x != *b {
                    return None;
                }
                x
            };
            for (lo, hi, ex) in st.to_slices() {
                let cell = st.live.meet(&IntervalSet::range(lo, hi));
                if cell.is_empty() {
                    continue;
                }
                let want = if let Some(n) = &constant {
                    if ex.contains_end(&Fin(n.clone())) {
                        continue;
                    }
                    self.cx.inputs[&name].as_ref().clone()
                } else {
                    self.cx.inputs[&name].minus(&ex)
                };
                if want.is_empty() {
                    continue;
                }
                let neg = ValTag::neg().map_set(&cell);
                let (ia, ib) = if name == *a {
                    (
                        want.meet(&sum_sets(db, &cell)),
                        db.meet(&sum_sets(&want, &neg)),
                    )
                } else {
                    (
                        da.meet(&sum_sets(&want, &cell)),
                        want.meet(&sum_sets(da, &neg)),
                    )
                };
                if ia.is_empty() || ib.is_empty() {
                    continue;
                }
                pa = pa.join(&ia);
                pb = pb.join(&ib);
                covered = covered.join(&cell);
                rules.push((cell, name.clone(), want));
            }
        }
        if pa.is_empty() || pb.is_empty() {
            return Some((Res::none(), None));
        }
        let out_coordinate = sum_sets(&pa, &ValTag::neg().map_set(&pb));
        let mut exact = out_coordinate.minus(&covered).is_empty();
        for (cell, name, want) in &rules {
            let bad = if name == a {
                pa.minus(want).meet(&sum_sets(&pb, cell))
            } else {
                pb.minus(want)
                    .meet(&sum_sets(&pa, &ValTag::neg().map_set(cell)))
            };
            exact &= bad.is_empty();
        }
        let mut r = Res::all();
        r.vars = VarSet::Many;
        r.exact = exact;
        if pa != *da {
            r.dom.insert(a.clone(), Rc::new(pa));
        }
        if pb != *db {
            r.dom.insert(b.clone(), Rc::new(pb));
        }
        let relation = if exact {
            None
        } else {
            let q = Lin::atom(presburger::Atom::Sym(a.clone()))
                .minus(&Lin::atom(presburger::Atom::Sym(b.clone())));
            let clauses = rules
                .into_iter()
                .map(|(cell, name, want)| {
                    Formula::and(vec![
                        presburger::within(&q, &cell),
                        presburger::member(&presburger::Atom::Sym(name), &want),
                    ])
                })
                .collect();
            Some(Relation::of(Formula::or(clauses)))
        };
        Some((r, relation))
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

/// The box hull of two boxes: the per-name join, where a name only one box narrows is whole.
/// The time is that of the smaller box's names.
fn hull(a: &Sets, b: &Sets) -> Sets {
    let (small, large) = if a.len() < b.len() { (a, b) } else { (b, a) };
    small
        .iter()
        .filter_map(|(k, v)| large.get(k).map(|w| (k.clone(), Rc::new(v.join(w)))))
        .collect()
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

/// The integers `c - v` for each member `v` of `z`, each piece reflected and moved by `c`,
/// exact at any magnitude: used to tell whether the forward image of `{c} - z` merged
/// pieces, and to move doubted values through `c - x` ([`Tx::back_doubt`]).
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
/// Test:
/// `l01_25_preimage_catalog::random::a_remainder_inverts_to_its_first_and_last_periods_and_one_piece_between`.
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
    branch(term, dom, classes, demand, &mut first)?;
    Some(first.0)
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
    // The second search looks for a point of `met` that fails the demand: one whose value is
    // outside it, or whose run fails (DESIGN.md sec:failure).
    let found = fails_in(term, met.clone(), classes, demand)?;
    Some((met, !found))
}

/// Whether some point of `root` with each input in its class fails `demand`: its value is
/// outside the demand, or its run fails. Branch and prune as in [`branch`]: a box is found to
/// hold such a point when [`preimage_in`] drops a value of an input's class from it, dropped
/// when the preimage is exact and keeps all of it, and otherwise halved on its widest input; a
/// single point is evaluated. `None` when a point cannot be run.
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

/// Branch and prune over `root`: each box not skipped by `search` is narrowed by [`preimage_in`]
/// and its inputs' classes, and dropped when empty, given to `search` when every point meets
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

impl Tx<'_> {
    /// The mod arm of a link, `(neg, c, inner, m)` for `c - (inner mod m)` (`neg`),
    /// `c + (inner mod m)`, `(inner mod m) +- c` or `inner mod m`, with literal `c` and
    /// nonzero literal `m`, read as `|m|` (`mod` is Euclidean). O(1).
    fn mod_arm(&self, t: Tid) -> Option<(bool, i128, Tid, i128)> {
        let modulo = |tx: &Self, u: Tid| -> Option<(Tid, i128)> {
            let Node::Prim(Prim::Mod, args) = tx.node(u) else {
                return None;
            };
            if args.len() != 2 {
                return None;
            }
            let Node::Int(m) = tx.node(tx.arg(args, 1)) else {
                return None;
            };
            (m != 0).then(|| (tx.arg(args, 0), i128::from(m).abs()))
        };
        if let Some((inner, m)) = modulo(self, t) {
            return Some((false, 0, inner, m));
        }
        let Node::Prim(op @ (Prim::Add | Prim::Sub), args) = self.node(t) else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let (a, b) = (self.arg(args, 0), self.arg(args, 1));
        match (self.node(a), self.node(b)) {
            (Node::Int(c), _) => {
                let (inner, m) = modulo(self, b)?;
                Some((op == Prim::Sub, i128::from(c), inner, m))
            }
            (_, Node::Int(c)) => {
                let (inner, m) = modulo(self, a)?;
                let c = i128::from(c);
                Some((false, if op == Prim::Sub { -c } else { c }, inner, m))
            }
            _ => None,
        }
    }

    /// False when `t` is a chain of modular links (the shape of the module comment of
    /// `preimage_ref/mod_chain.rs`, read from its arms alone) whose guards read no variable but
    /// its base: such a chain reads one input and is not this stage's. True for anything else,
    /// which the full walk then reads. This keeps the stage's cost on one-input chains of mod
    /// links (`normal_mod_chain`, `normal_mixed_moduli`) to O(n) node reads, with no
    /// [`Tx::difference_guard`], which takes the forward sets of both sides and translates the
    /// guard. Each node of the guards is visited once (a visited set, P207), so O(n + the
    /// guards' nodes).
    fn may_read_two_inputs(&self, t: Tid) -> bool {
        let mut guards = Vec::new();
        let mut cur = t;
        while let Node::If(g, a, b) = self.node(cur) {
            cur = match (self.mod_arm(b), self.mod_arm(a)) {
                (Some((.., inner, _)), _) if self.same_value_node(inner, a) => a,
                (_, Some((.., inner, _))) if self.same_value_node(inner, b) => b,
                _ => return true,
            };
            guards.push(g);
        }
        let Node::Var(base) = self.node(cur) else {
            return true;
        };
        let mut seen = std::collections::HashSet::new();
        while let Some(u) = guards.pop() {
            if !seen.insert(u) {
                continue;
            }
            match self.node(u) {
                Node::Var(v) if v == base => {}
                Node::Int(_) => {}
                Node::Prim(_, args) => guards.extend((0..args.len()).map(|i| self.arg(args, i))),
                _ => return true,
            }
        }
        false
    }

    /// The exact projections of a two-input chain of modular links, and whether their box is
    /// exact, with a relation when it is not; the terms, the proof and the costs are in the
    /// module comment of `preimage_ref/mod_chain.rs`, which holds the residue arithmetic.
    /// `None` for any other term, and for an unbounded base input (its classes would be all
    /// `M_1` residues, a count set by a modulus).
    fn mod_chain_pair(&mut self, root: Tid, d: &Demand) -> Option<(Res, Option<Relation>)> {
        let (original, wanted) = self.integer_request_shape(root, d)?;
        if !self.may_read_two_inputs(original) {
            return None;
        }
        // The links, root to base: a guard on an input, one arm plain and the other the mod
        // arm of that same term. The mod arm is taken where the guard is false when it is the
        // else arm, and where it is true when it is the then arm.
        let mut raw: Vec<(Arc<str>, bool, i128, i128, IntervalSet)> = Vec::new();
        let mut cur = original;
        while let Node::If(g, a, b) = self.node(cur) {
            let (Coordinate::Input(v), yes, no) = self.difference_guard(g, ROOT)? else {
                return None;
            };
            let dom = self.cx.inputs.get(&v)?.clone();
            let live = |m: ArmMask| m.map_or_else(|| (*dom).clone(), |(l, _)| (*l).clone());
            let (plain, (neg, c, m), fire) = if let Some((neg, c, inner, m)) = self.mod_arm(b)
                && self.same_value_node(inner, a)
            {
                (a, (neg, c, m), live(no))
            } else if let Some((neg, c, inner, m)) = self.mod_arm(a)
                && self.same_value_node(inner, b)
            {
                (b, (neg, c, m), live(yes))
            } else {
                return None;
            };
            raw.push((v, neg, c, m, fire));
            cur = plain;
        }
        let Node::Var(base) = self.node(cur) else {
            return None;
        };
        if self.lookup(ROOT, base).is_some() || raw.is_empty() {
            return None;
        }
        let x = self.name(base).clone();
        let mut y: Option<Arc<str>> = None;
        let (mut mx, mut my): (Option<i128>, Option<i128>) = (None, None);
        let mut links = Vec::with_capacity(raw.len());
        // Base outward, checking conditions (1) and (2) of the module comment of `mod_chain.rs`.
        let (mut last_x, mut last_y): (Option<IntervalSet>, Option<IntervalSet>) = (None, None);
        for (v, neg, c, m, fire) in raw.into_iter().rev() {
            let on_x = v == x;
            let (modulus, last) = if on_x {
                (&mut mx, &mut last_x)
            } else {
                if y.get_or_insert_with(|| v.clone()) != &v {
                    return None;
                }
                (&mut my, &mut last_y)
            };
            if *modulus.get_or_insert(m) != m || last.as_ref().is_some_and(|l| !fire.is_subset(l)) {
                return None;
            }
            *last = Some(fire.clone());
            links.push(ModLink { on_x, neg, c, fire });
        }
        let y = y?;
        let (mx, my) = (mx.unwrap_or(1), my?);
        if self.run.void {
            return Some((Res::none(), None));
        }
        let (dom_x, dom_y) = (
            self.cx.inputs.get(&x)?.clone(),
            self.cx.inputs.get(&y)?.clone(),
        );
        let cells = |dom: &IntervalSet, on_x: bool| {
            let mut out = Vec::new();
            let mut rest = dom.clone();
            for l in links.iter().filter(|l| l.on_x == on_x) {
                out.push(rest.minus(&l.fire));
                rest = l.fire.clone();
            }
            out.push(rest);
            out
        };
        let (cx, cy) = (cells(&dom_x, true), cells(&dom_y, false));
        // Bounded `x`: its classes are at most its `W` values (Complexity tradeoff in
        // `mod_chain.rs`).
        let xp: Vec<Pieces> = cx.iter().map(pieces_of).collect::<Option<_>>()?;
        let xne: Vec<bool> = cx.iter().map(|c| !c.is_empty()).collect();
        let yne: Vec<bool> = cy.iter().map(|c| !c.is_empty()).collect();
        let n = links.len();
        let m1 = if links[0].on_x { mx } else { my };
        let unwanted = IntervalSet::top().minus(&wanted);
        let modulus = |l: &ModLink| if l.on_x { mx } else { my };

        // `B_p` and `C_q` (step 4), and at each position the inverse of the other input's
        // composed map, which turns a trajectory's value into its `z` (at a link on `x`) or
        // its `w` (at a link on `y`). `end[j]` is the cell index the link at `j` ends.
        let mut bad_x = vec![Pieces::new(); cx.len()];
        let mut bad_y = vec![Pieces::new(); cy.len()];
        let (mut inv, mut end) = (Vec::with_capacity(n), Vec::with_capacity(n));
        let (mut e, mut o) = (ResidueMap::ID, ResidueMap::ID);
        let (mut p, mut q) = (0, 0);
        for l in &links {
            if l.on_x {
                p += 1;
                bad_x[p] = e.inverse(mx).image(&l.bad(mx, &unwanted), mx);
                e = l.map(mx).after(e, mx);
                inv.push(o.inverse(my));
                end.push(p);
            } else {
                q += 1;
                bad_y[q] = o.inverse(my).image(&l.bad(my, &unwanted), my);
                o = l.map(my).after(o, my);
                inv.push(e.inverse(mx));
                end.push(q);
            }
        }
        let gaps_x: Vec<Pieces> = bad_x.iter().map(|b| gaps(b, mx)).collect();
        let gaps_y: Vec<Pieces> = bad_y.iter().map(|b| gaps(b, my)).collect();
        // `later_y[p]`: the residues `z` that fail with every nonempty cell `q` after `p` (the
        // meet of their `C_q`), `None` when there is none; `all_y` the same over every `q >= 1`.
        let mut later_y: Vec<Option<Pieces>> = vec![None; cx.len()];
        let mut acc: Option<Pieces> = None;
        for j in (0..n).rev() {
            let k = end[j];
            if links[j].on_x {
                later_y[k] = acc.clone();
            } else if yne[k] {
                acc = Some(acc.map_or_else(|| bad_y[k].clone(), |s| meet(&s, &bad_y[k])));
            }
        }
        let all_y = acc;

        // The cells `q` that pass with cell 0 of `x`, or (for `q = 0`) with any cell `p`.
        let mut ypass = vec![false; cy.len()];
        ypass[0] = yne[0]
            && ((xne[0] && !cx[0].meet(&wanted).is_empty())
                || (1..cx.len()).any(|p| xne[p] && any_in(&xp[p], &gaps_x[p], mx)));
        for q in 1..cy.len() {
            ypass[q] = yne[q] && xne[0] && any_in(&xp[0], &gaps_y[q], my);
        }

        // The classes: residues mod `M_1` of the cells `p >= 1` (step 3).
        let present: Vec<Pieces> = (0..cx.len())
            .map(|p| {
                if p >= 1 {
                    residues(&xp[p], m1)
                } else {
                    Vec::new()
                }
            })
            .collect();
        let classes = normal(present.iter().flatten().copied().collect());
        let count: usize = classes
            .iter()
            .map(|&(a, b)| usize::try_from(b - a + 1).unwrap_or(usize::MAX))
            .fold(0, usize::saturating_add);
        if count > MOST_CLASSES {
            return None;
        }
        let each = || classes.iter().flat_map(|&(a, b)| a..=b);

        // Pass 1, per class: which `(p, u)` fail with every nonempty cell `q` (`fails[p]`, in
        // increasing `u`), and which cells `q` pass with some class. Forward: a cell `p` passes
        // with an earlier `q` iff some earlier `w` is outside `B_p`, and with a later `q` iff
        // its `z` is outside their meet `later_y[p]`; a cell `q` passes with an earlier `p` iff
        // some earlier `z` is outside `C_q`. Backward: a cell `q` passes with a later `p` iff
        // its `w` is outside the meet of their `B_p`. Each is step 5 read over the cells.
        let mut fails: Vec<Vec<i128>> = vec![Vec::new(); cx.len()];
        let mut ws = vec![0i128; cy.len()];
        for u in each() {
            let (mut wset, mut zset) = (BTreeSet::new(), BTreeSet::new());
            let mut v = u;
            for (j, l) in links.iter().enumerate() {
                v = l.value(v, modulus(l));
                let k = end[j];
                if l.on_x {
                    if !xne[k] || !contains(&present[k], u) {
                        continue;
                    }
                    let z = inv[j].at(v.rem_euclid(my), my);
                    let pass = hits(&wset, &gaps_x[k])
                        || later_y[k].as_ref().is_some_and(|s| !contains(s, z));
                    if !pass {
                        fails[k].push(u);
                    }
                    zset.insert(z);
                } else if yne[k] {
                    let w = inv[j].at(v.rem_euclid(mx), mx);
                    ws[k] = w;
                    ypass[k] = ypass[k] || hits(&zset, &gaps_y[k]);
                    wset.insert(w);
                }
            }
            let mut later_x: Option<Pieces> = None;
            for j in (0..n).rev() {
                let k = end[j];
                if links[j].on_x {
                    if xne[k] && contains(&present[k], u) {
                        later_x =
                            Some(later_x.map_or_else(|| bad_x[k].clone(), |s| meet(&s, &bad_x[k])));
                    }
                } else if yne[k] && !ypass[k] {
                    ypass[k] = later_x.as_ref().is_some_and(|s| !contains(s, ws[k]));
                }
            }
        }

        // The holes of `x`. Cell 0: `x` fails with cell 0 of `y` (empty, or `x` unwanted) and
        // with every nonempty `q >= 1` (`x mod My` in `all_y`). Cell `p >= 1`: the class fails
        // with every `q >= 1` (`fails[p]`) and `x` fails with cell 0 of `y` (empty, or
        // `x mod Mx` in `B_p`).
        //
        // The budget, `(K + K0 + P) (n + 1)` pieces for `K` classes, `K0` residues mod `My` in
        // cell 0 and `P` pieces of the cells, is the sweeps' own count plus the input's. It is
        // never exceeded when the hull of the domain of `x` is no wider than the least modulus
        // (proof): then two members of the domain differ by less than any modulus, so each
        // residue mod `M_1`, `Mx` or `My` has at most one member. Every piece
        // [`mod_chain::periodic`] makes holds a member of its input, so each call makes at most
        // as many pieces as its input has members: cell 0 at most `K0` (one member per residue
        // mod `My`), and a cell `p >= 1` at most `2 |cell p|` over its two calls, `2K` in all
        // (one member per class). `K0 + 2K <= (K + K0) (n + 1)` for `n >= 1`. Past the budget
        // the cell is kept whole and the answer marked not exact (Complexity tradeoff in
        // `mod_chain.rs`).
        let k0: usize = residues(&xp[0], my)
            .iter()
            .map(|&(a, b)| usize::try_from(b - a + 1).unwrap_or(usize::MAX))
            .fold(0, usize::saturating_add);
        let pieces: usize = xp.iter().map(Vec::len).sum();
        let mut budget = count
            .saturating_add(k0)
            .saturating_add(pieces)
            .saturating_mul(n + 1);
        let mut cover = false;
        let mut kept: Vec<IntervalSet> = cx.clone();
        let failing: Vec<Pieces> = fails
            .iter()
            .map(|f| normal(f.iter().map(|&u| (u, u)).collect()))
            .collect();
        for p in 0..cx.len() {
            if !xne[p] {
                continue;
            }
            let holes = if p == 0 {
                let first = if yne[0] {
                    cx[0].meet(&unwanted)
                } else {
                    cx[0].clone()
                };
                match &all_y {
                    None => pieces_of(&first),
                    Some(r) => periodic(&pieces_of(&first)?, r, my, &mut budget),
                }
            } else if failing[p].is_empty() {
                Some(Vec::new())
            } else if !yne[0] {
                periodic(&xp[p], &failing[p], m1, &mut budget)
            } else {
                let (f, b) = (&failing[p], &bad_x[p]);
                if estimate(&xp[p], f, m1) <= estimate(&xp[p], b, mx) {
                    periodic(&xp[p], f, m1, &mut budget)
                        .and_then(|s| periodic(&s, b, mx, &mut budget))
                } else {
                    periodic(&xp[p], b, mx, &mut budget)
                        .and_then(|s| periodic(&s, f, m1, &mut budget))
                }
            };
            match holes {
                Some(h) => kept[p] = cx[p].minus(&set_of(&h)),
                None => cover = true,
            }
        }
        let proj_x = kept.iter().fold(IntervalSet::empty(), |s, c| s.join(c));
        let proj_y = (0..cy.len())
            .filter(|&q| ypass[q])
            .fold(IntervalSet::empty(), |s, q| s.join(&cy[q]));
        if proj_x.is_empty() || proj_y.is_empty() {
            return Some((Res::none(), None));
        }

        // Exactness: no pair of a kept value and a kept cell fails (step 5 on the kept box).
        let mut exact = !cover;
        let kept_q = (1..cy.len()).any(|q| ypass[q]);
        let kp: Vec<Pieces> = kept.iter().map(pieces_of).collect::<Option<_>>()?;
        if exact && xne[0] {
            let union = normal(
                (1..cy.len())
                    .filter(|&q| ypass[q])
                    .flat_map(|q| bad_y[q].iter().copied())
                    .collect(),
            );
            exact = !(ypass[0] && !kept[0].meet(&unwanted).is_empty())
                && !(kept_q && any_in(&kp[0], &union, my));
        }
        for p in 1..cx.len() {
            if exact && xne[p] {
                exact = !(ypass[0] && any_in(&kp[p], &bad_x[p], mx))
                    && !(kept_q && any_in(&kp[p], &failing[p], m1));
            }
        }
        // Pass 2, per class, over the kept cells and the classes that pass (every value of
        // such a class is kept): a kept `p` fails with an earlier kept `q` iff an earlier `w`
        // is in `B_p`, and a kept `q` with an earlier kept `p` iff an earlier `z` is in `C_q`.
        // That covers every pair `0 < jy(q) < jx(p)` and `0 < jx(p) < jy(q)`.
        if exact {
            'classes: for u in each() {
                let (mut wset, mut zset) = (BTreeSet::new(), BTreeSet::new());
                let mut v = u;
                for (j, l) in links.iter().enumerate() {
                    v = l.value(v, modulus(l));
                    let k = end[j];
                    if l.on_x {
                        if !xne[k]
                            || !contains(&present[k], u)
                            || fails[k].binary_search(&u).is_ok()
                        {
                            continue;
                        }
                        if hits(&wset, &bad_x[k]) {
                            exact = false;
                            break 'classes;
                        }
                        zset.insert(inv[j].at(v.rem_euclid(my), my));
                    } else if ypass[k] {
                        if hits(&zset, &bad_y[k]) {
                            exact = false;
                            break 'classes;
                        }
                        wset.insert(inv[j].at(v.rem_euclid(mx), mx));
                    }
                }
            }
        }

        let mut out = Res::all();
        out.exact = exact;
        out.vars = VarSet::Many;
        if proj_x != *dom_x {
            out.dom.insert(x, Rc::new(proj_x));
        }
        if proj_y != *dom_y {
            out.dom.insert(y, Rc::new(proj_y));
        }
        let relation = if exact {
            None
        } else {
            Some(self.relation_within(original, &wanted)?)
        };
        Some((out, relation))
    }
}
