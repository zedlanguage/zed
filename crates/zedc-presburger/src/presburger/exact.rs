//! The exact projection of a formula onto each symbol, from the solver's answer, which is the
//! union of the hulls of disjuncts and so may hold values with no point (PRES-project-exact-
//! solver; author P197: "never avoid giving the full, complete, correct result -- but always
//! look for the fastest possible algorithm to get it").
//!
//! The solver projects each disjunct to its hull and meets each disjunction's union of them
//! (`super::project_parts`). That set holds every value with a point, but it can hold more:
//! a disjunct whose points leave holes (`x + 2 * y == 0` has only even `x`), and a value that
//! each disjunction allows through a different disjunct, where no one combination of them
//! does. Both cases came from the random tests (step 1 of the row: 50 of the pendants'
//! projections onto one symbol, 100 of l01_39 `random`'s, 33 of zedc_preimage's, 1 of
//! l01_38 `random`'s).
//!
//! The method, a model-guided cover of the solver's answer `h` (the projection by lazy model
//! enumeration of Monniaux, "Quantifier elimination by lazy model enumeration", CAV 2010, and
//! the model-based projection of Bjørner and Janota, "Playing with quantified satisfaction",
//! LPAR 2015): the set found so far `r` starts empty; while some point of `f` has the symbol
//! in `h` and outside `r` ([`super::satisfiable`] of `f` with the symbol in the gap), a cell
//! around that point, a set of values each with a point of `f`, is added to `r`. When no such
//! point is left, `r` is the projection: every value of `r` has a point, and every value with
//! a point lies in `h` and so in `r`. The cell of a point `m` is the union of:
//! - the line through `m`: the values `u` at which `f` holds with the symbol at `u` and every
//!   other atom at its value in `m`, found exactly by reading each constraint as a bound on `u`
//!   ([`line`]), O(|f| p) for p pieces of the result;
//! - the projection of the implicant of `f` at `m`, the conjunction of the constraints that
//!   hold at `m` and choose, in each disjunction, one disjunct that holds there (`implicant`),
//!   which implies `f`: where [`super::eliminated`] removes every other atom of it exactly
//!   (Fourier-Motzkin with the exact and dark shadows, Pugh, "The Omega test: a fast and
//!   practical integer programming algorithm for dependence analysis", Supercomputing 1991),
//!   the rows left bound the symbol, and each value between those bounds has a point of the
//!   implicant, so of `f`.
//!
//! Each question asks of one piece of the gap left (`f` and two bounds, so a question costs
//! the same however many holes the gap has): it either finds a point, whose value was outside
//! `r` and is added, or proves the piece empty and drops it. A cell of q pieces splits at most
//! q pieces of the gap, so the questions number at most the pieces of `h` plus, for each cell,
//! its pieces and one more; the loop ends when `h` is finite, after at most one question for
//! each of its values and one for each of its pieces; a cell
//! from an implicant takes the whole projection of that implicant, so each implicant gives at
//! most one such cell. The work is counted (`Work`), never timed, so where the loop is
//! stopped is the same on every run.
//!
//! Published work used in this file. Each site names the author; the full citation is in the
//! crate's `lib.rs`, "References". Monniaux 2010, doi:10.1007/978-3-642-14295-6_51; Bjørner and
//! Janota 2015, doi:10.29007/vv21; Pugh 1991, doi:10.1145/125826.125848, and 1992,
//! doi:10.1145/135226.135233; Freuder 1982, doi:10.1145/322290.322292.
// Complexity tradeoff: naive version, one decision of `f` with the symbol at each value of
// `h` (as the per-value check of the step 1 measurement did): exact, |h| questions for each
// symbol, and nothing for an unbounded `h`. Pugh's exact projection (the Omega test's
// splinters and strides, "The Omega test", 1991, sec. 4 of the expanded text, "Projection of
// Integer Programming Problems"; the comment had "section 3", which is on nonlinear
// subscripts; the crate root's References) gives a union of stride sets for
// one conjunction, but a disjunctive formula first needs its disjunctive normal form, which
// is exponential in the number of disjunctions, and the solver already avoids it. Used: the
// model-guided cover, one question for each cell and one more, each question one run of the
// solver on `f` and the gap, and O(|f|) for each cell: where the solver's hull was exact and
// the first point's cell covers it, as most do, one question in all for every symbol of the
// call together (the points found are kept for the other symbols). Measured on the families
// of step 1 (COMPLEXITY.md row PRES-pugh-work-budget).
// Trigger: a holed disjunct (a stride, `x + 2 * y == 0`), or values each disjunction allows
// through a different disjunct. Tests: `exact::tests`; zedc_preimage
// `or_if_projections_keep_the_gaps_the_if_reading_shows` and `or_ifs_hold_where_they_held_as_ifs`,
// on the checker's path since PRES-cover-wire (PRES-project-exact-solver).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use zed_graph::UnionFind;
use zedc_int::int::{Int, IntRange, meet_range, range_is_empty, range_meet, row_range};
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::lattice::Congruence;

use super::absorbing;
use super::formula::{Ends, Id};
pub use super::meter::{
    DIRECT_OFF, EXACT_LIMIT, EXACT_LIMIT_SET, EXACT_OFF, EXACT_QUESTIONS, EXACT_WORK, FAST_WORK,
    GUARDED_OFF, PART_CACHE_OFF, QUESTION_WORK, SHARED_OFF, SOLVER_UNIT, TWO_DISTRIBUTED_OFF,
};
use super::meter::{PIECE, Solver, Work};
use super::{Atom, Classed, Con, Each, EachClassed, Factor, Formula, Lin, Model, Refusal, Rel};

mod guarded;
mod projection;
pub use projection::{METHOD, Method};
use projection::{Strided, Tail, bounded, each_constraint, fin, holds_at, value};

/// The charge of [`Work`] that eliminates rows, here rather than in module `meter` with the
/// rest of [`Work`], so that the meter holds no step of the cover (row MAIN-red-pugh-land).
/// `Work::ask` is in module `meter`: `projection::rays` asks it too, and `projection` imports
/// nothing of this module (`s_01f_import_graph`). The solver's steps are the function values
/// of `Work::solver` ([`Solver`]), not paths into `presburger.rs`, which calls this module
/// (row PRES-cover-wire).
impl Work {
    /// A size-preserving exact shadow, with its input rows and all generated rows
    /// counted. A stopped shadow's provisional contradiction is discarded by `metered`.
    fn eliminate(
        &mut self,
        rows: &[Con],
        keep: &dyn Fn(&Atom) -> bool,
    ) -> Result<Option<Vec<Con>>, Refusal> {
        self.read(rows.len() as u64)?;
        let counted = self.solver.eliminated_counted;
        self.metered(|| counted(rows, keep))
    }
}

/// The exact projection of `f` onto each of `syms`, from `found`, the solver's answer, each of
/// its sets holding every value with a point (with any disjunction it left out, wider but
/// still holding them). A symbol the solver refused keeps its refusal. A symbol whose cover
/// meets a refused question or the work limit is refused for that cause
/// ([`Refusal::Questions`]): the solver's set is never kept in place of the exact one
/// (PRES-pugh-work-budget, decided by P197 exact answers and P13 no surprises, as `row_sums`
/// refuses past its limit). Every set answered is then exact, so the causes of the
/// disjunctions the solver left out, which made its sets wider, are dropped, but for values
/// with holes without end (`projection::Tail`): no set of ranges is exact there, so the piece
/// that holds them is kept whole, the finest set of ranges holding them, and
/// [`Refusal::Repeats`] is given as the cause of the wider answer, where refusing it dropped
/// what the solver alone answers (`l01_39_reduced_product::scaling::an_even_number_that_is_
/// odd_is_empty`, whose parity the reduction then finds).
///
/// `f` is in the form of [`super::canonical_parts`], as its one caller, `project_each_with`,
/// gives it: the solver and the cover then read one formula whatever order its parts were
/// written in, so the cover's models, cells, work and any refusal past the limit do not
/// depend on that order (PRES-cover-order-refusals). A caller with a formula in another
/// order puts it in that form first, once for both. `solver` holds the solver's steps the
/// cover asks ([`Solver`]).
pub(super) fn exact_each(f: &Formula, syms: &[Atom], found: Each, solver: Solver) -> EachClassed {
    exact_each_checked(f, syms, found, solver).unwrap_or_else(|e| EachClassed {
        sets: vec![Err(e); syms.len()],
        causes: Vec::new(),
    })
}

/// [`exact_each`], or the refusal of the projection as a whole where every symbol of a formula
/// of one part is refused at a step of its cover that does not read the symbol, for one cause.
pub(super) fn exact_each_checked(
    f: &Formula,
    syms: &[Atom],
    found: Each,
    solver: Solver,
) -> Result<EachClassed, Refusal> {
    if EXACT_OFF.get() {
        return Ok(EachClassed::plain(found));
    }
    let (each, _) = found;
    // A set of the solver's that is empty shows that `f` has no point, since each set it
    // answers holds every value of its symbol with a point: every projection of `f` is then
    // empty, the answer the covers below give (an empty `h` covered at once, every other
    // cover's questions finding no point, `has_points` false), and a refusal stays as it was.
    // Complexity tradeoff: naive version, the covers run as for any `f`, which first splits
    // `f` into parts (`split`, O(t log t) for t terms, uncharged) and asks `has_points` of
    // each part, so a call whose every set was empty took 2.4 ms of CPU time at 0 units and
    // a refusal of `has_points` replaced answers known to be empty (`nest_empty`,
    // PRES-work-charge-fit: past its prediction, as `split` is not charged). Used: one look at
    // each answer, O(k) for k symbols, before any work.
    if each
        .iter()
        .any(|h| h.as_ref().is_ok_and(IntervalSet::is_empty))
    {
        let out = (each.into_iter())
            .map(|r| r.map(|_| IntervalSet::empty()))
            .collect();
        return Ok(EachClassed::plain((out, Vec::new())));
    }
    if let Some(out) = by_columns(f, syms, &each, solver) {
        return Ok(out);
    }
    let limit = EXACT_LIMIT_SET.get().unwrap_or(EXACT_LIMIT);
    // The conjuncts of `f` grouped into parts that share no atom (`split`): each symbol is
    // covered over its own part, and the answers stand once every part is shown to have a
    // point, by a point a cover found there or else once for the call (`has_points`).
    let parts = split(f);
    let many = parts.len() > 1;
    let mut points: Vec<Vec<Model>> = vec![Vec::new(); parts.len()];
    let part_of: HashMap<&Atom, usize> = (parts.iter().enumerate())
        .flat_map(|(i, p)| p.atoms.iter().map(move |a| (a, i)))
        .collect();
    // Each part as a smaller formula with the same values of every symbol at its points, and a
    // point exactly where the part has one (`reduced`, every symbol kept), where one is found
    // within an allowance of its own (`tried`, as [`direct`]); its covers ask their questions
    // of it, and keep its points apart from those of the part, which they are not. A part
    // whose reduced formula a cover shows to have a point has one (`shown`).
    let kept: HashSet<&Atom> = syms.iter().collect();
    let mut allowance = limit;
    let small: Vec<Option<(Formula, u64)>> = (parts.iter())
        .map(|p| {
            if !p.factors.is_empty() {
                return None;
            }
            let g = tried(&mut allowance, solver, |w| {
                reduced(&p.f, &|a| kept.contains(a), w)
            })?;
            let size = constraints(&g);
            Some((g, size))
        })
        .collect();
    // Each part read once over blocks answered for all its atoms at once (`read_once`), within
    // an allowance of its own as [`direct`]; where it declines, its symbols are covered below
    // as before, with the same points, their fast paths having what the reading left (below).
    // The allowance is the limit once for each distinct symbol of the part the solver answered,
    // and a part with none is not read: the fast paths of the covers below, which run where it
    // declines, have the limit each, one for each such symbol. Every set
    // `read_once` answers is the exact projection, as is every set a cover answers, so where
    // both answer the answers are the same; a symbol whose cover would be refused may get its
    // exact set here instead. EXACT_LIMIT itself, the limit of each symbol, is unchanged.
    // Complexity tradeoff: before, an allowance of the limit for the whole part, so a part
    // whose one reading passed it, though linear (14,600 units for each group of four rows of
    // `disjoint::bench`, past 3,100,000 from 213 groups), went to the covers, each reading the
    // whole part again: O(k·r) for k symbols over r rows, 1,607,657,400 units and 46 s at
    // 224 groups against 2,802,000 units and 0.2 s at 192. Used: one reading, O(r) at that
    // size; the covers run only where it declines for another reason (COMPLEXITY.md row
    // PRES-cover-bench-disjoint-reduced).
    // Each symbol once, in the order of `Atom`, whatever the order of `syms`: a cover reads the
    // points the covers before it found in its part, so its work, and a refusal past the limit,
    // would depend on the symbols covered before it (`tests::the_answers_do_not_depend_on_the_
    // order_of_the_symbols`). With `f` canonical, as its caller gives it, the answers are then a
    // function of `f` up to the order of its parts and of the set of `syms`. Complexity
    // tradeoff: O(k log k) more for k symbols, and a symbol named twice is covered once. The
    // points a cover keeps are those of the model enumeration (Monniaux, CAV 2010, sec. 3,
    // doi:10.1007/978-3-642-14295-6_51);
    // fixing the order of the symbols is this module's own choice, from no paper.
    let mut sorted: BTreeMap<&Atom, Result<IntervalSet, Refusal>> = BTreeMap::new();
    for (s, got) in syms.iter().zip(each) {
        sorted.entry(s).or_insert(got);
    }
    // The symbols with a cover to run, those the solver answered, counted for each part: the
    // reading of the part stands in for their covers alone, and a part with none is not read
    // (no answer reads its reading).
    let mut asked: Vec<u64> = vec![0; parts.len()];
    let mut members: Vec<Vec<(&Atom, &IntervalSet)>> = vec![Vec::new(); parts.len()];
    for (s, got) in &sorted {
        if let Ok(h) = got
            && let Some(i) = part_of.get(s).copied().or((!many).then_some(0))
        {
            asked[i] += 1;
            members[i].push((*s, h));
        }
    }
    // The forward certificate of each symbol (`guarded::forward`), then the reading of the
    // part, both on the part's one allowance of `k·L`, and the work they used of it. The
    // certificate answers `h` itself where every value of it is shown to have a point by
    // definitions taken in order from `s`, with no question; such a symbol is neither read
    // nor covered. Where it declines, its work stays spent: the reading, then the fast paths of
    // the covers (`charge`, below), get only what is left, so the bound below is unchanged.
    // A symbol the certificate answers needs no reading, and where it answers every symbol of
    // the part the reading does not run.
    // Complexity tradeoff: the certificate is O(r·t) for r conjuncts of t terms, then O(r·t) for
    // each of the P pieces of `h`, with no question; the part is prepared for it once
    // (`guarded::prepare`), not once a name, and a part with more atoms than its definitions
    // plus 2 is rejected there for all its names (PRES-groupA-forward-per-part); the loop of the
    // cover asks at least one question a value where each value is its own cell (guards-beyond: one
    // for each value of `i`, each a run of the solver on the whole formula, O(v·r·t) or more for v
    // values), and on the chain of absolute values the reading alone spent 2,971,100 of 3,100,000
    // units at 1,100 levels, all of them at 8,800, against the certificate's 70,512 and 563,312.
    // Where it declines, its work, at most the part's allowance, is taken from the reading and the
    // fast paths, never from the loops (PRES-cover-bench-guards-beyond, -chains-abs).
    let mut certified: HashMap<&Atom, Classed> = HashMap::new();
    let mut once: Vec<(Option<ReadOnce>, u64)> = Vec::with_capacity(parts.len());
    for ((p, &k), mine) in parts.iter().zip(&asked).zip(&members) {
        if !p.factors.is_empty() || k == 0 {
            once.push((None, 0));
            continue;
        }
        let allowed = limit.saturating_mul(k);
        let mut left = allowed;
        let mut open = k;
        if !GUARDED_OFF.get()
            && let Some(prep) = tried(&mut left, solver, |w| guarded::prepare(&p.f, w))
        {
            for (s, set) in certificates(&prep, mine, &mut left, solver) {
                certified.insert(s, set);
                open -= 1;
            }
        }
        let got = if open > 0 {
            tried(&mut left, solver, |w| read_once(&p.f, w))
        } else {
            None
        };
        once.push((got, allowed - left));
    }
    // Where the reading declines, the cells of points shared by the part's symbols
    // ([`shared_cells`]), with what the reading left of the part's allowance `k·L`, and its
    // work added to the reading's, so that `w` below is at most `k·L` as before (`tried` takes
    // at most what it holds). The symbols it shows get their exact sets; the rest are covered
    // alone below, with its points. A symbol the forward certificate answered (above) is not
    // asked again. The step runs only where two or more symbols are left to cover: this is a
    // structural condition, not a tuned threshold, since a reading shared by one symbol saves
    // no reading, and the phase would only add questions where [`direct`] asks none
    // (`tests::fast_path_uses_the_full_work_limit_and_zero_allowance_walks_nothing`). Its work
    // goes into `once[i].1`, the `w` charged below, from an allowance of `k·L` less what the
    // certificates and the reading spent (`allowed`); a certified symbol's share of `w` comes
    // off a fast allowance it no longer uses. The allowance meets only the step's work that its
    // structure does not bound (`cell`, whose projections and eliminations run the solver, and
    // the questions); its reading, which grows with the part, is charged past it
    // ([`Work::exempt`] for `point_cells` and its own reads, [`Work::credit`] of the declared
    // room of each `quick_search`), so `tried` returns at most `allowed` used and `w <= k·L`
    // still, which the even charge below needs. The call's work is then at most `4·k·L` plus
    // that reading, O((k + 1)·T·α(T) + k·size) for T the terms of the part (see
    // [`shared_cells`]); the covers it stands in for read the part at least once a symbol.
    // Test: `tests::a_part_certified_in_part_shares_only_what_direct_declined` (answers equal with
    // the step off, `SHARED_OFF`, and the work of both within `4·k·L`); it cannot catch an
    // exempt reading that grows past the `O(...)` above.
    // Complexity tradeoff: before, the reading met the allowance too, a fixed `k·L` (15.3M
    // units for the 5 names of `deep_condition`'s `heavy`) that does not grow with the part: the
    // step read 10.67M at depth 1,440 and gave up past about 2,050, and every symbol was then
    // covered alone, 92M units at depth 5,760 where the step alone now answers in 62.5M (55M
    // against 31.3M at 2,880), a change of method at a size set by no cost model
    // (LIMITS-shared-step-allowance, the no-thresholds rule). Naive alternatives: no allowance
    // at all, which leaves `cell`'s eliminations and the solver runs of `quick_search`'s leaves
    // with no bound; or a larger fixed one, which only moves the crossing. See also
    // [`shared_cells`].
    let mut small_points: Vec<Vec<Model>> = vec![Vec::new(); parts.len()];
    let mut shared: Vec<HashMap<Atom, IntervalSet>> = vec![HashMap::new(); parts.len()];
    for (i, p) in parts.iter().enumerate() {
        if SHARED_OFF.get() || once[i].0.is_some() || !p.factors.is_empty() || asked[i] < 2 {
            continue;
        }
        // Complexity tradeoff: `members[i]` already holds the answered symbols of part `i` in
        // the order of `sorted`, so this reads O(k_i) entries per part and O(n) in all. Scanning
        // all of `sorted` for each part, as 0ac1dccff did, was O(parts · n) = O(n²) hash lookups
        // when every part is small (`independent_stages_scale`: 10.514,
        // FAIL-bench-independent-stages).
        let want: BTreeMap<&Atom, IntervalSet> = (members[i].iter())
            .filter(|(s, _)| !certified.contains_key(*s))
            .map(|(s, h)| (*s, (*h).clone()))
            .collect();
        if want.len() < 2 {
            continue;
        }
        let allowed = limit.saturating_mul(asked[i]) - once[i].1;
        let mut left = allowed;
        let out = &mut shared[i];
        tried(&mut left, solver, |w| {
            let (g, size, at) = match &small[i] {
                Some((g, size)) => (g, *size, &mut small_points[i]),
                None => (&p.f, p.size, &mut points[i]),
            };
            shared_cells(g, size, want, at, out, w).map(Some)
        });
        once[i].1 += allowed - left;
    }
    // Where the reading gives up, the fast path of each symbol's cover ([`direct`], in
    // [`cover`]) has what the reading left of that symbol's limit: the reading is a fast path
    // done for the part's symbols together, in place of their `direct`s. Its work `w`, with
    // that of the certificates before it (above), is at
    // most `k·L` for the part's k symbols and limit L (`tried` takes from the allowance at most
    // what it holds) and is charged evenly: in the order of `Atom`, the j-th symbol (from 0) is
    // charged `w / k`, plus 1 where `j < w % k`. The charges sum to exactly `w`, since `w % k`
    // symbols get the 1, and each is at most L: `w / k <= L`, and `w / k < L` where
    // `w % k > 0`, as then `w < k·L`. So the fast allowances left sum to `k·L - w`, and the
    // reading and one fast path for each symbol admit at most `k·L`, what one fast path for
    // each symbol admits with no reading. A symbol runs at most two fast paths (over the
    // reduced formula, then over the part), so the fast work of the part is at most
    // `w + 2·(k·L - w) <= 2·k·L`, and its loops (`cells_cover`) at most two limits each, `2·k·L`,
    // as with no reading: in all `4·k·L`, the bound of the covers alone. Before, the reading
    // came on top of that, up to `5·k·L`. Every meter may pass its limit by its one stopping
    // charge, as before; `reduced` and `has_points` (one limit for the call each) are outside
    // the symbols' limits, with or without the reading. A fast path with nothing left does not
    // run (`tried`), and its symbol is covered by the loop as with `direct` off: every answer
    // is the same as before (each exact), and a loop's limit and so its refusals do not depend
    // on any fast path (`tests::the_work_limit_is_met_alike_on_both_sides`).
    // Charging the loops too would bound the call by `k·L`, but the loop of a symbol would then
    // be refused by work done before it, which `tried` excludes: run so, that test failed and
    // `s22::the_cover_answers_where_the_solver_alone_answered_on_two_shapes_at_moduli_5_and_7`
    // refused one answer more (7, 3, remainders of two inputs, 2). Under A99 read for each
    // symbol (QUESTIONS A159) such a refusal would be correct; this keeps the loop as it was.
    // Complexity tradeoff: before (90cac8417), each fast path had the whole limit after the
    // reading gave up, so the fast work passed what the covers alone could spend (101,700 units
    // where k·L is 48,000 in `tests::a_reading_that_gives_up_late_leaves_the_covers_only_what_
    // is_left`, now 48,900, the reading's own). Naive alternative: charge each symbol the work of
    // the blocks that read its atoms, which needs the reading to count work per atom, O(atoms of
    // each block) more bookkeeping, for a share that only moves fast-path budget between
    // symbols. Used: the even charge, O(1) per symbol (COMPLEXITY.md row
    // PRES-cover-bench-disjoint-reduced, the second one).
    let charge = |i: usize, j: u64| -> u64 {
        let (w, k) = (once[i].1, asked[i].max(1));
        w / k + u64::from(j < w % k)
    };
    let mut nth: Vec<u64> = vec![0; parts.len()];
    // Each part's cache for its covers over the reduced formula and over the part ([`PartCache`]).
    let mut small_cache: Vec<PartCache> = (0..parts.len()).map(|_| PartCache::default()).collect();
    let mut part_cache: Vec<PartCache> = (0..parts.len()).map(|_| PartCache::default()).collect();
    let mut shown = vec![false; parts.len()];
    let mut wider = false;
    let answers: BTreeMap<&Atom, Result<Classed, Refusal>> = (sorted.into_iter())
        .map(|(s, got)| {
            // Each symbol's cover has a limit of its own, as each refusal names one symbol: a
            // limit shared by the call would refuse a symbol by the work of those before it in
            // the order above, and batch where single answers (PRES-pugh-xr round 2, D). Its fast
            // path has what the part's reading left of the limit (`charge`, above).
            let mut work = Work {
                used: 0,
                limit,
                solver,
            };
            let answer = (|| {
                let h = got?;
                let at = part_of.get(s).copied();
                let Some(i) = at.or((!many).then_some(0)) else {
                    // `s` is in no part of `f`: every value, once each part has a point.
                    return Ok(Classed::plain(IntervalSet::top()));
                };
                let fast = limit - charge(i, nth[i]);
                nth[i] += 1;
                let p = &parts[i];
                if PART_CACHE_OFF.get() {
                    small_cache[i] = PartCache::default();
                    part_cache[i] = PartCache::default();
                }
                // `h` is not empty here (above), and each of its values has a point of the part.
                if let Some(set) = certified.remove(s) {
                    shown[i] = true;
                    return Ok(set);
                }
                if let (Some((has, sets)), _) = &once[i] {
                    shown[i] |= *has;
                    return Ok(Classed::plain(match (sets.get(s), has) {
                        (Some(set), _) => set.clone(),
                        (None, true) => IntervalSet::range(End::NegInf, End::PosInf),
                        (None, false) => IntervalSet::empty(),
                    }));
                }
                if let Some(set) = shared[i].get(s) {
                    shown[i] |= small[i].is_some() && !set.is_empty();
                    return Ok(Classed::plain(set.clone()));
                }
                // The cover of `s` over the part's smaller formula (above), with the limit of its
                // own; where it is refused, the cover over `p.f` runs as it did before, with a
                // limit of its own too, so no answer is refused that was answered before.
                if let Some((g, size)) = &small[i] {
                    let mut alone = Work {
                        used: 0,
                        limit,
                        solver,
                    };
                    let got = cover(
                        g,
                        s,
                        &h,
                        *size,
                        &p.factors,
                        &mut small_points[i],
                        &mut small_cache[i],
                        fast,
                        &mut alone,
                    );
                    if let Ok((set, kept)) = got {
                        shown[i] |= !set.is_empty();
                        wider |= kept;
                        return Ok(set);
                    }
                }
                let (set, kept) = cover(
                    &p.f,
                    s,
                    &h,
                    p.size,
                    &p.factors,
                    &mut points[i],
                    &mut part_cache[i],
                    fast,
                    &mut work,
                )?;
                wider |= kept;
                Ok(set)
            })();
            (s, answer)
        })
        .collect();
    // Every symbol of the one part refused at a step of its cover over the part that does not
    // read the symbol (`PartCache::refused` counts them), all for one cause: the projection as
    // a whole is refused, as the solver refuses it alone, so the caller reports it once and not
    // once a symbol (`Scope::project_part` indexes each refusal under every name of the part).
    // Complexity tradeoff: naive version, k refusals of k names each, O(k²): 4.66 s of the
    // 9.7 s of `disjoint::bench::the_join_of_arms_on_many_disjoint_refused_groups_reduced_scales`
    // at 1,024 symbols; used: one refusal, O(k) (from the Gemini 4 Neon seat of
    // PRES-cover-hybrid, `exact_each_checked`).
    if let ([_], Some((_, Err(e)))) = (parts.as_slice(), answers.first_key_value())
        && answers.len() > 1
        && part_cache[0].refused == answers.len() as u64
        && answers.values().all(|a| a.as_ref().err() == Some(e))
    {
        return Err(e.clone());
    }
    let out: Vec<Result<Classed, Refusal>> = syms.iter().map(|s| answers[s].clone()).collect();
    if !many {
        return Ok(EachClassed {
            sets: out,
            causes: if wider {
                vec![Refusal::Repeats]
            } else {
                Vec::new()
            },
        });
    }
    let mut call = Work {
        used: 0,
        limit,
        solver,
    };
    let has = has_points(&parts, &mut points, &small, &shown, &mut call);
    // A refusal, the solver's or the cover's, stays as it was; where a part has no point, `f`
    // has none, and every other answer is empty; where the check is refused, so is every
    // answer, which rests on it.
    let wider = wider && has == Ok(true);
    let out = (out.into_iter())
        .map(|r| match (&has, r) {
            (_, Err(e)) => Err(e),
            (Ok(true), r) => r,
            (Ok(false), _) => Ok(Classed::plain(IntervalSet::empty())),
            (Err(e), _) => Err(e.clone()),
        })
        .collect();
    Ok(EachClassed {
        sets: out,
        causes: if wider {
            vec![Refusal::Repeats]
        } else {
            Vec::new()
        },
    })
}

/// A part of `f` for [`split`]: the conjunction of some of its conjuncts, the atoms they read,
/// their constraints and the factors of their products.
struct Piece {
    f: Formula,
    atoms: HashSet<Atom>,
    size: u64,
    factors: HashSet<Atom>,
}

/// The conjuncts of `f` (its parts, and theirs where they are conjunctions too) grouped so
/// that no two groups read one atom, each group a conjunction: `f` itself where they do not
/// part. A product is read as reading its factors too, since its value is theirs. A value of
/// `s` has a point of `f` exactly when it has one of the group reading `s` and every other
/// group has a point: points of groups reading disjoint atoms join into one point of `f`.
// Complexity tradeoff: the cover asked each question and read each cell on the whole formula,
// so a call on n stages that share no atom cost O(n) for each symbol and O(n^2) for all
// (`bench::omega::every_state_and_credit_of_a_pipeline_scale`, 5.4 M units for each symbol at
// 3,450 constraints, refused). Used: union-find over the atoms of the conjuncts, with path
// halving and no union by rank, O(t log t) for t terms, once a call; each symbol's cover then
// reads its own group. The same split the solver makes for its hulls (item TIGHTEN-each-whole),
// made here for the cover. The conjuncts are read by `Formula::conjuncts`, a shared conjunction
// once: read once for each path to it, `A_(n+1) = A_n ∧ A_n` gave 2^(n+1) conjuncts (42 s and
// 8 GB at n = 22; Sol, round 2 of PRES-pugh-xr), test
// `splitting_a_shared_conjunction_reads_it_once`.
fn split(f: &Formula) -> Vec<Piece> {
    let conjuncts = f.conjuncts();
    let whole = || {
        vec![Piece {
            f: f.clone(),
            atoms: atoms_of(f),
            size: constraints(f),
            factors: factors(f),
        }]
    };
    if conjuncts.len() < 2 {
        return whole();
    }
    let mut parent = UnionFind::new(conjuncts.len());
    let mut first: HashMap<Atom, usize> = HashMap::new();
    let mut reads: Vec<HashSet<Atom>> = Vec::with_capacity(conjuncts.len());
    for (i, g) in conjuncts.iter().enumerate() {
        let atoms = atoms_of(g);
        for a in &atoms {
            let j = *first.entry(a.clone()).or_insert(i);
            parent.union_least(i, j);
        }
        reads.push(atoms);
    }
    // The groups in the order of their first conjunct, so the same on every run.
    let mut order: Vec<usize> = Vec::new();
    let mut of: HashMap<usize, usize> = HashMap::new();
    let mut groups: Vec<(Vec<Formula>, HashSet<Atom>)> = Vec::new();
    for (i, g) in conjuncts.iter().enumerate() {
        let r = parent.find(i);
        let k = *of.entry(r).or_insert_with(|| {
            order.push(r);
            groups.push((Vec::new(), HashSet::new()));
            groups.len() - 1
        });
        groups[k].0.push((*g).clone());
        let atoms = std::mem::take(&mut reads[i]);
        groups[k].1.extend(atoms);
    }
    if groups.len() < 2 {
        return whole();
    }
    (groups.into_iter())
        .map(|(gs, atoms)| {
            let f = Formula::and(gs);
            Piece {
                size: constraints(&f),
                factors: factors(&f),
                atoms,
                f,
            }
        })
        .collect()
}

/// The atoms `f` reads, a product's factors among them.
fn atoms_of(f: &Formula) -> HashSet<Atom> {
    let mut out = HashSet::new();
    each_constraint(f, |c| {
        for a in c.lin.terms.keys() {
            if let Atom::Product(p, q) = a {
                for x in [p, q] {
                    out.insert(match x {
                        Factor::Sym(n) => Atom::Sym(n.clone()),
                        Factor::Aux(i) => Atom::Aux(*i),
                    });
                }
            }
            out.insert(a.clone());
        }
    });
    out
}

/// A point of `f`, found without a question where one comes soon: the parts of `f` are taken
/// depth first, each disjunction by its first disjunct, then the next where that branch has
/// no point; at the end of a branch its rows go to [`super::point_of`] (exact elimination and
/// one solve of the rows left), and a point is taken once `f` holds there ([`holds_as`]).
/// `None` once the rows read pass `room`, or where no branch gave a point: the caller asks the
/// solver then, so no answer rests on a branch left untried. `f` has no product atom. The
/// search is [`quick_search`]; a proof that `f` has no point counts as `None` here.
fn quick_point(f: &Formula, room: u64, work: &mut Work) -> Result<Option<Model>, Refusal> {
    Ok(match quick_search(f, None, room, work)? {
        Quick::Point(m) => Some(m),
        Quick::Empty | Quick::Unknown => None,
    })
}

/// What [`quick_search`] found.
enum Quick {
    /// A point of the formula (and of the restriction).
    Point(Model),
    /// A proof that there is none: every branch was cut.
    Empty,
    /// Neither, within the room given.
    Unknown,
}

/// The decisions of [`quick_search`]'s path that a failed branch, or every branch below a
/// decision, failed on: the decisions at depths `..=upto`, and each decision of `tips` with
/// the decisions that hold it (its `up`, their `up`, and so on). A decision that holds a
/// failed row is in the set by its tip alone, so a set takes O(1) entries a row, not one for
/// each decision above it.
#[derive(Default)]
struct Conflict {
    upto: Option<usize>,
    tips: BTreeSet<usize>,
}

impl Conflict {
    /// The set of the decision `at` (and those that hold it); empty for `None`, a row that
    /// no decision holds.
    fn of(at: &[Option<usize>]) -> Conflict {
        Conflict {
            upto: None,
            tips: at.iter().flatten().copied().collect(),
        }
    }

    /// The deepest decision of the set: every decision that holds a tip is above it.
    fn deepest(&self) -> Option<usize> {
        self.upto.max(self.tips.last().copied())
    }

    /// The union with `other`, the smaller set moved into the larger.
    fn join(&mut self, mut other: Conflict) {
        if other.tips.len() > self.tips.len() {
            std::mem::swap(&mut self.tips, &mut other.tips);
        }
        self.tips.extend(other.tips);
        self.upto = self.upto.max(other.upto);
    }

    /// The set without the decision `d`, its deepest, held by `up`: the decisions that hold
    /// `d` stay, as the disjunction of `d` is reached only through them.
    fn without(&mut self, d: usize, up: Option<usize>) {
        self.tips.remove(&d);
        if self.upto == Some(d) {
            self.upto = d.checked_sub(1);
        }
        self.tips.extend(up);
    }
}

/// The search of [`quick_point`]. `within`, where given, is a formula taken with `f`, so a
/// point is one of both: a question's restriction of one symbol to a piece
/// ([`shared_cells`]), whose rows then cut every branch that leaves the piece as soon as
/// they are taken (below).
///
/// A branch is cut, with no leaf, once its rows of one atom ([`super::slack::unary_bound`])
/// meet in a range with no integer, or a row of no atom is false, or it meets an empty
/// disjunction: no point holds those rows, each atom read as its own value as `point_of`
/// reads it, so `point_of` would find none at the leaf. In a conjunction the rows that do not
/// branch are taken before its other parts: the parts are a conjunction, so any order gives
/// the same branches, and the rows, taken first, cut a branch before it goes down a nest
/// below them.
///
/// A decision is a disjunction (or a row `t != 0`, two branches) taken by its first disjunct,
/// the others waiting; each part taken carries the decision that holds it (`None` at the
/// top). Where a branch fails, the search goes back by conflict-directed backjumping (CBJ;
/// P. Prosser, "Hybrid algorithms for the constraint satisfaction problem", Computational
/// Intelligence 9(3):268–299, 1993, doi:10.1111/j.1467-8640.1993.tb00310.x, §3.3, pp. 277–279,
/// `cbj-label` and `cbj-unlabel`, read in full text from CORE work 59827248, checked again
/// against that text on 2026-11-19 with the allpapers skill). The paper, for
/// variables `v[1..n]` taken in order: "CBJ maintains a conflict set `conf-set[i]` for each
/// variable ... When a consistency check fails between `v[i]` and `v[h]`, h is added to the
/// set `conf-set[i]`. ... If there are no remaining values to be tried in
/// `current-domain[i]`, CBJ jumps back to the deepest variable `v[h]`, where h ∈
/// `conf-set[i]` ... The array element `conf-set[h]` becomes `conf-set[h] ∪ conf-set[i] − h`"
/// (`cbj-unlabel` line 4:
/// `conf-set[h] ← remove(h, union(conf-set[h], conf-set[i]))`); the values of the variables
/// passed over are not tried. Departures: (1) the variables are the decisions of the path,
/// made as the disjunctions are reached, and a value is a disjunct, so a branch's rows depend
/// on the decisions that hold them, not on every decision above them; (2) a cut's conflict
/// is the decisions that hold its rows (the two that gave the empty range's ends, or the false
/// row, or the empty disjunction), each with the decisions that hold it (`Conflict::tips`),
/// since a row is taken in every branch that makes the decisions holding it; (3) a decision
/// whose disjuncts all failed passes up its set without itself but with the decision that
/// holds its disjunction (`Conflict::without`), as the disjunction is reached only through
/// it; (4) a leaf where `point_of` gives no point, a failure with no explanation, conflicts
/// with every decision of the path (`Conflict::upto`), which makes the step back chronological
/// there, as in naive backtracking. A disjunct passed over fails for the reason recorded, as
/// the rows of the conflict are taken in it too, so it has no point: the branches tried are
/// those of the plain depth-first search less those with no point, in the same order, so the
/// first branch with a point, and the point, are the same, reached with no more rows read.
/// Each branch is charged the rows it took since it was taken from its decision (`took`), at
/// most the leaf it would have read, so the search never gives up where it did not before.
///
/// [`Quick::Empty`] is given where the conflict of a failure holds no decision (every branch
/// fails for its reason) and no leaf failed without a proof: the branches are the
/// disjunctive normal form of `f ∧ within`, every point of which holds some branch. A branch
/// that reached its leaf with no point proves nothing, as `point_of` gives `None` also where
/// the solver refuses its rows, so the search then gives [`Quick::Unknown`] and the caller
/// asks the solver.
// Complexity tradeoff: a question of the solver on a part of 7 constraints cost 40,800 units
// and 0.65 ms (`bench::omega::independent_stages_scale`, load 60), so one for each of n parts
// cost 1.2 s at n = 1,800. Naive alternative: every branch of the disjunctive normal form,
// exponential in the disjunctions. Used: the first branches, stopped at `room` rows read,
// which the caller sets to the rows the question it replaces is charged to read, so this never
// costs more than that charge, plus the elimination and solve of the branches read (charged by
// the solver's meter).
// Complexity tradeoff (the cuts and the backjumping): `deep_condition`'s `heavy` d deep, asked
// for a point with `w <= -1`, has one only in the last disjunct at the top. With neither, each
// branch went down the nest d deep before its leaf, and chronological backtracking tried again
// the waiting disjunct `y >= 0` of each level's `z <= 0 || y >= 0`, which no failure involves:
// 2^d branches, so the room ran out (654 cuts at d = 180 with the cuts alone) and the question
// went to the solver, 2.49M units at d = 180 and past the allowance of `shared_cells` at d =
// 1,440 (BENCH-deep-small-choice: 11.0 times the instructions at 8 times the depth). Used: the
// ends of each atom kept for each branch in a persistent map (`imbl::OrdMap`, copied in O(1)
// where a decision is made), O(log a) a row for a atoms, and CBJ's conflict sets, held as
// tips (a join moves the smaller set into the larger, O(s log p) for s tips moved, p decisions
// on the path). On `heavy` (L_i the body/outer decision of level i, Y_i its `z <= 0 || y >= 0`,
// S_i its small/deep): the small disjunct of S_i is cut at its first rows, `w >= i` against
// `w <= -1` or `20 <= x` against `x <= 10` of S_(i-1), conflict {S_i} or {S_i, S_(i-1)}; the
// outer disjunct of L_(i+1) is cut by `100 <= x` against `x <= 10` of S_i, conflict
// {L_(i+1), S_i}; so a failed level i+1 hands up {S_i} (S_(i+1) left with its `up` L_(i+1),
// then L_(i+1) left with its `up` S_i), the jump passing over Y_(i+1), deeper than L_(i+1) and
// in no conflict. That is O(1) branches a level, each O(1) rows past the one descent, and
// conflicts of at most 2 tips: O(d log a) in all, and the leaf of the point (outer_0 and
// `100 <= x <= 200`) has O(1) rows (COMPLEXITY.md row BENCH-deep-small-choice).
//
// Proof that a backjump never passes over a branch with a point (PROOF-quick-search-backjump-
// sound, 2026-11-19). Tests: `a_backjump_never_passes_over_a_branch_with_a_point` (one case
// for each way of getting a step below wrong) and
// `quick_search_on_rows_of_one_atom_finds_a_point_wherever_one_exists` (random, no room
// limit). Each wrong jump named below was run as a negative control against them, not
// committed, and was caught. Prosser gives no proof of CBJ ("An informal proof of the
// completeness of CBJ, using induction, has been given by Tsang (1992)", p. 279); this one
// follows the same induction, over the departures (1)–(4) above.
//
// Terms. The branches of `f ∧ within` form a tree: a node is a disjunction (or a `t != 0`)
// at a place in the formula tree (a subformula shared by several parents counts once for each
// place), and a leaf is a full choice of disjuncts, a term of the disjunctive normal form.
// Every point of `f ∧ within` holds the rows of some leaf. Decision j of the path is a place
// p_j with the disjunct c_j taken there now. Its disjunction is reached only through the
// disjunct c_up(j) of decision up(j) < j (or always, where `up` is `None`). A part held by j
// (reached from c_j through conjunctions and negations, not through another decision) is in
// every leaf that takes c_j at p_j. For a conflict C, cl(C) is its tips, the decisions that
// hold them (`up`, the `up` of that, and so on) and the decisions `0..=upto`. cl(C) is
// closed under `up`, and `deepest` is its largest member. Valid(C) means: every leaf that
// takes c_j at p_j for each j in cl(C) has no point, or was already given to `point_of`.
//
// (a) Each failure gives a valid conflict. A cut by an empty range: the two rows that gave
// its ends have no common integer, and each is held by `l_at` or `h_at` (or by none), so it
// is in every leaf that takes those choices and the choices above them. None of those leaves
// has a point: the rows are read with each atom as its own value, which allows at least the
// points of the formula. On a tie of ends the shallower holder is kept; its row gives the
// same end. A false row, or an empty disjunction, held by `at`: the same with one part. A
// leaf where `point_of` gives no point: cl is every decision of the path, and the one leaf
// that takes all of them is this leaf, already given to `point_of`.
//
// (b) The jump passes over no point. Let C be valid and h = deepest(C). Decisions `0..=h`
// stay. The frames deeper than h are dropped with their disjuncts untried, as `cbj-unlabel`
// (lines 5–9) resets `conf-set[j]` and the domain of each j in h+1..=i. Each disjunct
// dropped, and each leaf below it, takes c_j for every j <= h, so for every j in cl(C), a
// subset of `0..=h`. By Valid(C) none of those leaves has a point, unless it was tried.
//
// (c) The conflict a decision passes up is valid. A frame d lives only while decisions
// `0..d` stay, and each disjunct a of d that is tried and gives no point joins exactly one
// conflict C_a into it, with deepest(C_a) = d, valid with c_d = a (by induction on the order
// in which the search finishes subtrees, from (a) and this step). For `t != 0` the second
// branch, cut where the decision is made, gives its conflict at once. Once every disjunct is
// tried, `Conflict::without` gives C' = (the union of the C_a, less d) with up(d) added: d is
// the deepest, so no other tip is held through d, and `upto = d` becomes d - 1. Let L be a
// leaf that takes c_j for every j in cl(C'). L takes c_up(d) and the choices above it, so it
// reaches p_d and takes there some disjunct a. Every j in cl(C_a) other than d is below d
// and in cl(C'), so L takes c_j, and by Valid(C_a) L has no point or was tried. So Valid(C').
// Without up(d) a leaf need not reach p_d, and the step fails (negative control 1); with the
// conflict of only the last disjunct, in place of the union, it fails too (control 5).
//
// (d) The answers. A point is given only after `holds_as` shows it holds `f` and `within`.
// `Empty` is given only when a valid conflict has an empty cl, so every leaf has no point or
// was given to `point_of`, and only when no leaf was (`leaf_without_point` is false): so no
// leaf, and no point of `f ∧ within`, exists. `Unknown` claims nothing. A point can be missed
// only in a leaf given to `point_of` (the solver refused its rows), and then the answer is
// `Unknown`, never `Empty`.
fn quick_search(
    f: &Formula,
    within: Option<&Formula>,
    room: u64,
    work: &mut Work,
) -> Result<Quick, Refusal> {
    // A list shared by the branches that hold it, so a branch is copied in O(1).
    struct Node<T>(T, List<T>);
    type List<T> = Option<Rc<Node<T>>>;
    // A part still to take: the formula, its sign, and the decision that holds it.
    type Item<'a> = (&'a Formula, bool, Option<usize>);
    // The ends of an atom that the rows of one atom of a branch give, met, with the decision
    // that holds the row that gave each end.
    type Held = (Ends, Option<usize>, Option<usize>);
    type Bounds = imbl::OrdMap<Atom, Held>;
    // A branch: the rows taken, the parts still to take, and the ends of its rows of one atom.
    type Branch<'a> = (List<Con>, List<Item<'a>>, Bounds);
    // A decision of the path: the disjuncts still to try (the next last), each as the branch
    // was where the decision was made with the disjunct to take; the conflicts of those tried
    // (`conf-set`); and the decision that holds the disjunction.
    struct Frame<'a> {
        alts: Vec<Branch<'a>>,
        conflict: Conflict,
        up: Option<usize>,
    }
    fn push<T>(l: &List<T>, x: T) -> List<T> {
        Some(Rc::new(Node(x, l.clone())))
    }
    // Takes the row `c`, held by the decision `at`, into `bounds`: the conflict where the
    // branch then has no point, as a row of no atom is false or the ends of one atom meet in
    // a range with no integer.
    fn bound(bounds: &mut Bounds, c: &Con, at: Option<usize>) -> Result<(), Conflict> {
        match super::slack::unary_bound(c) {
            Some((_, _, true)) => Err(Conflict::of(&[at])),
            Some((Some(a), (lo, hi), false)) => {
                let ((mut l, mut h), mut l_at, mut h_at) =
                    bounds
                        .get(&a)
                        .cloned()
                        .unwrap_or(((None, None), None, None));
                // Each end is the tighter of the two; on a tie, held by the shallower decision
                // (`None`, held by none, first), so a conflict is no deeper than it must be. A
                // row taken earlier in a branch can be held by a deeper decision, as the parts
                // of a conjunction held by an outer decision may wait below an inner one.
                match (&lo, &l) {
                    (Some(v), Some(o)) if v < o => {}
                    (Some(v), Some(o)) if v == o => l_at = l_at.min(at),
                    (Some(_), _) => (l, l_at) = (lo, at),
                    (None, _) => {}
                }
                match (&hi, &h) {
                    (Some(v), Some(o)) if v > o => {}
                    (Some(v), Some(o)) if v == o => h_at = h_at.min(at),
                    (Some(_), _) => (h, h_at) = (hi, at),
                    (None, _) => {}
                }
                let ends = (l, h);
                if range_is_empty(&ends) {
                    return Err(Conflict::of(&[l_at, h_at]));
                }
                bounds.insert(a, (ends, l_at, h_at));
                Ok(())
            }
            _ => Ok(()),
        }
    }
    // Whether `h`, with sign `pos`, is one row that makes no branch: a constraint, under any
    // number of negations, other than a negated equation (`t != 0`, two branches).
    fn plain_row(mut h: &Formula, mut pos: bool) -> bool {
        while let Formula::Not(g) = h {
            h = g;
            pos = !pos;
        }
        matches!(h, Formula::Con(c) if pos || c.rel != Rel::Eq)
    }
    // Drops a list node by node: dropped whole, a long list would recurse once a node.
    fn unwind<T>(mut l: List<T>) {
        while let Some(rc) = l {
            match Rc::try_unwrap(rc) {
                Ok(Node(_, next)) => l = next,
                Err(_) => break,
            }
        }
    }
    fn drop_frame(frame: Frame) {
        for (r, t, _) in frame.alts {
            unwind(r);
            unwind(t);
        }
    }
    let mut start = push(&None, (f, true, None));
    if let Some(g) = within {
        start = push(&start, (g, true, None));
    }
    let mut path: Vec<Frame> = Vec::new();
    let mut next: Option<Branch> = Some((None, start, Bounds::new()));
    let mut read = 0u64;
    let mut charged = 0u64;
    // Whether a branch reached its leaf and gave no point there: then no proof of no point.
    let mut leaf_without_point = false;
    while let Some((mut rows, mut todo, mut bounds)) = next.take() {
        // The rows this branch took since it was taken from its decision, charged where it is
        // cut.
        let mut took = 0u64;
        // The conflict of the branch's failure; `None` where the room ran out.
        let failed: Option<Conflict> = 'run: {
            while let Some(top) = todo.clone() {
                let (g, pos, at) = top.0;
                todo = top.1.clone();
                match g {
                    Formula::Con(c) => {
                        let (row, at) = match (pos, c.rel) {
                            (true, _) => (c.clone(), at),
                            (false, Rel::Ge) => (negated(c, &Int::from(-1)), at),
                            (false, Rel::Eq) => {
                                // `t != 0`: a decision, `t >= 1`, else `t <= -1`.
                                read += 1;
                                let d = path.len();
                                let other = negated(c, &Int::from(-1));
                                let mut theirs = bounds.clone();
                                let mut frame = Frame {
                                    alts: Vec::new(),
                                    conflict: Conflict::default(),
                                    up: at,
                                };
                                match bound(&mut theirs, &other, Some(d)) {
                                    Ok(()) => {
                                        frame.alts.push((push(&rows, other), todo.clone(), theirs))
                                    }
                                    // Already failed: its conflict is the decision's first.
                                    Err(k) => frame.conflict = k,
                                }
                                path.push(frame);
                                (negated(c, &Int::from(1)), Some(d))
                            }
                        };
                        took += 1;
                        let held = bound(&mut bounds, &row, at);
                        rows = push(&rows, row);
                        if let Err(k) = held {
                            read += took;
                            break 'run (read <= room).then_some(k);
                        }
                    }
                    Formula::Not(h) => todo = push(&todo, (&**h, !pos, at)),
                    Formula::And(gs) | Formula::Or(gs) => {
                        if matches!(g, Formula::And(_)) == pos {
                            // The rows that do not branch go on top, so they are taken first;
                            // the other parts keep their order below them.
                            for h in gs.iter().rev().filter(|h| !plain_row(h, pos)) {
                                todo = push(&todo, (h, pos, at));
                            }
                            for h in gs.iter().rev().filter(|h| plain_row(h, pos)) {
                                todo = push(&todo, (h, pos, at));
                            }
                        } else if let [h] = &gs[..] {
                            // One disjunct: taken, with no decision.
                            todo = push(&todo, (h, pos, at));
                        } else if let Some((head, rest)) = gs.split_first() {
                            // A decision: the later disjuncts wait, the next one first.
                            let d = path.len();
                            let mut alts = Vec::with_capacity(rest.len());
                            for h in rest.iter().rev() {
                                read += 1;
                                alts.push((
                                    rows.clone(),
                                    push(&todo, (h, pos, Some(d))),
                                    bounds.clone(),
                                ));
                            }
                            path.push(Frame {
                                alts,
                                conflict: Conflict::default(),
                                up: at,
                            });
                            todo = push(&todo, (head, pos, Some(d)));
                        } else {
                            // An empty disjunction (or a negated empty conjunction) is false.
                            break 'run Some(Conflict::of(&[at]));
                        }
                    }
                }
                // The branch's own rows count too: `read` takes them only where the branch is
                // cut or ends, and `f` is a DAG walked as a tree, so one branch can take rows
                // past any bound in the size of `f` (a kept conjunction used at many places,
                // `Formula::and_keeping`). Without `took` here the walk was bounded by the
                // unfolded tree of `f`, not by `room` (LIMITS-shared-step-allowance; test
                // `tests::quick_search_stops_at_its_room_on_a_branch_longer_than_its_formula`).
                if read + took > room {
                    read += took;
                    break 'run None;
                }
            }
            let mut leaf = Vec::new();
            let mut at = &rows;
            while let Some(node) = at {
                leaf.push(node.0.clone());
                at = &node.1;
            }
            read += leaf.len() as u64;
            work.read(read - charged)?;
            charged = read;
            if read > room {
                break 'run None;
            }
            let point_of = work.solver.point_of;
            if let Some(m) = work.metered(|| point_of(&leaf, false))?
                && holds_as(f, &m, &mut HashMap::new())
                && within.is_none_or(|g| holds_as(g, &m, &mut HashMap::new()))
            {
                unwind(rows);
                unwind(todo);
                path.into_iter().for_each(drop_frame);
                return Ok(Quick::Point(m));
            }
            leaf_without_point = true;
            // A failure with no explanation: every decision of the path.
            Some(Conflict {
                upto: path.len().checked_sub(1),
                tips: BTreeSet::new(),
            })
        };
        unwind(rows);
        unwind(todo);
        drop(bounds);
        let Some(mut failed) = failed else {
            work.read(read - charged)?;
            path.into_iter().for_each(drop_frame);
            return Ok(Quick::Unknown);
        };
        // Back to the deepest decision of the conflict (`cbj-unlabel`); the decisions below
        // it are passed over with their disjuncts left untried.
        next = loop {
            let Some(d) = failed.deepest() else {
                // No decision: every branch fails.
                break None;
            };
            path.drain(d + 1..).for_each(drop_frame);
            let frame = &mut path[d];
            frame.conflict.join(failed);
            if let Some(b) = frame.alts.pop() {
                break Some(b);
            }
            let Frame { conflict, up, .. } = path.pop().expect("the decision `d` is on the path");
            failed = conflict;
            failed.without(d, up);
        };
    }
    work.read(read - charged)?;
    path.into_iter().for_each(drop_frame);
    Ok(if leaf_without_point {
        Quick::Unknown
    } else {
        Quick::Empty
    })
}

/// Whether every part of [`split`] has a point: a part where a cover found one has, and each
/// other is shown so by [`quick_point`], by [`direct`] where it reads the part exactly, or by a
/// question. Checked once for the call, after the covers, in the order of the parts, so the
/// same for every order of `syms`; its work has its own limit, as a cover has, and past it
/// every answer is refused ([`Refusal::Questions`]). A call on fewer symbols checks the same
/// parts or more, so it refuses wherever a call on more of them does.
fn has_points(
    parts: &[Piece],
    points: &mut [Vec<Model>],
    small: &[Option<(Formula, u64)>],
    shown: &[bool],
    work: &mut Work,
) -> Result<bool, Refusal> {
    let none = Atom::Sym("#none".into());
    // The fast paths' allowance, the same work limit as the questions (`tried`, `POLY-nf-work`).
    let mut fast = work.limit;
    let all = parts.iter().zip(points.iter_mut()).zip(small).zip(shown);
    for (((p, found), small), shown) in all {
        if !found.is_empty() || *shown {
            continue;
        }
        // The part's smaller formula, with a point exactly where the part has one (`reduced`),
        // is asked in its place; a point of it is not one of the part, so it is not kept.
        let (f, size) = match small {
            Some((g, size)) => (g, *size),
            None => (&p.f, p.size),
        };
        let mut keep = |m: Model| {
            if small.is_none() {
                found.push(m);
            }
        };
        if p.factors.is_empty()
            && let Some(m) = quick_point(f, 2 * (size + 2), work)?
        {
            keep(m);
            continue;
        }
        if p.factors.is_empty()
            && let Some(set) = tried(&mut fast, work.solver, |w| {
                direct(f, &none, &IntervalSet::top(), w)
            })
        {
            if set.is_empty() {
                return Ok(false);
            }
            continue;
        }
        work.read(size)?;
        EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
        match work.ask(f)? {
            None => return Ok(false),
            Some(m) => keep(m),
        }
    }
    Ok(true)
}

/// The values of `s` with a point of `f`, given `h`, a set holding them all: the cover of the
/// module note. `points` are points of `f` found before, for this symbol or another, and
/// those found here are added to them. Refused where a question is refused (for its cause)
/// and past the work limit ([`Refusal::Questions`]). Where the values have holes without end,
/// which no set of ranges holds, the piece holding them is kept whole and the answer comes
/// with `true`, wider than exact for that cause ([`Refusal::Repeats`]). The set comes with a
/// class where [`direct`] reads it as ranges met with one ([`Classed`]); every other answer
/// is ranges alone.
/// `fast` is the allowance of `direct` (`tried`), the limit less what `exact_each` charged the
/// symbol for the reading of its part; the loop has `work`'s limit, whatever `fast` is.
#[expect(
    clippy::too_many_arguments,
    reason = "the fast allowance is apart from `work` so that the loop's limit is not charged by the reading"
)]
fn cover(
    f: &Formula,
    s: &Atom,
    h: &IntervalSet,
    size: u64,
    factors: &HashSet<Atom>,
    points: &mut Vec<Model>,
    cache: &mut PartCache,
    fast: u64,
    work: &mut Work,
) -> Result<(Classed, bool), Refusal> {
    // No value has a point where the solver's set, which holds every value with one, is empty.
    if h.is_empty() {
        return Ok((Classed::plain(IntervalSet::empty()), false));
    }
    // The exact projection read from the structure of `f`, with no question (`direct`). It lies
    // within `h` where `f` is the whole formula; for a part of it (`split`) it may not, where
    // another part has no point, and then every answer is made empty (`exact_each`). So it may
    // be met with the hull of `h` where that helps a block end (`block_set`). The solver finds
    // such an `f` empty before the cover runs in every case tried, so the test that reaches
    // this case gives `exact_each` sets that miss it (`tests::a_part_split_off_gets_the_same_
    // answer_with_and_without_direct`, which also compares `direct` on and off).
    // A symbol outside the atoms of a block that `direct` noted for an earlier symbol of the
    // part gets no answer from it (`direct_noting`), so it is not run ([`PartCache`]).
    let given = fast;
    let mut fast = fast;
    if factors.is_empty()
        && !DIRECT_OFF.get()
        && !(cache.direct_fails.iter()).any(|(b, upto)| given <= *upto && !b.contains(s))
        && let Some(set) = tried(&mut fast, work.solver, |w| {
            let mut fails = None;
            let got = direct_noting(f, s, &h.hull(), w, &mut fails);
            let upto = |refused: bool| if refused { given } else { u64::MAX };
            (cache.direct_fails).extend(fails.map(|(b, refused)| (b, upto(refused))));
            got
        })
    {
        return Ok((set, false));
    }
    let (set, kept) = cells_cover(f, s, h, size, factors, points, cache, work)?;
    Ok((Classed::plain(set), kept))
}

/// What the covers of one part's symbols learn that does not read the symbol, kept for the
/// later symbols of the part, which reach the same step at the same work and so get the same
/// outcome at the same charge: `quick` is [`quick_point`]'s outcome where it found no point
/// (the units it charged) or was refused, asked at no work used; `whole` is the question of
/// `f` alone (the gap every value, no point found), with the work used when it was asked, and
/// its units where it found no point, or its refusal; `direct_fails` holds the atoms
/// [`direct_noting`] noted, outside which no symbol of the part gets an answer from it, each
/// with the largest allowance it holds for (every allowance where the note is of a block whose
/// elimination does not end, the allowance of the run where it is of a refusal); `refused`
/// counts the symbols refused by `quick` or `whole`, steps that do not read the symbol.
/// The same outcome needs the same work and the same limit too: `quick` is used only at no
/// work used and `whole` only at the work used when it was asked, and every symbol's loop runs
/// under the one `limit` of the call ([`exact_each_checked`]), so a step reached again starts
/// where it did and stops where it did. Test: `tests::the_covers_answer_alike_with_and_without_
/// what_the_symbols_before_learned_part_*` (`PART_CACHE_OFF`); random formulas over four
/// symbols seldom reach these steps, so it cannot catch an outcome reused where the step reads
/// the symbol after all.
// Complexity tradeoff: naive version, each of the k symbols of a part runs `quick_point`,
// `direct` and asks `f` alone again, O(k·|f|) where `|f|` is O(k): at 1,024 symbols in
// `disjoint::bench::the_join_of_arms_on_many_disjoint_refused_groups_reduced_scales`, 4.9 s in
// `direct` (513 runs, each refused at the same step) and the covers 2.9 s at 256 symbols, each
// symbol refused alike. Used: each run once a part (twice for `direct`, whose allowances take
// two values, `charge` in [`exact_each_checked`]), the rest O(1) a symbol and O(1) a note
// checked, a note made only by a run that costs at least the reading of `f`; every answer and
// refusal is the one the symbol's own run gives (from the Gemini 4 Neon seat of
// PRES-cover-hybrid, `PartCache`, its proof checked against this code).
#[derive(Default)]
struct PartCache {
    quick: Option<Result<u64, Refusal>>,
    whole: Option<(u64, Result<u64, Refusal>)>,
    direct_fails: Vec<(HashSet<Atom>, u64)>,
    refused: u64,
}

/// [`cover`] by cells and questions, once [`direct`] has not answered.
#[expect(
    clippy::too_many_arguments,
    reason = "the cache is kept by the part, apart from the points of `f` it holds"
)]
fn cells_cover(
    f: &Formula,
    s: &Atom,
    h: &IntervalSet,
    size: u64,
    factors: &HashSet<Atom>,
    points: &mut Vec<Model>,
    cache: &mut PartCache,
    work: &mut Work,
) -> Result<(IntervalSet, bool), Refusal> {
    let mut found = IntervalSet::empty();
    let mut gap = h.clone();
    let within = h.hull();
    let mut strides: Vec<Stride> = Vec::new();
    // The parts with holes and no end found by the cells, and the pieces with no end of their
    // union that ranges cannot hold (`projection::ranges`).
    let mut open: Vec<Strided> = Vec::new();
    let mut tails: Vec<Tail> = Vec::new();
    // The pieces of the tails whose holes repeat without end, each with its residues: the
    // values there with a point of `f` are exactly those residues' ([`ended`]).
    let mut kept: Vec<Kept> = Vec::new();
    let mut read = 0;
    // A first point without a question where one comes soon (`quick_point`): every point of
    // `f` has `s` in `h`, so its cell is read as a question's point would be. Its outcome where
    // it finds none does not read `s`, so a later symbol of the part, starting from the same
    // work, gets it from `cache` at the same charge ([`PartCache`]).
    if points.is_empty() && factors.is_empty() {
        let fresh = work.used == 0;
        match &cache.quick {
            Some(Ok(units)) if fresh => work.charge(*units)?,
            Some(Err(e)) if fresh => {
                cache.refused += 1;
                return Err(e.clone());
            }
            _ => match quick_point(f, 2 * (size + 2), work) {
                Ok(Some(m)) => points.push(m),
                Ok(None) => {
                    if fresh {
                        cache.quick = Some(Ok(work.used));
                    }
                }
                Err(e) => {
                    if fresh {
                        cache.quick = Some(Err(e.clone()));
                        cache.refused += 1;
                    }
                    return Err(e);
                }
            },
        }
    }
    loop {
        while read < points.len() && !gap.is_empty() {
            let m = points[read].clone();
            read += 1;
            if gap.contains_end(&fin(&value(&Lin::atom(s.clone()), &m))) {
                work.read(size)?;
                let (mut c, more, holed) = cell(f, &m, s, factors, &within, work)?;
                if !holed.is_empty() {
                    // The parts with holes and no end of every cell so far, joined: where the
                    // values found fill a tail up to an end, the values left of it are listed.
                    open.extend(holed);
                    let (filled, left) = projection::ranges(&open, work)?;
                    c = c.join(&filled);
                    let known = found.join(&c);
                    tails.clear();
                    let mut listed = Vec::new();
                    for t in left {
                        // The difference below reads each piece of `known` inside the tail's
                        // piece and builds a set of the holes between them, about 1 µs a piece
                        // (482 ms for 489,580 pieces in the cover above `LISTED`), before any
                        // value is listed or charged: charged first, [`PIECE`] units each, the
                        // count read in O(log p) from the two piece iterators' lengths.
                        if let Some((lo, hi)) = t.piece.bounds() {
                            let inside = known.pieces_from(lo).len()
                                - known.pieces_after(|p| p.0 <= *hi).len();
                            work.charge(PIECE.saturating_mul(inside as u64))?;
                        }
                        for (l, u) in t.piece.minus(&known).pieces() {
                            if let (End::Fin(l), End::Fin(u)) = (l, u) {
                                let (l, u) = (Int::from(l), Int::from(u));
                                projection::listed(&l, &u, &t.step, &t.have, work, &mut listed)?;
                            } else {
                                let piece = IntervalSet::range(l.clone(), u.clone());
                                tails.push(Tail {
                                    piece,
                                    step: t.step.clone(),
                                    have: t.have.clone(),
                                });
                            }
                        }
                    }
                    c = c.join(&IntervalSet::from_pieces(listed));
                }
                // The cell cut from the gap and joined to the values found, charged first,
                // [`PIECE`] units for each of its pieces and one more.
                // Complexity tradeoff: naive version, uncharged, its share left to the charges
                // of what made the cell's pieces; a cell of 2,000 pieces took 1.35 ms here at
                // load 50 (675 ns a piece), and its cover ran 1.4 times its prediction (the
                // benchmark of PRES-cover-time-per-unit, cover 0, PRES-work-charge-fit). Used:
                // `O(m log(n/m + 1))` for a cell of m pieces and sets of n, as `minus` and
                // `join` say, charged 16 units (1.28 µs predicted) a piece of the cell, the
                // count read in O(1).
                work.charge(PIECE.saturating_mul(c.len() as u64 + 1))?;
                gap = gap.minus(&c);
                found = found.join(&c);
                strides.extend(more);
            }
        }
        if gap.is_empty() {
            return ended(found, kept, work);
        }
        // The residue question of a piece with holes and no end: a point of `f` there in a
        // residue no part found holds. Where there is none, the values of `s` there are those
        // residues alone, holes without end, which ranges cannot hold: refused.
        if let Some(tail) = tails.pop() {
            if gap.meet(&tail.piece).is_empty() {
                continue;
            }
            let other = IntervalSet::from_pieces(
                (tail.have.iter().enumerate())
                    .filter(|(_, b)| !**b)
                    .map(|(r, _)| (End::from(r as i64), End::from(r as i64)))
                    .collect(),
            );
            work.question(size + 4)?;
            EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
            let (t, j) = (Atom::Sym("#t".into()), Atom::Sym("#j".into()));
            let lin = Lin {
                terms: [
                    (s.clone(), Int::from(1)),
                    (t, -&tail.step),
                    (j.clone(), Int::from(-1)),
                ]
                .into_iter()
                .collect(),
                constant: Int::from(0),
            };
            let q = Formula::and(vec![
                f.clone(),
                super::member(s, &tail.piece),
                Formula::Con(Con { lin, rel: Rel::Eq }),
                super::member(&j, &other),
            ]);
            match work.ask(&q)? {
                Some(m) => points.push(m),
                // Holes without end, which ranges cannot hold: the values of `s` in the tail's
                // piece are exactly those of its residues, kept with them; the answer is then
                // read from the exact set alone ([`ended`]), wider than exact for that cause,
                // given with it ([`exact_each`]).
                None => {
                    let left = gap.meet(&tail.piece);
                    let have: Rc<[bool]> = tail.have.into();
                    kept.extend(left.pieces().map(|(lo, hi)| Kept {
                        lo: lo.clone(),
                        hi: hi.clone(),
                        step: tail.step.clone(),
                        have: have.clone(),
                    }));
                    gap = gap.minus(&left);
                }
            }
            continue;
        }
        // The residue question of a progression: a point of `f` with `s` between its first and
        // last values and in a residue class modulo its step that no value found there is in.
        // Where there is none, every piece of the gap there shorter than the step, with no
        // value in such a class, is dropped at once: the odd values between the even ones of a
        // stride, which one question for each would cost as many questions as the answer has
        // pieces.
        // The question takes one piece of those classes, the first, so that it holds no
        // disjunction of residues; a piece with no point is kept in the stride's `absent`, and
        // the stride is asked again for the next piece, until every class no value found is in
        // has been asked and found empty: then the pieces of the gap are dropped as above.
        // Complexity tradeoff: naive version, one question with the residues no value found is
        // in, `j` in their union of q pieces, a disjunction of q intervals that the solver
        // splits on: on `REMAINDER_SHAPES`' "a test of the chain" at modulus 7, seed 3, k = 5
        // (s22, FAIL-s22-cover-moduli-5-7), the question of the residues {1..3} ∪ {5..6} cost
        // 1,421,700 units where that of {1..3} alone cost 319,600, and the cover was refused at
        // the limit. Used: one question a piece, its answer the same set of points; a stride
        // asks at most one question for each class a point is then found in (as before) and one
        // for each piece found empty, at most `step` questions a stride where before it asked
        // one fewer than the classes found plus one, so at most `step` more questions where
        // every piece is one class and none has a point. The questions are no larger, each `f`
        // and four rows. On s22's cases at moduli 5 and 7, 6 of the 22 cases refused before
        // are answered, and no case answered before is refused
        // (`s22::the_cover_answers_where_the_solver_alone_answered_on_three_shapes_at_moduli_5_and_7`).
        if let Some(mut st) = strides.pop() {
            let have = residues(&found, &st, work)?;
            let all = IntervalSet::range(fin(&Int::from(0)), fin(&(&st.step - &Int::from(1))));
            let other = all.minus(&have).minus(&st.absent);
            let Some((a, b)) = other.first().cloned() else {
                // Every class with no value found has no point here: the pieces between the
                // values found are dropped. With `absent` empty, every class has a value.
                if !st.absent.is_empty() {
                    gap = gap.minus(&outside(&gap, &st, &have, work)?);
                }
                continue;
            };
            let first = IntervalSet::range(a, b);
            work.question(size + 4)?;
            EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
            let (t, j) = (Atom::Sym("#t".into()), Atom::Sym("#j".into()));
            let lin = Lin {
                terms: [
                    (s.clone(), Int::from(1)),
                    (t, -&st.step),
                    (j.clone(), Int::from(-1)),
                ]
                .into_iter()
                .collect(),
                constant: Int::from(0),
            };
            let span = IntervalSet::range(fin(&st.lo), fin(&st.hi));
            let q = Formula::and(vec![
                f.clone(),
                super::member(s, &span),
                Formula::Con(Con { lin, rel: Rel::Eq }),
                super::member(&j, &first),
            ]);
            // A refusal of this question for another cause leaves the gap to the questions by
            // piece; past the work limit, the cover stops here at once.
            match work.ask(&q) {
                Err(_) if work.used > work.limit => return Err(Refusal::Questions),
                Err(_) => {}
                Ok(None) => {
                    st.absent = st.absent.join(&first);
                    strides.push(st);
                }
                Ok(Some(m)) => {
                    points.push(m);
                    strides.push(st);
                }
            }
            continue;
        }
        // One piece of the gap at a time, so that each question is `f` and two bounds: asked
        // with the whole gap, a question after k cells carries the k holes they made, and k
        // cells cost O(k^2) (the even values of `x == 2 * y` in a box, `exact::tests`).
        let Some(piece) = gap.first().cloned() else {
            return ended(found, kept, work);
        };
        // With no point found and the gap every value, the question is `f` alone, which does
        // not read `s`; a later symbol of the part reaching it at the same work gets its
        // outcome from `cache` at the same charge ([`PartCache`]).
        let whole = points.is_empty() && piece == (End::NegInf, End::PosInf);
        let start = work.used;
        match &cache.whole {
            Some((at, Ok(units))) if whole && *at == start => {
                work.charge(*units)?;
                gap = IntervalSet::empty();
                continue;
            }
            Some((at, Err(e))) if whole && *at == start => {
                cache.refused += 1;
                return Err(e.clone());
            }
            _ => {}
        }
        let piece = IntervalSet::range(piece.0, piece.1);
        let asked = (|| {
            work.question(size + 2)?;
            EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
            let q = Formula::and(vec![f.clone(), super::member(s, &piece)]);
            work.ask(&q)
        })();
        match asked {
            Ok(None) => {
                if whole {
                    cache.whole = Some((start, Ok(work.used - start)));
                }
                gap = gap.minus(&piece);
            }
            Ok(Some(m)) => points.push(m),
            Err(e) => {
                if whole {
                    cache.whole = Some((start, Err(e.clone())));
                    cache.refused += 1;
                }
                return Err(e);
            }
        }
    }
}

/// A piece of a tail kept by [`cover`], an interval from `lo` to `hi`, where the values of `s`
/// with a point of `f` are exactly those whose residue modulo `step` is marked in `have`: the
/// tail's residue question found no point there in another residue, and each marked value is
/// one of a strided part that holds over the whole piece (`projection::ranges`).
struct Kept {
    lo: End,
    hi: End,
    step: Int,
    have: Rc<[bool]>,
}

/// A residue table `have` modulo `step` read as a periodic set of integers, with the nearest
/// residue at or below and at or above each residue that is in the set and that is out of it,
/// so that the nearest member or nonmember of any value is read in O(1). The table of a tail
/// has both: a strided part holds, and not every residue (`projection::ranges` makes no tail
/// where every residue is marked).
struct Periodic {
    step: Int,
    have: Rc<[bool]>,
    /// `below[b][r]`: the greatest residue `r' <= r` with `have[r'] == b`, if any.
    below: [Vec<Option<usize>>; 2],
    /// `above[b][r]`: the least residue `r' >= r` with `have[r'] == b`, if any.
    above: [Vec<Option<usize>>; 2],
}

impl Periodic {
    /// The tables of `have`, charged as the residue tables of `projection::ranges` are, one
    /// unit for each 64 residues.
    fn new(step: &Int, have: &Rc<[bool]>, work: &mut Work) -> Result<Self, Refusal> {
        let n = have.len();
        work.charge(n as u64 / 64 + 1)?;
        debug_assert!(have.contains(&true) && have.contains(&false));
        let mut below = [vec![None; n], vec![None; n]];
        let mut above = [vec![None; n], vec![None; n]];
        let mut last = [None, None];
        for (r, &b) in have.iter().enumerate() {
            last[b as usize] = Some(r);
            below[0][r] = last[0];
            below[1][r] = last[1];
        }
        let mut next = [None, None];
        for (r, &b) in have.iter().enumerate().rev() {
            next[b as usize] = Some(r);
            above[0][r] = next[0];
            above[1][r] = next[1];
        }
        Ok(Periodic {
            step: step.clone(),
            have: have.clone(),
            below,
            above,
        })
    }

    fn residue(&self, v: &Int) -> usize {
        v.mod_floor(&self.step).to_i128().expect("a table's size") as usize
    }

    fn at(&self, v: &Int) -> bool {
        self.have[self.residue(v)]
    }

    /// The greatest value at or below `v` that is in the set (`b`) or out of it (`!b`).
    fn last(&self, b: bool, v: &Int) -> Int {
        let (r, n) = (self.residue(v), self.have.len());
        let to = |k: usize| Int::from(k as i64);
        match self.below[b as usize][r] {
            Some(q) => v - &to(r - q),
            None => {
                let q = self.below[b as usize][n - 1].expect("both kinds of residue");
                v - &to(r + n - q)
            }
        }
    }

    /// The least value at or above `v` that is in the set (`b`) or out of it (`!b`).
    fn first(&self, b: bool, v: &Int) -> Int {
        let (r, n) = (self.residue(v), self.have.len());
        let to = |k: usize| Int::from(k as i64);
        match self.above[b as usize][r] {
            Some(q) => v + &to(q - r),
            None => {
                let q = self.above[b as usize][0].expect("both kinds of residue");
                v + &to(n - r + q)
            }
        }
    }
}

/// The answer of [`cover`] once the gap is empty: `found`, exact, where no tail was kept;
/// else the set read from the exact set `E` of the values of `s` with a point alone, with
/// `true` for the cause ([`Refusal::Repeats`]): `E` where its values have no holes without
/// end, and each ray past the start of the period of those holes, whole.
///
/// Why `E` is known exactly here: `found` holds only values of `E` (each cell's values have
/// points); `h`, the cover's input, holds every value of `E`, and each piece of it left the
/// gap by a cell (into `found`), by a question that found no point there (a piece, or the
/// pieces of `outside`), or as a kept piece; in a kept piece `E` is exactly its residues
/// ([`Kept`]). So `E` is `found` outside the kept pieces and the residues inside them, and the
/// pieces are disjoint (each is taken out of the gap when it is kept).
///
/// The rule (PRES-cover-tail-writing; P246): where `E` has holes without end above, it equals
/// far above a periodic set `P`, the residues of the kept piece with no upper end (`E` there),
/// a set `E` alone fixes: `P = {v : v + k·T in E for every large k}` for any period `T`. Let
/// `p` be one more than the greatest value where `E` and `P` differ, and `u` the least value of
/// `E` at or above `p` (`E` has one, as `P` does): every value from `u` up is given, and below
/// it `E` as it is. The same below, read on the values negated. So the answer is
/// `(-inf, l] ∪ (E ∩ (l, u)) ∪ [u, +inf)`, `(-inf, +inf)` where the two rays meet, a function
/// of `E` alone, which holds `E` and is exact outside the two rays. Kept pieces exist exactly
/// when `E` has holes without end (a tail is kept only when its residue question proves them,
/// and where `E` has them the gap there cannot be emptied otherwise: a finite union of ranges
/// is not `E` there, a question on a piece drops only an empty piece and one on a progression
/// only pieces between its finite ends), so the cause is a function of `E` too. Every writing
/// of one formula that the cover answers then gets one set and one cause, whatever the
/// solver's `h` and whatever order the cells came in. Before, each piece of `h` holding a kept
/// piece was given whole, and `h` depends on the writing: formula 67 of seed
/// 15455823323744612893 in `l01_38_presburger::shared` (the even integers) got `(-inf, -2] ∪
/// [0, +inf)` as written and `(-inf, +inf)` with a shared part taken out.
///
/// The price: where the solver's `h` leaves out a value inside a ray, the answer holds it (the
/// even integers above get `(-inf, +inf)`, not the `h` above), since no such cut is fixed by
/// `E`: any set of ranges holding the even integers holds a ray each way, and which odd values
/// it leaves out is not fixed by them.
// Complexity tradeoff: naive, every piece of `h` holding a kept piece given whole, O(q log q)
// for `q` pieces of `h`, but an answer that depends on `h`. Used: one walk down from the kept
// piece with no upper end and one up from the one with no lower end, each stopping at the
// first value where `E` and the period differ: O(1) for each piece of `found` passed (O(log p)
// to find it, `p` pieces of `found`), one table of the period, made in O(T) and charged as
// `projection::ranges` charges its own, and for each kept piece passed with another period a
// scan of at most the lcm of the two periods, charged before it at the same rate; then the
// values of each kept piece between the rays listed, each charged [`LISTED`]
// (`projection::listed`). In all O((p + k) log p + k·L) for k kept pieces and L the largest
// lcm, where before O(q log q).
fn ended(
    found: IntervalSet,
    mut kept: Vec<Kept>,
    work: &mut Work,
) -> Result<(IntervalSet, bool), Refusal> {
    if kept.is_empty() {
        return Ok((found, false));
    }
    kept.sort_by(|a, b| a.lo.cmp(&b.lo));
    let up = ray_from(&found, &kept, work)?;
    let negated: Vec<Kept> = (kept.iter().rev())
        .map(|k| {
            let n = k.have.len();
            Kept {
                lo: negated_end(&k.hi),
                hi: negated_end(&k.lo),
                step: k.step.clone(),
                have: (0..n).map(|r| k.have[(n - r) % n]).collect(),
            }
        })
        .collect();
    let down = ray_from(&found.neg(), &negated, work)?.map(|u| u.map(|u| -&u));
    let (l, u) = match (down, up) {
        (Some(None), _) | (_, Some(None)) => return Ok((IntervalSet::top(), true)),
        (Some(Some(l)), Some(Some(u))) if &l + &Int::from(1) >= u => {
            return Ok((IntervalSet::top(), true));
        }
        (l, u) => (l.flatten(), u.flatten()),
    };
    let between = IntervalSet::range(
        l.as_ref()
            .map_or(End::NegInf, |l| fin(&(l + &Int::from(1)))),
        u.as_ref()
            .map_or(End::PosInf, |u| fin(&(u - &Int::from(1)))),
    );
    let mut pieces: Vec<(End, End)> = found.meet(&between).into_pieces();
    if let Some(l) = &l {
        pieces.push((End::NegInf, fin(l)));
    }
    if let Some(u) = &u {
        pieces.push((fin(u), End::PosInf));
    }
    // A kept piece between the rays is bounded: one with no upper end holds the start of the
    // upper ray's period or lies past it (`ray_from`), and the same below.
    for k in &kept {
        let inside = IntervalSet::range(k.lo.clone(), k.hi.clone()).meet(&between);
        for (a, b) in inside.pieces() {
            let (End::Fin(a), End::Fin(b)) = (a, b) else {
                unreachable!("a kept piece between the rays is bounded");
            };
            projection::listed(
                &Int::from(a),
                &Int::from(b),
                &k.step,
                &k.have,
                work,
                &mut pieces,
            )?;
        }
    }
    Ok((IntervalSet::from_pieces(pieces), true))
}

fn negated_end(e: &End) -> End {
    match e {
        End::NegInf => End::PosInf,
        End::PosInf => End::NegInf,
        End::Fin(v) => End::Fin(-v),
    }
}

/// For [`ended`]: where the values `E` of `s` have holes without end above (a kept piece with no
/// upper end, `kept` sorted and disjoint), the least value `u` of `E` from which `E` agrees
/// with its period at every value, `None` in it where `E` is that period everywhere; `None`
/// where `E` has no such holes above. `E` is read as [`ended`] says: in a kept piece its
/// residues, elsewhere `found`.
fn ray_from(
    found: &IntervalSet,
    kept: &[Kept],
    work: &mut Work,
) -> Result<Option<Option<Int>>, Refusal> {
    let Some(top) = kept.last().filter(|k| k.hi == End::PosInf) else {
        return Ok(None);
    };
    let p = Periodic::new(&top.step, &top.have, work)?;
    let End::Fin(lo) = &top.lo else {
        return Ok(Some(None));
    };
    let one = Int::from(1);
    // `cur`: every value above it agrees with `P`; the kept pieces below it are those of
    // `kept[..next]`, each wholly below it (they are disjoint from the ones passed).
    let mut cur = &Int::from(lo) - &one;
    let mut next = kept.len() - 1;
    let differs = loop {
        // The values from `cur` down to the next kept piece are `found`'s: a value of a piece
        // of `found` differs from `P` at a value out of `P`, a value between two pieces at one
        // in `P`, so each run is read in O(1) by `P`'s tables.
        let below = next.checked_sub(1).map(|i| &kept[i]);
        let floor = below.map_or(End::NegInf, |k| k.hi.clone());
        let mut w = cur.clone();
        let mut hit = None;
        while fin(&w) > floor {
            let (inside, start) = match found.piece_at_or_below(&fin(&w)) {
                Some((a, b)) if *b >= fin(&w) => (true, a.clone()),
                Some((_, b)) => (false, b.succ()),
                None => (false, End::NegInf),
            };
            let start = start.max(floor.succ());
            let d = p.last(!inside, &w);
            if fin(&d) >= start {
                hit = Some(d);
                break;
            }
            let End::Fin(s) = start else {
                unreachable!("a run with no lower end holds a value of each kind of residue");
            };
            w = &Int::from(&s) - &one;
        }
        if hit.is_some() {
            break hit;
        }
        let Some(k) = below else {
            unreachable!("the run with no lower end returned above");
        };
        // A kept piece with other residues: compared with `P` from its top down, over at most
        // the lcm of the two periods (equal there, they are equal everywhere), charged first.
        let End::Fin(hi) = &k.hi else {
            unreachable!("a kept piece below another has an upper end");
        };
        let hi = Int::from(hi);
        let g = p.step.gcd(&k.step);
        let lcm = &p.step.div_floor(&g) * &k.step;
        let span = match &k.lo {
            End::Fin(a) => Some(&(&hi - &Int::from(a)) + &one),
            _ => None,
        };
        let count = match &span {
            Some(s) if *s < lcm => s.clone(),
            _ => lcm.clone(),
        };
        let n = count
            .to_i128()
            .and_then(|n| u64::try_from(n).ok())
            .unwrap_or(u64::MAX);
        work.charge(n / 64 + 1)?;
        let q = Periodic {
            step: k.step.clone(),
            have: k.have.clone(),
            below: [Vec::new(), Vec::new()],
            above: [Vec::new(), Vec::new()],
        };
        let mut v = hi.clone();
        let mut d = None;
        for _ in 0..n {
            if p.at(&v) != q.at(&v) {
                d = Some(v);
                break;
            }
            v = &v - &one;
        }
        if d.is_some() {
            break d;
        }
        match &k.lo {
            End::Fin(a) => cur = &Int::from(a) - &one,
            _ => return Ok(Some(None)),
        }
        next -= 1;
    };
    let d = differs.expect("a value that differs");
    Ok(Some(Some(p.first(true, &(&d + &one)))))
}

/// A part of `f` as [`direct`] reads it: a conjunction of constraints not yet projected, so
/// that a conjunction above it can project it with the constraints beside it; or the exact
/// projection of the part onto the symbol, with the atoms other than the symbol it reads; or a
/// disjunction of conjunctions of constraints not yet projected (`Alts`, each block one
/// disjunct), so that a conjunction above it can project each block with the constraints beside
/// it (PRES-cover-refusals-moduli). A projected part and a disjunction of blocks come with
/// bounds that hold at every point of the part ([`Dirs`]; none is always sound). A shared
/// disjunction, projected, keeps its blocks (see `direct_noting`).
#[derive(Clone)]
enum Part {
    Rows(Vec<Con>),
    Set(Classed, HashSet<Atom>, Dirs, Option<Rc<[Vec<Con>]>>),
    Alts(Vec<Vec<Con>>, Dirs),
}

/// Bounds on terms that hold at every point of a part: for each term (a row's terms, its sign
/// fixed so that the first coefficient is positive), the least and greatest values it takes
/// there, as far as they are known (each end `None` where it is not). A term absent has no
/// bound known. [`met`] reads them to drop a disjunction that the other conjuncts imply.
type Dirs = HashMap<BTreeMap<Atom, Int>, Ends>;

/// The term of `c`, its sign fixed so that its first coefficient is positive, with the bounds
/// `c` puts on it; `None` for a row with no atom.
fn dir_of(c: &Con) -> Option<(BTreeMap<Atom, Int>, Ends)> {
    let first = c.lin.terms.values().next()?;
    let k = &c.lin.constant;
    Some(if first.is_positive() {
        // `t + k >= 0` is `t >= -k`; `t + k == 0` is `t == -k`.
        let v = -k;
        let ends = match c.rel {
            Rel::Ge => (Some(v), None),
            Rel::Eq => (Some(v.clone()), Some(v)),
        };
        (c.lin.terms.clone(), ends)
    } else {
        // With `u = -t`: `-u + k >= 0` is `u <= k`; `-u + k == 0` is `u == k`.
        let terms = (c.lin.terms.iter()).map(|(a, v)| (a.clone(), -v)).collect();
        let ends = match c.rel {
            Rel::Ge => (None, Some(k.clone())),
            Rel::Eq => (Some(k.clone()), Some(k.clone())),
        };
        (terms, ends)
    })
}

/// The bounds that hold at every point of the conjunction `rows`.
fn dirs_of(rows: &[Con]) -> Dirs {
    let mut d = Dirs::new();
    for (t, e) in rows.iter().filter_map(dir_of) {
        let met = d
            .get(&t)
            .map_or_else(|| e.clone(), |old| range_meet(old, &e));
        d.insert(t, met);
    }
    d
}

/// `a` met with `b`: the bounds of a conjunction of two parts, each of which holds at every
/// point of it. O(|b|).
fn dirs_meet(a: &mut Dirs, b: Dirs) {
    for (t, e) in b {
        let met = a
            .get(&t)
            .map_or_else(|| e.clone(), |old| range_meet(old, &e));
        a.insert(t, met);
    }
}

/// The bounds of a disjunction of two parts with bounds `a` and `b`: the terms bounded in both,
/// each end the wider of the two, a term with neither end dropped. O(min(|a|, |b|)).
fn dirs_join(a: Dirs, b: Dirs) -> Dirs {
    let (small, big) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    let mut out = Dirs::new();
    for (t, (l1, h1)) in small {
        let Some((l2, h2)) = big.get(&t) else {
            continue;
        };
        let lo = l1.zip(l2.clone()).map(|(x, y)| x.min(y));
        let hi = h1.zip(h2.clone()).map(|(x, y)| x.max(y));
        if lo.is_some() || hi.is_some() {
            out.insert(t, (lo, hi));
        }
    }
    out
}

/// Whether every point where the bounds `d` hold satisfies `c`: its term's bound in `d` lies
/// within what `c` asks (a row with no atom: its constant).
fn implied(c: &Con, d: &Dirs) -> bool {
    let Some((t, (lo, hi))) = dir_of(c) else {
        return match c.rel {
            Rel::Ge => !c.lin.constant.is_negative(),
            Rel::Eq => c.lin.constant == Int::ZERO,
        };
    };
    let Some((dl, dh)) = d.get(&t) else {
        return false;
    };
    let above = lo.is_none_or(|l| dl.as_ref().is_some_and(|x| *x >= l));
    let below = hi.is_none_or(|h| dh.as_ref().is_some_and(|x| *x <= h));
    above && below
}

/// `run`, a fast path, given what is left of `fast`, the fast paths' own allowance (the work
/// limit `L`, set by the caller: [`exact_each_checked`] gives each symbol `L` less its even
/// share of the part's reading, `limit - charge(..)`, and `has_points` starts at
/// `work.limit`; corrected 2026-11-20 from "a quarter of the limit", which predates the change
/// described below): its answer, or `None` where it fails
/// or passes that allowance. Its work is counted in [`EXACT_WORK`] and [`FAST_WORK`] and taken
/// from `fast`, never from `work`, so the complete method after it (the loop of [`cover`], or
/// the questions of [`has_points`]) runs with the same limit and the same work as with no fast
/// path, and refuses exactly where it would have.
// Complexity tradeoff: before, a failed fast path was charged to the limit, up to a quarter of
// the work left, so the loop could refuse a cover needing more than three quarters of the limit
// that it answers alone (`tests::the_work_limit_is_met_alike_on_both_sides`). Used: an
// allowance of its own equal to the same A99 work limit `L` as the complete method (as the
// factored fast path of `POLY-nf-power-value` in `COMPLEXITY.md` runs under its own budget of
// the limit before giving way to expansion), with no unmeasured fraction. When `direct` answers,
// the loop does not run, so total admitted work is at most `L`; when `direct` declines or passes
// `L`, the loop starts at `0` with limit `L`, so total admitted work per symbol is at most `2 * L`
// (each meter passing `L` by at most its single stopping charge), and the refusal boundary of
// the loop is identical to running with no fast path. Stopping at `*fast == 0` keeps a shared
// zeroed allowance (`has_points`) from walking remaining parts. The loop is the lazy model
// enumeration of Monniaux, "Quantifier Elimination by Lazy Model Enumeration", CAV 2010,
// sec. 2.2 (block `¬π(C_i)`, the projection of each implicant, not `¬C_i`) and sec. 3
// (Algorithm 2, the same loop done lazily; with one existential block it is the loop of sec.
// 2.2), doi:10.1007/978-3-642-14295-6_51, with model-based cells after Bjørner and Janota,
// "Playing with Quantified Satisfaction", LPAR-20, 2015, sec. 2.2 (Requirement 1: a cell
// holds at the model and implies the projection), doi:10.29007/vv21; both read 2026-11-21,
// the departures listed in the crate root's References; `direct` is Pugh's structural exact
// shadow, "A practical algorithm for exact array dependence analysis", CACM 35(8), 1992,
// doi:10.1145/135226.135233, the section on integer solutions by Fourier-Motzkin elimination
// (sec. 2.3.2 of the expanded text). Full
// citations, and how each was checked, are in the crate root's References.
fn tried<T>(
    fast: &mut u64,
    solver: Solver,
    run: impl FnOnce(&mut Work) -> Result<Option<T>, Refusal>,
) -> Option<T> {
    if *fast == 0 {
        return None;
    }
    let mut part = Work {
        used: 0,
        limit: *fast,
        solver,
    };
    let got = run(&mut part);
    FAST_WORK.set(FAST_WORK.get().saturating_add(part.used));
    *fast = fast.saturating_sub(part.used);
    got.ok().flatten()
}

/// The names of `mine` the forward certificate answers, with their sets, each name's work
/// taken from `left` as [`tried`] takes it.
// Complexity tradeoff: naive version, each name's certificate its own, O(r·t) for its reading
// and again for each piece of `h`, so O(k·r·t) for the k names of a part: on a chain of unit
// equations, k = r, 61 times the work at 8 times k
// (`tests::the_names_of_a_chain_of_unit_equations_are_certified_together`). Used: the classes
// of names tied by equations of two atoms with coefficients 1 or -1, built once a part in
// O(r·α(a)) (`guarded::ties`), one certificate for each class and O(P) to move its set to each
// other name, P pieces. A class whose first certificate declines is tried no more (before, each
// of its names was tried at O(r·t): 62.95 times at 8 times k on
// `tests::a_class_whose_certificate_declines_is_tried_once`). Names tied only through equations
// of three or more atoms, or with coefficients past 1, or through choices, are still each tried
// at O(r·t) (PRES-groupA-forward-per-name-order, part 2, open).
fn certificates<'s>(
    prep: &guarded::Prep,
    mine: &[(&'s Atom, &IntervalSet)],
    left: &mut u64,
    solver: Solver,
) -> Vec<(&'s Atom, Classed)> {
    let mut out = Vec::new();
    // The whole part read once with two pins (`guarded::two_pins`): each name's exact set from
    // the polygon, with no reading of its own; a name it declines goes on to the reading below.
    let two = tried(left, solver, |w| prep.two_pins(mine.len(), w));
    let mut rest: Vec<(&'s Atom, &IntervalSet)> = Vec::new();
    for &(s, h) in mine {
        match two
            .as_ref()
            .and_then(|t| tried(left, solver, |w| t.values(s, w)))
        {
            Some(set) => out.push((s, set)),
            None => rest.push((s, h)),
        }
    }
    let mine = &rest[..];
    // The first name of each class certified, by which the others of its class are answered
    // with no reading of their own (`Prep::carried`).
    let mut first: HashMap<usize, (&Atom, IntervalSet)> = HashMap::new();
    // The classes whose first try declined: the others of the class are left to the cover with
    // no try of their own. A name of the class differs from the one tried by a sign and a
    // shift, so its reading is the same but for that bijection and its certificate would
    // decline on the same residual; where it would not, the cover still answers it exactly, so
    // nothing but speed rests on this.
    let mut declined: HashSet<usize> = HashSet::new();
    for &(s, h) in mine {
        let class = prep.class(s);
        if class.is_some_and(|c| declined.contains(&c)) {
            continue;
        }
        if let Some((from, set)) = class.and_then(|c| first.get(&c))
            && let Some(set) = prep.carried(s, from, set)
        {
            out.push((s, Classed::plain(set)));
            continue;
        }
        match tried(left, solver, |w| guarded::forward_in(prep, s, h, w)) {
            Some(set) => {
                if let Some(c) = class {
                    first.insert(c, (s, set.clone()));
                }
                out.push((s, Classed::plain(set)));
            }
            None => {
                if let Some(c) = class {
                    declined.insert(c);
                }
            }
        }
    }
    out
}

/// The exact projection of `f` onto `s`, read from the structure of `f` with no question of
/// the solver; `None` where a step below is not shown exact, and the cover is then asked.
/// `f` has no product atom (the solver may read a product more tightly than as an atom of its
/// own, as [`cell`] notes). Each part is read with its sign (a negation flips it):
/// - a constraint is a row (a negated `t >= 0` is `-t - 1 >= 0`; a negated `t == 0` is the
///   union of the projections of `t - 1 >= 0` and `-t - 1 >= 0`);
/// - a disjunction projects to the union of its parts' projections, since a value has a point
///   of `A or B` exactly when it has one of `A` or one of `B`;
/// - a conjunction splits its parts into groups that share no atom but `s` (union-find). A
///   group of rows alone projects by [`super::eliminated`], whose rows over `s` hold exactly
///   where the group has a point (Pugh's exact projection, Pugh 1991/1992, sec. 2.3.2,
///   doi:10.1145/125826.125848 and doi:10.1145/135226.135233, in the crate root's
///   References); a group of one
///   projected part keeps its set; a group with a projected part and anything more is not
///   shown exact (`None`). The conjunction is the meet of its groups: given a point of each
///   group with `s` at `v`, the groups read disjoint atoms but `s`, so the points join into one
///   point of the conjunction; the other way is plain. A conjunction of rows alone stays rows,
///   so that the conjunction above it groups them with its own.
///
/// So every set it gives is the set of values of `s` with a point of `f`, the cover's answer.
// Complexity tradeoff: the cover asks the solver at least one question of the whole formula
// for each symbol, and a question cost up to 7.6 M units at 12,000 constraints, past the limit
// alone (R1 cross-review, `bench::omega::*`). Naive alternative: the disjunctive normal form,
// projected one conjunction at a time, exact but exponential in the disjunctions. Used: one
// pass over the parts, each shared part read once for each sign (`memo`), rows moved up, not
// copied, but for a shared part read again, whose rows are charged again. Each conjunction
// groups the rows moved up from below it again, so a nest of conjunctions k deep costs O(k n)
// for n rows: 448,000 units at 131 constraints 64 deep and past the limit at 1027 512 deep
// (`l01_38_presburger::nest_empty`), where the loop answers with no question. So it runs
// under an allowance of its own equal to the limit (`tried`), and the loop takes over
// past it. Each
// elimination charges its substitutions and bound pairs (`eliminated_counted`), and each
// constraint read is charged as the cover charges one. Not exact for a conjunction that ties a
// disjunction to other parts through a shared atom (`y == x + 1 and (x <= 3 or x >= 10)`), nor
// where a stride stops the elimination; those go to the cover (safe path, P246).
//
// PRES-cover-refusals-moduli (2026-11-18): the remainder chains of `s22` at moduli 5 and 7 give
// `R ∧ D ∧ (B1 ∨ ... ∨ Bk)`, rows `R` tied to the disjunction through the chain's quotient and
// remainder atoms, with `D` over `s` alone; the steps above returned `None` there, and the cover
// asked 9 to 40 questions of the whole formula, about 1.9 M units each (refused past the limit
// in 50 of 120 cases; 44 M units for the worst, whose answer is 44 values of a period of 14).
// Now a disjunction of blocks of rows is kept as blocks (`Part::Alts`), and a group of rows `R`
// with one such disjunction projects as the union of the projections of `R ∧ Bi` (exact, as
// above: a value has a point of `R ∧ (B1 ∨ ... ∨ Bk)` exactly when it has one of some `R ∧ Bi`),
// and a block whose elimination stops at a stride is projected by Pugh's exact projection
// ([`block_set`]). Naive alternative: the disjunctive normal form of the whole formula, a
// product over its disjunctions; here only a group with one disjunction is distributed, k
// copies of `R` for k blocks, which is the size of that group's normal form, every row of
// them charged, so the cost is O(k |R|) row reads plus the projections, under the allowance of
// `tried`. A group with exactly two disjunctions goes to [`two_distributed`] (its cost there);
// one with three or more is not distributed (`None`, the cover is asked).
fn direct_noting(
    f: &Formula,
    s: &Atom,
    within: &IntervalSet,
    work: &mut Work,
    fails: &mut Option<(HashSet<Atom>, bool)>,
) -> Result<Option<Classed>, Refusal> {
    enum Go<'a> {
        Read(&'a Formula, bool),
        Join(&'a Formula, bool),
    }
    // The parts held by more than one holder, the only ones a memo entry is kept for.
    let mut holders: HashMap<Id, u32> = HashMap::new();
    let mut stack = vec![f];
    while let Some(g) = stack.pop() {
        if let Some(k) = Id::of(g) {
            let n = holders.entry(k).or_insert(0);
            *n += 1;
            if *n > 1 {
                continue;
            }
        }
        match g {
            Formula::Con(_) => {}
            Formula::Not(h) => stack.push(h),
            Formula::And(gs) | Formula::Or(gs) => stack.extend(gs.iter()),
        }
    }
    // Whether no step so far read `s` (below).
    let mut pure = true;
    let mut memo: HashMap<(Id, bool), Part> = HashMap::new();
    let mut stack = vec![Go::Read(f, true)];
    let mut values: Vec<Part> = Vec::new();
    let read = (|| {
        while let Some(step) = stack.pop() {
            match step {
                Go::Read(g, pos) => {
                    if let Some(v) = Id::of(g).and_then(|k| memo.get(&(k, pos))) {
                        match v {
                            Part::Rows(rows) => work.read(rows.len() as u64)?,
                            Part::Alts(blocks, _) => {
                                work.read(blocks.iter().map(|b| b.len() as u64).sum())?
                            }
                            Part::Set(..) => {}
                        }
                        values.push(v.clone());
                        continue;
                    }
                    match g {
                        Formula::Con(c) => {
                            work.read(1)?;
                            values.push(match (pos, c.rel) {
                                (true, _) => Part::Rows(vec![c.clone()]),
                                (false, Rel::Ge) => Part::Rows(vec![negated(c, &Int::from(-1))]),
                                // `t != 0` is `t <= -1 or t >= 1`, two blocks, which bound
                                // `t` on no common side, so no bound holds on both.
                                (false, Rel::Eq) => Part::Alts(
                                    vec![
                                        vec![negated(c, &Int::from(-1))],
                                        vec![negated(c, &Int::from(1))],
                                    ],
                                    Dirs::new(),
                                ),
                            });
                        }
                        Formula::Not(h) => stack.push(Go::Read(h, !pos)),
                        Formula::And(gs) | Formula::Or(gs) => {
                            stack.push(Go::Join(g, pos));
                            stack.extend(gs.iter().rev().map(|h| Go::Read(h, pos)));
                        }
                    }
                }
                Go::Join(g, pos) => {
                    let (Formula::And(gs) | Formula::Or(gs)) = g else {
                        unreachable!("a join is pushed for a conjunction or a disjunction");
                    };
                    let parts = values.split_off(values.len() - gs.len());
                    let and = matches!(g, Formula::And(_)) == pos;
                    pure &= if and {
                        parts.iter().all(|p| matches!(p, Part::Rows(_)))
                    } else {
                        !parts.iter().any(|p| matches!(p, Part::Set(..)))
                    };
                    let v = if and {
                        met(parts, s, within, true, work)?
                    } else {
                        joined_parts(parts, s, within, work)?
                    };
                    let Some(mut v) = v else {
                        return Ok(None);
                    };
                    if let Some(k) = Id::of(g)
                        && holders.get(&k).is_some_and(|&n| n > 1)
                    {
                        // A shared disjunction is projected here, not kept as blocks: each holder
                        // would copy its blocks and distribute its own rows over them, so a chain
                        // of parts each holding the two before it (`l01_39_reduced_product`
                        // `arms_of_a_chain_of_named_conjunctions...`) grew as the number of paths,
                        // exponential in its length, until each call spent its allowance (past 60 s
                        // where 4.2 s before 94f38f6d3). Projected, it is one set read by each
                        // holder, as before; blocks stay unprojected only on parts read once.
                        // The blocks are kept with the set, shared, not copied: a holder that
                        // meets the set with rows reading its other atoms distributes those rows
                        // over them once, and gets a set (`met`), so no copy holds another.
                        if let Part::Alts(blocks, d) = v {
                            pure = false;
                            let Some((set, atoms)) = blocks_set(&blocks, s, within, work)? else {
                                return Ok(None);
                            };
                            v = Part::Set(set, atoms, d, Some(Rc::from(blocks)));
                        }
                        memo.insert((k, pos), v.clone());
                    }
                    values.push(v);
                }
            }
        }
        Ok(Some(()))
    })();
    // A refusal while every step is `pure` comes at the same work for every symbol, as no step
    // so far read `s` or `within` (a conjunction of rows and a disjunction with no set charge
    // nothing, and a read charges its rows): it is noted with no atoms, so no symbol of the part
    // is run again at this allowance or less (`PartCache`; with less, a run stops at the same
    // charge or before, as `Work::charge` and `metered` stop once past the limit).
    match read {
        Err(e) => {
            if pure {
                *fails = Some((HashSet::new(), true));
            }
            return Err(e);
        }
        Ok(None) => return Ok(None),
        Ok(Some(())) => {}
    }
    let last = values.pop().expect("the part of `f`");
    // A disjunction of blocks read with no step that reads `s` (`pure`): its blocks are the same
    // for every symbol, and its set is `None` where a block's is, else the join of theirs. The
    // blocks without `s` are projected first, then those with it, the sets joined in the order
    // of the blocks: with every block projected, the work is the same sum in either order, and
    // with one not, the set is `None` in either order. A block without `s` reads neither `s` nor
    // `within` in [`block_set`], so its outcome is the same for every symbol it lacks. One whose
    // elimination does not end is `None` for every symbol it lacks, at any allowance, so the
    // atoms of that block are noted (`fails`): no symbol outside them gets an answer here. One
    // refused is refused alike for every symbol none of the blocks without `s` up to it reads
    // (each of them lacks that symbol too, and its blocks before it without the symbol hold at
    // least those, each adding work or ending the run), so their atoms are noted as a refusal,
    // holding at this allowance or less.
    // Complexity tradeoff: naive version, the blocks in their order: on two blocks of k/2 rows
    // each (`disjoint::bench::the_join_of_arms_on_many_disjoint_refused_groups_reduced_scales`),
    // each symbol of the first was refused at its own block, spending its whole allowance, k/2
    // times, before the second block, whose elimination does not end for any of them, was read
    // (4.9 s of 5.2 s at 1,024 symbols). Used: the blocks without `s` first, O(1) more a block,
    // so the first symbol of the first block notes the second and the others are not run
    // (from the Gemini 4 Neon seat of PRES-cover-hybrid, `disjoint_uneliminable`, which tests
    // each block's groups once a part; here the blocks are read by the runs already made).
    if let (true, Part::Alts(blocks, _)) = (pure, &last) {
        let atoms = |bs: &mut dyn Iterator<Item = &Vec<Con>>| -> HashSet<Atom> {
            bs.flatten()
                .flat_map(|c| c.lin.terms.keys().cloned())
                .collect()
        };
        let reads = |b: &[Con]| b.iter().any(|c| c.lin.terms.contains_key(s));
        let mut sets: Vec<Option<Classed>> = vec![None; blocks.len()];
        for (i, b) in blocks.iter().enumerate().filter(|(_, b)| !reads(b)) {
            match block_set(b, s, within, work) {
                Ok(Some(p)) => sets[i] = Some(p),
                Ok(None) => {
                    *fails = Some((atoms(&mut std::iter::once(b)), false));
                    return Ok(None);
                }
                Err(e) => {
                    let before = blocks[..=i].iter().filter(|b| !reads(b));
                    *fails = Some((atoms(&mut before.into_iter()), true));
                    return Err(e);
                }
            }
        }
        let mut each = Vec::with_capacity(blocks.len());
        for (b, done) in blocks.iter().zip(sets) {
            each.push(match done {
                Some(p) => p,
                None => match block_set(b, s, within, work)? {
                    Some(p) => p,
                    None => return Ok(None),
                },
            });
        }
        // One union of all, not one per block ([`Classed::join_all`]).
        return Ok(Some(Classed::join_all(each)));
    }
    Ok(as_set(last, s, within, work)?.map(|(set, _)| set))
}

/// [`direct_noting`], with nothing noted.
fn direct(
    f: &Formula,
    s: &Atom,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<Option<Classed>, Refusal> {
    direct_noting(f, s, within, work, &mut None)
}

/// What [`read_once`] gives: whether `f` has a point, and its projection onto each atom.
type ReadOnce = (bool, HashMap<Atom, IntervalSet>);

/// The exact projection of `f` onto every atom it reads at once, with whether `f` has a point;
/// `None` where `f` is not read once over blocks, or a block's elimination is not exact. `f`
/// has no product atom. Read with signs as [`direct`] reads it, `f` is a tree of conjunctions,
/// disjunctions and blocks, a block being a constraint or a conjunction of constraints alone;
/// it is read once when no part is shared and no atom is read by two blocks. Then, with `sat`
/// whether a node has a point (a conjunction's parts read disjoint atoms, so their points join),
/// and from the root down `ctx` (every conjunction above holds its other parts at a point) and
/// `esc` (some disjunction above, with `ctx` there, has another part with a point), the values
/// of an atom `s` of block `B` with a point of `f` are every value where `esc(B)`, else `B`'s
/// own projection onto `s` where `ctx(B)`, else none. Proof: along the one path from the root
/// to `B`, a conjunction holds at `s = v` exactly where its child on the path does and its other
/// parts have points, a disjunction where its child does or another part has a point, as those
/// parts do not read `s`; unrolled, that is `esc(B)`, or `ctx(B)` and `v` in `B`'s projection
/// (Opus and Sol, round 1 of XR-cover-hybrid; after Darwiche and Marquis, "A knowledge
/// compilation map", JAIR 17, 2002, doi:10.1613/jair.989, read 2026-11-21: sec. 4, Table 5,
/// consistency of a decomposable form in one bottom-up pass, and sec. 5, Proposition 5.1,
/// forgetting in a decomposable form; the paper gives neither pass in detail, so the top-down
/// pass and this proof are ours; see the crate's References).
///
/// An atom may also be read by several blocks, provided no conjunction has two parts that read
/// it (the tree is decomposable, Darwiche and Marquis sec. 2, Definition 2.5). The values of
/// `s` are then every value where some disjunction that reads `s`, with `ctx` there, has a part
/// with a point that does not read `s`, else the union of the projections onto `s` of the
/// blocks `B` that read it with `ctx(B)`. Proof: by the rule above, node by node, a
/// conjunction's values of `s` are those of its one part that reads `s` where its other parts
/// have points; a disjunction's are the union of those of its parts, every value for a part
/// with a point that does not read `s`.
/// Unrolled from the root, that is the rule stated. Such a disjunction is found among the nodes
/// where the paths to the blocks of `s` part (their lowest common ancestors), checked one by one,
/// and on the paths between them, where one part alone reads `s` and `esc` is counted as before
/// (Sol, round 2 of XR-cover-hybrid).
///
/// A conjunction's rows of one atom are kept as a box apart from its block, so a conjunction may
/// read an atom in its box and in one part under it. Each block's rows are met with the boxes of
/// the conjunctions above it before it is projected: at a point of `f` that comes through the
/// block, every conjunction on the path holds, so the added rows change neither `f`'s points nor
/// the values read there. The rule above then holds with "every value" read as the box met on the
/// path down to that node: a disjunction's part with a point that does not read `s` gives `s` the
/// values the conjunctions above allow, no more (CE1: `(-5 <= s <= 5) && (s >= 0 || y >= 0)` gives
/// `s` in [-5, 5]); a conjunction whose met box is empty has no point (CE2). A conjunction with two
/// parts reading `s` beyond its box is still declined (CE3) (Gemini, round 3 of XR-cover-hybrid,
/// PRES-cover-unary-push-down). The walk keeps the met box with an undo list, O(1) a bound, so it
/// costs O(n) over the tree; the naive alternative, each block's ancestors read again, is O(n
/// depth).
// Complexity tradeoff: [`direct`] reads the whole of `f` once for each symbol, O(k n) for k
// symbols, 52.9 times the time at 8 times the depth of a chain of accounts
// (`deep_condition::bench::arms_of_a_chain_of_accounts_take_time_near_linear_in_its_depth`).
// Used: two passes over the nodes, O(n), and each block eliminated once for each of its own
// atoms, charged as [`direct`] charges it, or, for a forest of rows over one or two atoms,
// projected onto all of them at once ([`forest`], O(rows)); a part shared, a conjunction with
// two parts reading one atom, or an elimination not exact sends every symbol to the covers as
// before. An atom read by m > 1 blocks costs O(m log n): its blocks sorted in the order of a
// walk of the tree, the lowest common ancestor of each two neighbors by binary lifting
// (O(n log n) once, built only where some atom is read by two blocks), and the count of
// escapes on a path as a difference of counts from the root. Naive alternative: each
// disjunction above each block checked for each atom, O(n) for each, quadratic on a deep
// chain; `wide_pairs` (an atom in both arms of one disjunction) was declined and covered
// symbol by symbol, past the time limit at 4096 names
// (`l01_39_scope_relations::families::bench::wide_pairs_scale`).
fn read_once(f: &Formula, work: &mut Work) -> Result<Option<ReadOnce>, Refusal> {
    enum Node {
        Block(Vec<Con>),
        And {
            block: Option<usize>,
            unary: HashMap<Atom, Ends>,
            unsat: bool,
            kids: Vec<usize>,
        },
        Or(Vec<usize>),
    }
    enum Go<'a> {
        Read(&'a Formula, bool),
        Join(bool, usize),
    }
    // The nodes in post-order, so each node's parts come before it.
    let mut nodes: Vec<Node> = Vec::new();
    let mut values: Vec<usize> = Vec::new();
    // The parts `f` reaches by two paths; handles held outside `f` do not count.
    let twice = Id::reached_twice(f);
    let mut stack = vec![Go::Read(f, true)];
    while let Some(step) = stack.pop() {
        match step {
            Go::Read(g, pos) => {
                if Id::among(g, &twice).is_some() {
                    return Ok(None);
                }
                match g {
                    Formula::Con(c) => {
                        work.read(1)?;
                        match (pos, c.rel) {
                            (true, _) => nodes.push(Node::Block(vec![c.clone()])),
                            (false, Rel::Ge) => {
                                nodes.push(Node::Block(vec![negated(c, &Int::from(-1))]));
                            }
                            (false, Rel::Eq) => {
                                nodes.push(Node::Block(vec![negated(c, &Int::from(-1))]));
                                nodes.push(Node::Block(vec![negated(c, &Int::from(1))]));
                                let n = nodes.len();
                                nodes.push(Node::Or(vec![n - 2, n - 1]));
                            }
                        }
                        values.push(nodes.len() - 1);
                    }
                    Formula::Not(h) => stack.push(Go::Read(h, !pos)),
                    Formula::And(gs) | Formula::Or(gs) => {
                        let and = matches!(g, Formula::And(_)) == pos;
                        stack.push(Go::Join(and, gs.len()));
                        stack.extend(gs.iter().rev().map(|h| Go::Read(h, pos)));
                    }
                }
            }
            Go::Join(and, len) => {
                let parts = values.split_off(values.len() - len);
                if !and {
                    nodes.push(Node::Or(parts));
                    values.push(nodes.len() - 1);
                    continue;
                }
                // A conjunction takes in the parts of the conjunctions under it, and its rows
                // are one block: the rows of `x0 <= -1 and not (x0 >= 0 or ...)` that read
                // `x0` meet in one block. Each list taken in is moved into the longer one, so a
                // chain of n conjunctions costs O(n log n), not O(n^2). The nodes taken in stay
                // in `nodes`, unreached. Rows of one atom are then met into the box `unary`.
                let mut rows: Vec<Con> = Vec::new();
                let mut unary: HashMap<Atom, Ends> = HashMap::new();
                let mut unsat = false;
                let mut kids: Vec<usize> = Vec::new();
                let take_rows = |rows: &mut Vec<Con>, mut more: Vec<Con>| {
                    if more.len() > rows.len() {
                        std::mem::swap(rows, &mut more);
                    }
                    rows.append(&mut more);
                };
                let take_unary =
                    |u: &mut HashMap<Atom, Ends>, mut more: HashMap<Atom, Ends>, bad: &mut bool| {
                        if more.len() > u.len() {
                            std::mem::swap(u, &mut more);
                        }
                        for (a, bnd) in more {
                            let met = u
                                .get(&a)
                                .map_or_else(|| bnd.clone(), |old| range_meet(old, &bnd));
                            if range_is_empty(&met) {
                                *bad = true;
                            }
                            u.insert(a, met);
                        }
                    };
                for i in parts {
                    match std::mem::replace(&mut nodes[i], Node::Or(Vec::new())) {
                        Node::Block(r) => take_rows(&mut rows, r),
                        Node::And {
                            block,
                            unary: sub_u,
                            unsat: sub_bad,
                            kids: mut more,
                        } => {
                            unsat |= sub_bad;
                            take_unary(&mut unary, sub_u, &mut unsat);
                            if let Some(b) = block
                                && let Node::Block(r) =
                                    std::mem::replace(&mut nodes[b], Node::Or(Vec::new()))
                            {
                                take_rows(&mut rows, r);
                            }
                            if more.len() > kids.len() {
                                std::mem::swap(&mut kids, &mut more);
                            }
                            kids.append(&mut more);
                        }
                        or => {
                            nodes[i] = or;
                            kids.push(i);
                        }
                    }
                }
                if kids.is_empty() && unary.is_empty() && !unsat {
                    nodes.push(Node::Block(rows));
                } else {
                    let empty_model = Model::new();
                    let mut wide: Vec<Con> = Vec::new();
                    for c in rows {
                        if c.lin.terms.is_empty() {
                            if !c.holds(&empty_model) {
                                unsat = true;
                            }
                        } else if let Some((a, lo, hi)) = super::formula::one_bound(&c) {
                            let bnd = (lo, hi);
                            let met = unary
                                .get(a)
                                .map_or_else(|| bnd.clone(), |old| range_meet(old, &bnd));
                            if range_is_empty(&met) {
                                unsat = true;
                            }
                            unary.insert(a.clone(), met);
                        } else {
                            wide.push(c);
                        }
                    }
                    let block = (!wide.is_empty()).then(|| {
                        nodes.push(Node::Block(wide));
                        nodes.len() - 1
                    });
                    nodes.push(Node::And {
                        block,
                        unary,
                        unsat,
                        kids,
                    });
                }
                values.push(nodes.len() - 1);
            }
        }
    }
    let root = values.pop().expect("the node of `f`");
    for n in &mut nodes {
        if let Node::And { block, kids, .. } = n
            && let Some(b) = block.take()
        {
            kids.push(b);
        }
    }
    // The nodes reached from the root, each once (the parts of a merged block are not).
    let mut reached = vec![false; nodes.len()];
    reached[root] = true;
    for i in (0..nodes.len()).rev() {
        if !reached[i] {
            continue;
        }
        if let Node::And { kids: cs, .. } | Node::Or(cs) = &nodes[i] {
            for &c in cs {
                reached[c] = true;
            }
        }
    }
    // Pass 0, top-down with an undo stack: cumulative ancestor unary bounds `cur_box`, pushing
    // active ancestor bounds into each leaf block over the atoms it reads, and marking `And`
    // nodes whose cumulative box becomes empty (`box_unsat`, handling nested disjoint intervals).
    // Why the answers stay exact (PRES-cover-unary-push-down), in steps:
    // 1. A point of `f` that a node's subformula `s` helps to hold, in the tree read here (only
    //    `And` and `Or`, negations pushed to the rows as they are read), holds every `unary`
    //    bound of every `And` above `s`: an `And` holds only where each of its parts does.
    //    Call their meet `U` (`cur_box` on entering `s`).
    // 2. At every point that holds `U`, `s` and `s ∧ U'` agree for any `U'` that `U` implies,
    //    so putting `U'` beside `s` changes no point of `f`. The rows pushed into a block are
    //    `U` on the block's own atoms, which `U` implies.
    // 3. An `And` whose `U` with its own bounds is empty (`box_unsat`) holds at no point that
    //    reaches it from the root, by 1, so it may be read as false, though each interval was
    //    not empty alone (CE2) and even where no wide row of it reads the atom (CE2b).
    // Tests: exact/tests/push_down.rs (CE1, CE1b, CE2, CE2b and CE3, from Gemini's round 3 of
    // XR-cover-hybrid, and an outer box over `wide_pairs(512)`), checked against sets written
    // by hand; they cannot catch an error on a shape none of the six builds, such as a box met
    // at three levels.
    enum BoxStep {
        Enter(usize),
        Exit(Vec<(Atom, Option<Ends>)>),
    }
    let mut cur_box: HashMap<Atom, Ends> = HashMap::new();
    let mut after_box: Vec<HashMap<Atom, Ends>> =
        (0..nodes.len()).map(|_| HashMap::new()).collect();
    let mut box_unsat = vec![false; nodes.len()];
    let mut pushed: Vec<Vec<Con>> = (0..nodes.len()).map(|_| Vec::new()).collect();
    let mut bstack = vec![BoxStep::Enter(root)];
    while let Some(step) = bstack.pop() {
        match step {
            BoxStep::Enter(i) => match &nodes[i] {
                Node::And { unary, kids, .. } => {
                    let mut undo = Vec::with_capacity(unary.len());
                    for (a, bnd) in unary {
                        let prev = cur_box.get(a).cloned();
                        let met = prev
                            .as_ref()
                            .map_or_else(|| bnd.clone(), |old| range_meet(old, bnd));
                        if range_is_empty(&met) {
                            box_unsat[i] = true;
                        }
                        after_box[i].insert(a.clone(), met.clone());
                        cur_box.insert(a.clone(), met);
                        undo.push((a.clone(), prev));
                    }
                    if !undo.is_empty() {
                        bstack.push(BoxStep::Exit(undo));
                    }
                    for &c in kids.iter().rev() {
                        bstack.push(BoxStep::Enter(c));
                    }
                }
                Node::Or(kids) => {
                    for &c in kids.iter().rev() {
                        bstack.push(BoxStep::Enter(c));
                    }
                }
                Node::Block(rows) => {
                    let mut seen_a: HashSet<&Atom> = HashSet::new();
                    for a in rows.iter().flat_map(|c| c.lin.terms.keys()) {
                        if seen_a.insert(a)
                            && let Some((lo, hi)) = cur_box.get(a)
                        {
                            if let Some(lo) = lo {
                                pushed[i].push(Con {
                                    lin: Lin {
                                        terms: [(a.clone(), Int::ONE)].into_iter().collect(),
                                        constant: -lo,
                                    },
                                    rel: Rel::Ge,
                                });
                            }
                            if let Some(hi) = hi {
                                pushed[i].push(Con {
                                    lin: Lin {
                                        terms: [(a.clone(), -&Int::ONE)].into_iter().collect(),
                                        constant: hi.clone(),
                                    },
                                    rel: Rel::Ge,
                                });
                            }
                        }
                    }
                }
            },
            BoxStep::Exit(undo) => {
                for (a, prev) in undo {
                    match prev {
                        Some(old) => {
                            cur_box.insert(a, old);
                        }
                        None => {
                            cur_box.remove(&a);
                        }
                    }
                }
            }
        }
    }
    // The blocks and unary-bearing `And` nodes that read each atom, each once.
    let mut occ_of: HashMap<&Atom, Vec<usize>> = HashMap::new();
    let mut any_and_unary = false;
    for (i, n) in nodes.iter().enumerate() {
        if !reached[i] {
            continue;
        }
        match n {
            Node::Block(rows) => {
                for a in rows.iter().flat_map(|c| c.lin.terms.keys()) {
                    let os = occ_of.entry(a).or_default();
                    if os.last() != Some(&i) {
                        os.push(i);
                    }
                }
            }
            Node::And { unary, .. } => {
                for a in unary.keys() {
                    any_and_unary = true;
                    occ_of.entry(a).or_default().push(i);
                }
            }
            Node::Or(_) => {}
        }
    }
    // Pass 1, from the blocks up: each block's projection onto each of its atoms, and `sat`.
    let mut sat = vec![false; nodes.len()];
    let mut own: Vec<HashMap<Atom, IntervalSet>> =
        (0..nodes.len()).map(|_| HashMap::new()).collect();
    for i in 0..nodes.len() {
        if !reached[i] {
            continue;
        }
        sat[i] = match &nodes[i] {
            Node::Block(rows) => {
                let atoms: BTreeMap<&Atom, ()> = (rows.iter().flat_map(|c| c.lin.terms.keys()))
                    .map(|a| (a, ()))
                    .collect();
                if atoms.is_empty() {
                    return Ok(None);
                }
                // The block's rows split into groups that share no atom (`row_groups`), each
                // projected onto each of its own atoms alone. Proof that the sets are those of
                // the block: a point of the block is a point of each group, and points of groups
                // over disjoint atoms join into one point of the block; so the values of an
                // atom `a` with a point of the block are those with a point of `a`'s group when
                // every other group has a point, else none. Each projection here is exact
                // (`forest`, or the exact shadow of `projected`), as it was over the whole block,
                // so each set is the one exact projection, the same set the whole block gave.
                // Complexity tradeoff: [`projected`] of the whole block for each of its atoms,
                // O(r) each and O(r a) for r rows and a atoms: 512 atoms over 512 rows of 128
                // groups of four in each arm of `disjoint::bench`'s join, O(k^2). Used: one
                // union-find over the rows' atoms, O(t α) for t terms, then each group
                // projected onto its own atoms, O(r_g a_g) for a group of r_g rows and a_g
                // atoms; a block of one group costs what it did (COMPLEXITY.md row
                // PRES-cover-bench-disjoint-reduced).
                let combined: Vec<Con>;
                let eff: &[Con] = if pushed[i].is_empty() {
                    rows
                } else {
                    combined = rows.iter().chain(&pushed[i]).cloned().collect();
                    &combined
                };
                let mut all = true;
                // A group that is one sum over boxed atoms ([`star`], exact) is projected onto
                // all its atoms at once. Complexity tradeoff: [`projected`] per atom, O(a) each
                // and O(a²) for the a atoms of the sum (`wide` of
                // `l01_39_scope_relations::families`, 55 per cent of its time at k = 128 in
                // `shadow_logged` under this loop); `star`, one pass, O(a).
                for group in row_groups(eff, work)? {
                    let sets = if let Some(sets) = forest(&group, work)? {
                        sets
                    } else if let Some(sets) = star(&group, work)? {
                        sets
                    } else {
                        let mut sets = HashMap::new();
                        for a in (group.iter().flat_map(|c| c.lin.terms.keys()))
                            .map(|a| (a, ()))
                            .collect::<BTreeMap<&Atom, ()>>()
                            .keys()
                        {
                            let Some(p) = projected(&group, a, work)? else {
                                return Ok(None);
                            };
                            sets.insert((*a).clone(), p);
                        }
                        sets
                    };
                    // A group has a point exactly where its projections are not empty: the
                    // shadow of a group with no point is the false row, every set empty.
                    all &= sets.values().any(|p| !p.is_empty());
                    own[i].extend(sets);
                }
                if !all {
                    for p in own[i].values_mut() {
                        *p = IntervalSet::empty();
                    }
                }
                all
            }
            Node::And {
                unsat, kids: cs, ..
            } => !*unsat && !box_unsat[i] && cs.iter().all(|&c| sat[c]),
            Node::Or(cs) => cs.iter().any(|&c| sat[c]),
        };
    }
    // Pass 2, from the root down: `ctx` of each node, its parent and depth, and `esc` as a count:
    // the disjunctions on the path from the root to it (it excluded) that have `ctx` and another
    // part with a point than the one on the path.
    let mut ctx = vec![false; nodes.len()];
    let mut escs = vec![0usize; nodes.len()];
    let mut parent = vec![root; nodes.len()];
    let mut depth = vec![0usize; nodes.len()];
    let mut live = vec![0usize; nodes.len()];
    ctx[root] = sat[root];
    for i in (0..nodes.len()).rev() {
        if !reached[i] {
            continue;
        }
        if let Node::And { kids: cs, .. } | Node::Or(cs) = &nodes[i] {
            work.read(cs.len() as u64)?;
            live[i] = cs.iter().filter(|&&c| sat[c]).count();
            for &c in cs {
                let others = live[i] - usize::from(sat[c]);
                parent[c] = i;
                depth[c] = depth[i] + 1;
                if let Node::And { unsat, .. } = &nodes[i] {
                    ctx[c] = ctx[i] && !*unsat && !box_unsat[i] && others == cs.len() - 1;
                    escs[c] = escs[i];
                } else {
                    ctx[c] = ctx[i] && sat[c];
                    escs[c] = escs[i] + usize::from(ctx[i] && others > 0);
                }
            }
        }
    }
    // Where some atom is read by two nodes, or a conjunction holds a box: the order of a walk of
    // the tree from the root, and the tree by binary lifting (`zed_graph::Lift`), its own root
    // above `root`. A parent has a higher index than its parts (pass 2 runs down the indices),
    // so each reached node is attached after its parent.
    let mut order = vec![0usize; nodes.len()];
    let mut tree = None;
    if any_and_unary || occ_of.values().any(|os| os.len() > 1) {
        let mut stack = vec![root];
        let mut at = 0;
        while let Some(i) = stack.pop() {
            order[i] = at;
            at += 1;
            if let Node::And { kids: cs, .. } | Node::Or(cs) = &nodes[i] {
                stack.extend(cs.iter().copied());
            }
        }
        let deepest = (0..nodes.len()).filter(|&i| reached[i]).map(|i| depth[i]);
        let mut lift = zed_graph::Lift::with_depth(nodes.len(), deepest.max().unwrap_or(0) + 1);
        for i in (0..nodes.len()).rev().filter(|&i| reached[i]) {
            lift.attach(i, if i == root { lift.root() } else { parent[i] });
        }
        tree = Some(lift);
    }
    // Asked only for an atom read by two nodes or more, which is where the tree is built.
    let tree = || {
        tree.as_ref()
            .expect("the tree is built where two nodes read an atom")
    };
    let ends_set = |e: &Ends| {
        if range_is_empty(e) {
            IntervalSet::empty()
        } else {
            let fin =
                |v: &Option<Int>, inf: End| v.as_ref().map_or(inf, |x| End::Fin(Num::from(x)));
            IntervalSet::range(fin(&e.0, End::NegInf), fin(&e.1, End::PosInf))
        }
    };
    let every = IntervalSet::range(End::NegInf, End::PosInf);
    let mut out = HashMap::new();
    // The atoms in their order, not the map's: an atom whose places meet under a conjunction
    // ends the read (`None`) after the atoms before it are charged, so in the map's order,
    // which changes from run to run, the work charged and the allowance left to the fast paths
    // after it changed too (found by `tests::the_covers_answer_alike_with_and_without_what_the_
    // symbols_before_learned`, 100 units apart on one formula). Sorting adds O(a log a) for the
    // a atoms to the O(t) read of their t places.
    let mut occ_of: Vec<(&Atom, Vec<usize>)> = occ_of.into_iter().collect();
    occ_of.sort_unstable_by(|x, y| x.0.cmp(y.0));
    for (a, mut os) in occ_of {
        if os.len() == 1 && matches!(nodes[os[0]], Node::Block(_)) {
            let b = os[0];
            let set = if !sat[root] {
                IntervalSet::empty()
            } else if escs[b] > 0 {
                every.clone()
            } else if ctx[b] && sat[b] {
                own[b][a].clone()
            } else {
                IntervalSet::empty()
            };
            out.insert(a.clone(), set);
            continue;
        }
        work.read(os.len() as u64)?;
        os.sort_by_key(|&v| order[v]);
        let mut vs = os.clone();
        vs.extend(os.windows(2).map(|w| tree().lca(w[0], w[1])));
        vs.sort_by_key(|&v| order[v]);
        vs.dedup();
        let mut vkids: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
        for w in vs.windows(2) {
            let x = tree().lca(w[0], w[1]);
            let c = tree().up_to(w[1], tree().depth(x) + 1);
            vkids.entry(x).or_default().push((w[1], c));
        }
        for (&x, edges) in &vkids {
            if matches!(nodes[x], Node::And { .. }) {
                let mut cs: Vec<usize> = edges.iter().map(|&(_, c)| c).collect();
                zed_collections::sorted::sort_dedup(&mut cs);
                if cs.len() > 1 {
                    return Ok(None);
                }
            }
        }
        if !sat[root] {
            out.insert(a.clone(), IntervalSet::empty());
            continue;
        }
        if escs[vs[0]] > 0 {
            out.insert(a.clone(), every.clone());
            continue;
        }
        let mut v_in: HashMap<usize, Ends> = HashMap::new();
        v_in.insert(vs[0], (None, None));
        let mut pieces = Vec::new();
        for &v in &vs {
            let vin = v_in[&v].clone();
            let vafter = match &nodes[v] {
                Node::And { unary, .. } if unary.contains_key(a) => after_box[v][a].clone(),
                _ => vin.clone(),
            };
            match &nodes[v] {
                Node::Block(_) if ctx[v] && sat[v] => {
                    pieces.extend(own[v][a].pieces().cloned());
                }
                Node::And { unary, .. }
                    if unary.contains_key(a)
                        && vkids.get(&v).is_none_or(Vec::is_empty)
                        && ctx[v]
                        && sat[v] =>
                {
                    pieces.extend(ends_set(&vafter).pieces().cloned());
                }
                Node::Or(_) if ctx[v] && sat[v] => {
                    let mut cs: Vec<usize> = vkids
                        .get(&v)
                        .map(|es| es.iter().map(|&(_, c)| c).collect())
                        .unwrap_or_default();
                    zed_collections::sorted::sort_dedup(&mut cs);
                    let reading = cs.iter().filter(|&&c| sat[c]).count();
                    if live[v] > reading {
                        pieces.extend(ends_set(&vin).pieces().cloned());
                    }
                }
                _ => {}
            }
            if let Some(edges) = vkids.get(&v) {
                for &(w, c) in edges {
                    v_in.insert(w, vafter.clone());
                    if escs[w] > escs[c] {
                        pieces.extend(ends_set(&vafter).pieces().cloned());
                    }
                }
            }
        }
        out.insert(a.clone(), IntervalSet::from_pieces(pieces));
    }
    Ok(Some((sat[root], out)))
}

/// The exact projections of the part `f` onto the symbols of `want`, each with the solver's
/// set, put in `out` as each is shown, read from the cells of points shared by every symbol:
/// for a part [`read_once`] declines, in place of a cell of each point read for each symbol
/// alone ([`cell`], which reads the whole part once a symbol). For each point `m` (those of
/// `points`, else one from [`quick_point`] or a question), its implicant `I` ([`implicant`]:
/// rows that hold at `m` and whose conjunction implies `f`) is read once and split into groups
/// that share no atom ([`row_groups`]). Each set below holds only values of points of `I`, so
/// of `f`; a symbol whose sets so far hold its solver's set `h` (which holds every value with a
/// point) has exactly `h`. The sets of one point:
/// - a symbol `I` does not read: every value, since `I` holds whatever its value is;
/// - in a group [`forest`] answers: its exact projection of the group, which is that of `I`,
///   as the other groups share no atom with it and hold at `m`;
/// - in another group, a symbol `a` whose column (each row's coefficient of it) is that of
///   another atom `b`: every value, as `a + t`, `b - t` leaves each row's value as it was, so
///   moving `m` so keeps every row of the group, for each integer `t`. A row is a [`Lin`],
///   whose `terms` map atoms to integer coefficients and nothing else: no `mod`, division or
///   congruence term sits inside a row. `x div n` and `x mod n` are written as the row
///   `x == n·q + r` over atoms of their own (`formula.rs`, [`Factor`]), so an atom such a
///   remainder reads has that row in its column, which no atom outside it shares
///   (`tests::an_atom_read_by_a_remainder_is_no_twin`). A product atom could change when one
///   factor moves, but a part with any product has factors ([`factors`]) and never comes
///   here ([`exact_each`]);
/// - else its line: the values `v` with every row of its group true at `m` with `a` at `v`.
///
/// Then each symbol not yet shown, in the order of `Atom`, asks one question, of `f` with the
/// symbol on the first piece of its gap: a point found is read for every symbol, and a piece
/// with none is cut from that symbol's `h`. A symbol whose gap that leaves gets one more
/// search, with no question, on the first piece of its gap (the second pass, below); a symbol
/// still left is covered alone, as before.
// Complexity tradeoff: naive version, each symbol's cover reads each point's cell over the
// whole part (`along`, then the implicant's projection), O(k·r) for k symbols over r rows,
// 15,200 M instructions at k = 1,536 of `unary_arms` against a limit of 24 s
// (PRES-cover-bench-unary-arms). Used: one implicant and one grouping for each point, O(r + k)
// a point, the symbols read at once, and one question for each symbol the points leave, so
// O(p·(r + k)) for p points, linear where the points are few. A symbol left after its question
// costs what it cost before. Where `I` is a forest of two-atom rows the cells are exact
// projections; elsewhere a line can be narrower than the projection, and the symbol is then
// left to its own cover, never answered wrongly.
// What meets `work`'s limit (the allowance of [`exact_each`]): `cell` (its eliminations and
// projections run the solver) and each question, the work with no bound of its own. Charged
// past it (row LIMITS-shared-step-allowance):
// - `point_cells` and this step's reads of `size`, 1, `want` and [`PIECE`]s, with
//   [`Work::exempt`]: `point_cells` runs no solver step, only [`implicant`] (each shared part
//   walked once, by its `seen`), [`row_groups`] (union-find, O(t·α(t)) for t terms),
//   [`forest`] and [`star`] (linear, by their notes) and a loop over the implicant's columns,
//   so O(T·α(T)) for T the terms of the part; it runs once a point, and the points are at most
//   k + 1 (one found first, then one a symbol, each symbol asking once);
// - the declared room of each [`quick_search`] and [`quick_point`] (`2·(size + 2)` rows,
//   [`SOLVER_UNIT`] each), with [`Work::credit`], at most k + 1 of them. Only the declared room
//   is credited; what a search reads past it (the last step's count, a decision's disjuncts or
//   a leaf's rows) meets the limit, as all of it did before, and the solver runs at its leaves
//   (`point_of`) meet the limit too, so room credited and not read is at most `k + 1` rooms
//   more for them.
// The second pass (at the end) runs outside `work`, on meters of its own: at most k more
// searches and points, each within its own room (PERF-project-each-renaming-cost).
// Measured on `deep_condition`'s `heavy` (5 names): the step reads 5.3M units at depth 720 and
// 42.6M at 5,760 (`point_cells` 16.1M, the rooms of two `quick_search`s 12.7M), all reading, no
// question; the allowance is 15.3M (`deep_condition::bench::arms_of_a_test_whose_small_choice_
// misses_the_bound_take_time_near_linear_past_the_shared_allowance`).
fn shared_cells(
    f: &Formula,
    size: u64,
    mut want: BTreeMap<&Atom, IntervalSet>,
    points: &mut Vec<Model>,
    out: &mut HashMap<Atom, IntervalSet>,
    work: &mut Work,
) -> Result<(), Refusal> {
    if points.is_empty() {
        let room = 2 * (size + 2);
        work.credit(SOLVER_UNIT.saturating_mul(room));
        if let Some(m) = quick_point(f, room, work)? {
            points.push(m);
        } else {
            work.question(size)?;
            EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
            match work.ask(f)? {
                Some(m) => points.push(m),
                None => {
                    for s in want.keys() {
                        out.insert((*s).clone(), IntervalSet::empty());
                    }
                    return Ok(());
                }
            }
        }
    }
    let mut found: HashMap<Atom, IntervalSet> = HashMap::new();
    let mut read = 0;
    let order: Vec<Atom> = want.keys().map(|s| (*s).clone()).collect();
    let none = IntervalSet::empty();
    // Each symbol is checked once before its question, O(1) charged pieces each, and all once
    // at the end: a check of every symbol before each question would be O(k²). A symbol with
    // a gap reads one cell, at the newest point (below), so the loop's work beyond
    // `point_cells` and the questions is the sum over the symbols s left with a gap of
    // `size + PIECE·(|c_s| + 1)` plus the work of `cell` for s, O(k·size) plus the cells' own
    // charged work, with no term in the number of points: each symbol is visited once by this
    // loop (`order` holds it once), and it reads one point, not every point found.
    for s in &order {
        while read < points.len() {
            work.exempt(|w| point_cells(f, &points[read], &want, size, &mut found, w))?;
            read += 1;
        }
        let Some(h) = want.get(s) else {
            continue;
        };
        work.exempt(|w| w.read(1))?;
        let mut gap = h.minus(found.get(s).unwrap_or(&none));
        if gap.is_empty() {
            out.insert(s.clone(), h.clone());
            want.remove(s);
            continue;
        }
        // Before the question, the symbol's cell at the newest point, as `cells_cover` reads it
        // (the projection of the implicant at that point): every cell of `s` at a point of `f`
        // lies in the projection of `f` on `s`, so any point is sound, and the question still
        // follows where a gap is left; only the cost changes, never the answer. The cells that
        // `point_cells` reads (forest, star, line) can be narrower than this projection, and
        // each question it saves charges `size + 2` and a solver run.
        // Complexity tradeoff: naive version, a question for each gap `point_cells` left (9 on
        // the guards of `tests::a_part_certified_in_part_shares_only_what_direct_declined`,
        // 2,587,400 units); reading the cell at every point already found would cost
        // O(k·q·size) for q points, up to O(k²·size). Used: one cell per symbol, at one point,
        // `size` units read plus the cell's own charged work and [`PIECE`] for each of its
        // pieces and one more, O(k·size) plus the cells' work over the k symbols (the sum above
        // the loop). The cell's own work meets this step's allowance, which is part of the
        // symbols' `k·L` ([`exact_each`]); the `size` and [`PIECE`]s read are charged past it
        // ([`Work::exempt`]), O(size) a symbol (LIMITS-shared-step-allowance). `points` is not
        // empty here: the step returned above where `f` has no point, and the loop above read every
        // point, so `read == points.len() >= 1`. The parts of the cell with holes and its strides
        // are dropped: the ranges `c` alone are values of `s` with a point, as in `cells_cover`,
        // and what they leave is asked or left to the symbol's own cover.
        let (c, _, _) = cell(f, &points[read - 1], s, &HashSet::new(), &h.hull(), work)?;
        work.exempt(|w| {
            w.read(size)?;
            w.charge(PIECE.saturating_mul(c.len() as u64 + 1))
        })?;
        gap = gap.minus(&c);
        let e = found.entry(s.clone()).or_insert_with(IntervalSet::empty);
        *e = e.join(&c);
        let Some((lo, hi)) = gap.pieces().next() else {
            out.insert(s.clone(), h.clone());
            want.remove(s);
            continue;
        };
        let piece = IntervalSet::range(lo.clone(), hi.clone());
        let within = super::member(s, &piece);
        // The question's answer found with no question where one comes soon ([`quick_search`],
        // whose rows of one atom cut each branch that leaves the piece): a point of `f` with
        // `s` in the piece, read as the loop reads every point, or a proof that there is none,
        // every branch cut, taken as the question's `None` is. Where it finds neither, the
        // question is asked as before, so the answer is the question's in every case and only
        // the cost changes.
        // Complexity tradeoff: naive version, a question for each gap, a run of the solver on
        // the whole part, 2.49M units for the one with a point on `deep_condition`'s `heavy` at
        // depth 180 (1,720 a constraint), so at depth 1,440 the questions passed the step's
        // allowance `k·L`, which does not grow with the part, and every symbol went to its own
        // cover (BENCH-deep-small-choice). Used: `quick_search` first, at most `2·(size + 2)`
        // rows, as where `quick_point` stands for a question elsewhere in this module, then the
        // question where it gives up: at most that much more than before for each question. On
        // `heavy` both of its questions are answered so, with 1.44M and 1.73M units at depth
        // 1,440 (the step 10.67M units in all at depth 1,440, 1.35M at 180: 7.9 times at 8
        // times the depth). The declared room is credited past the allowance ([`Work::credit`],
        // see above [`shared_cells`]), which met it before and so gave up past depth about 2,050.
        let room = 2 * (size + 2);
        work.credit(SOLVER_UNIT.saturating_mul(room));
        let answer = match quick_search(f, Some(&within), room, work)? {
            Quick::Point(m) => Some(m),
            Quick::Empty => None,
            Quick::Unknown => {
                work.question(size + 2)?;
                EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
                work.ask(&Formula::and(vec![f.clone(), within]))?
            }
        };
        match answer {
            Some(m) => points.push(m),
            None => {
                if let Some(h) = want.get_mut(s) {
                    *h = h.minus(&piece);
                }
            }
        }
    }
    while read < points.len() {
        work.exempt(|w| point_cells(f, &points[read], &want, size, &mut found, w))?;
        read += 1;
    }
    work.exempt(|w| w.read(want.len() as u64))?;
    let mut rest: BTreeMap<&Atom, IntervalSet> = BTreeMap::new();
    for (s, h) in want {
        if found.get(s).is_some_and(|r| h.is_subset(r)) {
            out.insert(s.clone(), h);
        } else {
            rest.insert(s, h);
        }
    }
    // Each symbol still left, in the order of `Atom`, gets one more turn (the second pass): a
    // search ([`quick_search`] only, no question) on the first piece of its gap. A symbol whose
    // gap that turn, or a turn before it, closes is answered here; every other symbol goes to
    // its own cover, which starts exactly as it did with no second pass.
    // Complexity tradeoff: naive version (before), one question for each symbol, then the
    // symbols left go to covers of their own ([`cover`]), each reading the whole part again
    // within its own limit L. Which symbols are left depends on the order of the atoms, so on
    // the names: on `deep_condition`'s `heavy` renamed by structure, the atom of `w >= i` comes
    // last, its one question (the piece below the first point's cell, (-inf, 1439] at depth
    // 1,440) finds a point at 0, its gap (-inf, -1] stays, and its own cover passes L at depth
    // 1,440 and is refused, which `project_each`'s caller then retries: 32.3M units against
    // 14.5M with the names as written, whose order asks (-inf, -1] first (bench ratio 9.86
    // against 7.90; row PERF-project-each-renaming-cost). Used: one more search for each
    // symbol left, over the points this step already holds, with no second reading of the part:
    // O(k·(size + 2)) rows of search and k reads of `size + 1`, plus `point_cells` of each
    // point found, O(T·α(T)) each (the note above [`shared_cells`]).
    // A first version asked again until each gap closed, with the solver where the search gave
    // up, charged against this step's allowance. A gap with infinitely many pieces (a set with
    // a stride, `families::two_eq_case_against_the_oracle`'s `a` in 9 mod 12) never closed, so
    // that version spent the whole allowance `k·L`; it was taken from the symbols' fast paths
    // (`charge` in [`exact_each`]), and their covers were then refused or answered wider (14 of
    // the 1,012 test pieces of l01_25, l01_38 and l01_39 failed, 7 of them by timeout).
    // Charges: each turn runs on a meter of its own, its limit only the turn's declared room:
    // `size + 1` rows read and the search's `2·(size + 2)` rows ([`Work::credit`]), with the
    // cells of the point it finds exempt ([`Work::exempt`], as in the first pass). It runs no
    // solver question, and a solver run at a search's leaf (`point_of`) meets that limit, so a
    // turn is bounded by its structure and its work does not depend on [`EXACT_LIMIT`]
    // (`deep_condition::a_small_limit_leaves_the_shared_reading_of_a_deep_test_whole`). Its
    // work is counted in [`EXACT_WORK`] but not in `work`, so the allowance and every fast
    // path's share of it are what they were with no second pass; a turn that gives up
    // (`Unknown`, or its room spent) only leaves its symbol to its cover. A point it finds is
    // not added to `points`, which the covers read, so each cover sees the points it saw before.
    // Why the answers do not change: a point found is a point of `f`, whose cells
    // (`point_cells`) hold only values of points of `f` (the proof above this function), and a
    // piece is cut from `h` only where the search proved `f` has no point with `s` in it
    // ([`quick_search`]'s proof, (d)); so a set given here is the exact projection, as the
    // cover's is, and a symbol not given one is covered as before.
    let names: Vec<&Atom> = rest.keys().copied().collect();
    for &s in &names {
        let mut turn = Work {
            used: 0,
            limit: 0,
            solver: work.solver,
        };
        let room = 2 * (size + 2);
        turn.credit(SOLVER_UNIT.saturating_mul(size + 1 + room));
        let gap_of = |rest: &BTreeMap<&Atom, IntervalSet>, found: &HashMap<Atom, IntervalSet>| {
            rest[s].minus(found.get(s).unwrap_or(&none))
        };
        if turn.read(size + 1).is_err() {
            continue;
        }
        let gap = gap_of(&rest, &found);
        let Some((lo, hi)) = gap.pieces().next() else {
            out.insert(s.clone(), rest[s].clone());
            continue;
        };
        let piece = IntervalSet::range(lo.clone(), hi.clone());
        let within = super::member(s, &piece);
        match quick_search(f, Some(&within), room, &mut turn) {
            Ok(Quick::Point(m)) => {
                if turn
                    .exempt(|w| point_cells(f, &m, &rest, size, &mut found, w))
                    .is_err()
                {
                    continue;
                }
            }
            Ok(Quick::Empty) => {
                if let Some(h) = rest.get_mut(s) {
                    *h = h.minus(&piece);
                }
            }
            Ok(Quick::Unknown) | Err(_) => continue,
        }
        if gap_of(&rest, &found).is_empty() {
            out.insert(s.clone(), rest[s].clone());
        }
    }
    // A symbol before another in the order may be closed by the point of the other's turn: one
    // check each, O(k) set differences, on a meter of its own as the turns are.
    let mut last = Work {
        used: 0,
        limit: u64::MAX,
        solver: work.solver,
    };
    last.read(names.len() as u64)?;
    for s in names {
        if !out.contains_key(s) && rest[s].minus(found.get(s).unwrap_or(&none)).is_empty() {
            out.insert(s.clone(), rest[s].clone());
        }
    }
    Ok(())
}

/// The cells of the point `m` of `f` for the symbols of `want`, joined to `found`
/// ([`shared_cells`], which proves each).
fn point_cells(
    f: &Formula,
    m: &Model,
    want: &BTreeMap<&Atom, IntervalSet>,
    size: u64,
    found: &mut HashMap<Atom, IntervalSet>,
    work: &mut Work,
) -> Result<(), Refusal> {
    work.read(size + want.len() as u64)?;
    let mut rows = Vec::new();
    if !implicant(
        f,
        m,
        true,
        &mut rows,
        &mut HashSet::new(),
        &mut HashMap::new(),
    ) {
        // Every point given holds `f`; one that did not would give no cell.
        return Ok(());
    }
    // A row reading no atom holds at `m`, so everywhere, and limits no atom.
    rows.retain(|c| !c.lin.terms.is_empty());
    let mut add = |a: &Atom, set: IntervalSet| {
        if want.contains_key(a) {
            let e = found.entry(a.clone()).or_insert_with(IntervalSet::empty);
            *e = e.join(&set);
        }
    };
    let mut seen: HashSet<Atom> = HashSet::new();
    for group in row_groups(&rows, work)? {
        for c in &group {
            seen.extend(c.lin.terms.keys().cloned());
        }
        if let Some(sets) = forest(&group, work)? {
            for (a, set) in sets {
                add(&a, set);
            }
            continue;
        }
        if let Some(sets) = star(&group, work)? {
            for (a, set) in sets {
                add(&a, set);
            }
            continue;
        }
        let mut columns: HashMap<&Atom, Vec<(usize, &Int)>> = HashMap::new();
        for (j, c) in group.iter().enumerate() {
            for (a, k) in &c.lin.terms {
                columns.entry(a).or_default().push((j, k));
            }
        }
        let mut alike: HashMap<&Vec<(usize, &Int)>, u32> = HashMap::new();
        for col in columns.values() {
            *alike.entry(col).or_default() += 1;
        }
        for (a, col) in &columns {
            if !want.contains_key(*a) {
                continue;
            }
            if alike[col] > 1 {
                add(a, IntervalSet::top());
                continue;
            }
            let v = value(&Lin::atom((*a).clone()), m);
            let (mut lo, mut hi): Ends = (None, None);
            for &(j, k) in col {
                let c = &group[j];
                // `k·x + r` with every other atom at `m`.
                let r = &value(&c.lin, m) - &(k * &v);
                let row: Ends = match c.rel {
                    Rel::Eq => (Some(v.clone()), Some(v.clone())),
                    Rel::Ge => row_range(k, &r, false).0,
                };
                (lo, hi) = range_meet(&(lo, hi), &row);
            }
            let end = |e: Option<Int>, inf: End| e.as_ref().map_or(inf, fin);
            add(
                a,
                IntervalSet::range(end(lo, End::NegInf), end(hi, End::PosInf)),
            );
        }
    }
    for a in want.keys() {
        if !seen.contains(*a) {
            add(a, IntervalSet::top());
        }
    }
    Ok(())
}

/// The exact projection of the conjunction `rows` onto each atom it reads, where every row
/// reads one atom except rows `>=` over one linear form `t` that differ only in their constant
/// (`t + k >= 0`, the least `k` standing for all); `None` for other rows. Each atom `x` alone in
/// its rows has an interval `D_x`. Then `v` is in the projection onto `a` where `v` is in `D_a` and
/// `c_a·v + k + Σ_{x ≠ a} max_{D_x} c_x·x >= 0`: each other atom takes, independently of the rest,
/// the end of its own interval that makes its term largest, and an interval of integers attains its
/// maximum term at an end (or the term is unbounded above, and every `v` in `D_a` has a point).
/// Exact over the integers, as every step names a point. Where the rows have no point (an empty
/// interval, an equation `k·x = c` with `k` not dividing `c`, or an atom of the form left with no
/// value, which happens exactly when `k + Σ max c_x·x < 0`, that is, when no point meets the form),
/// the projection onto every atom is empty ([`nothing`]).
// Complexity tradeoff: naive version, a cover per symbol ([`projected`] for each atom,
// eliminating the others one by one), O(n) each and O(n²) for the n atoms of the form (`wide`
// of `l01_39_scope_relations::families`, a sum of n names each boxed, measured 166 times the
// work at 8 times n). Used: one pass, the sum of every term's maximum once, with the count of
// unbounded ones, and each atom's own term taken back out, O(n) in all.
fn star(rows: &[Con], work: &mut Work) -> Result<Option<HashMap<Atom, IntervalSet>>, Refusal> {
    work.read(rows.iter().map(|c| c.lin.terms.len() as u64).sum())?;
    let mut dom: HashMap<&Atom, Ends> = HashMap::new();
    let mut form: Option<(&BTreeMap<Atom, Int>, &Int)> = None;
    for c in rows {
        if c.lin.terms.len() == 1 {
            let (a, k) = c.lin.terms.iter().next().expect("one term");
            let c0 = &c.lin.constant;
            let (row, bad) = row_range(k, c0, c.rel == Rel::Eq);
            if bad {
                return Ok(Some(nothing(rows)));
            }
            let d = dom.entry(a).or_insert((None, None));
            *d = range_meet(d, &row);
            continue;
        }
        if c.rel != Rel::Ge {
            return Ok(None);
        }
        match &mut form {
            None => form = Some((&c.lin.terms, &c.lin.constant)),
            Some((t, k)) if *t == &c.lin.terms => {
                if &c.lin.constant < *k {
                    *k = &c.lin.constant;
                }
            }
            Some(_) => return Ok(None),
        }
    }
    let Some((terms, k)) = form else {
        return Ok(None);
    };
    if dom.values().any(range_is_empty) {
        return Ok(Some(nothing(rows)));
    }
    // Each term's maximum on its atom's interval, `None` where it is unbounded above.
    let top = |a: &Atom, c: &Int| -> Option<Int> {
        let d = dom.get(a);
        let end = if c.is_positive() {
            d.and_then(|d| d.1.as_ref())
        } else {
            d.and_then(|d| d.0.as_ref())
        };
        end.map(|e| c * e)
    };
    let mut sum = Int::from(0);
    let mut open = 0usize;
    for (a, c) in terms {
        match top(a, c) {
            Some(v) => sum = &sum + &v,
            None => open += 1,
        }
    }
    let end = |e: &Option<Int>, inf: End| e.as_ref().map_or(inf, fin);
    let mut out: HashMap<Atom, IntervalSet> = HashMap::new();
    for (a, c) in terms {
        let own = top(a, c);
        let d = dom.get(a).cloned().unwrap_or((None, None));
        let rest_open = open - usize::from(own.is_none());
        let d = if rest_open > 0 {
            d
        } else {
            // `c·v + r >= 0`, `r` the constant and the other terms' maxima.
            let r = &(k + &sum) - &own.unwrap_or_else(|| Int::from(0));
            range_meet(&d, &row_range(c, &r, false).0)
        };
        if range_is_empty(&d) {
            return Ok(Some(nothing(rows)));
        }
        out.insert(
            a.clone(),
            IntervalSet::range(end(&d.0, End::NegInf), end(&d.1, End::PosInf)),
        );
    }
    for (a, d) in &dom {
        if !terms.contains_key(*a) {
            out.insert(
                (*a).clone(),
                IntervalSet::range(end(&d.0, End::NegInf), end(&d.1, End::PosInf)),
            );
        }
    }
    Ok(Some(out))
}

/// The empty set for every atom `rows` read: the projections of a conjunction with no point.
fn nothing(rows: &[Con]) -> HashMap<Atom, IntervalSet> {
    (rows.iter())
        .flat_map(|c| c.lin.terms.keys())
        .map(|a| (a.clone(), IntervalSet::empty()))
        .collect()
}

/// The values of `y` for which some `x` in `d` has `a·x + b·y + k >= 0`, for `a` and `b` not
/// zero: every `y` where `a·x` is unbounded above on `d`, else `b·y >= -(k + max a·x)`.
fn ends_sent(d: &Ends, a: &Int, b: &Int, k: &Int) -> Ends {
    if range_is_empty(d) {
        return (Some(Int::ONE), Some(Int::ZERO));
    }
    let end = if a.is_positive() { &d.1 } else { &d.0 };
    let Some(x) = end else {
        return (None, None);
    };
    let t = -&(k + &(a * x));
    if b.is_positive() {
        (Some(t.div_ceil(b)), None)
    } else {
        (None, Some(t.div_floor(b)))
    }
}

/// The exact projection of the conjunction `rows` onto each atom it reads, where each row is
/// `>=` over one atom, or over two atoms and the rows over two atoms join the atoms as a forest
/// (no two rows over the same two atoms, no cycle); `None` for other rows. Each atom's values
/// are an interval: its own rows' interval met with, from each neighbor, the values for which
/// some value of the neighbor in its interval, met with those from its other neighbors, meets
/// their row. Exact over the integers, as a forest of constraints made arc consistent has a
/// point with each atom at each of its values: each neighbor's subtree takes a value that meets
/// the row, and so on outward, with no cycle to close (Freuder, "A sufficient condition for
/// backtrack-free search", JACM 29, 1982, sec. 4, Theorem 3 with Theorem 1, read 2026-11-21:
/// strong 2-consistency makes a forest backtrack-free; each message an interval, by the rounding
/// above). Where some atom has no value, the conjunction has no point and every atom gets none.
// Complexity tradeoff: [`projected`] for each atom eliminates the others, O(r) each and O(r²)
// for the r rows of a path of `wide_pairs`. Used: two passes over each tree, a message each way
// on each row, prefix and suffix intersections at each atom, O(r) in all; rows of other forms
// fall back to [`projected`].
fn forest(rows: &[Con], work: &mut Work) -> Result<Option<HashMap<Atom, IntervalSet>>, Refusal> {
    let mut index: HashMap<&Atom, usize> = HashMap::new();
    let mut atoms: Vec<&Atom> = Vec::new();
    for c in rows {
        if c.lin.terms.len() > 2 || (c.lin.terms.len() == 2 && c.rel == Rel::Eq) {
            return Ok(None);
        }
        for a in c.lin.terms.keys() {
            index.entry(a).or_insert_with(|| {
                atoms.push(a);
                atoms.len() - 1
            });
        }
    }
    work.read(rows.len() as u64)?;
    let n = atoms.len();
    let mut own: Vec<Ends> = vec![(None, None); n];
    // The rows over two atoms: (u, v, coefficient of u, of v, constant).
    let mut edges: Vec<(usize, usize, &Int, &Int, &Int)> = Vec::new();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    // The trees joined so far.
    let mut trees = UnionFind::new(n);
    for c in rows {
        if let Some((a, lo, hi)) = super::formula::one_bound(c) {
            let i = index[a];
            own[i] = range_meet(&own[i], &(lo, hi));
            continue;
        }
        let mut ts = c.lin.terms.iter();
        let (Some((x, a)), Some((y, b))) = (ts.next(), ts.next()) else {
            return Ok(None);
        };
        let (u, v) = (index[x], index[y]);
        if !trees.union(u, v) {
            return Ok(None);
        }
        adj[u].push(edges.len());
        adj[v].push(edges.len());
        edges.push((u, v, a, b, &c.lin.constant));
    }
    // The message along edge `e` from its end `from` to its other end, given `from`'s values.
    let sent = |e: usize, from: usize, d: &Ends| {
        let (u, _, a, b, k) = edges[e];
        if from == u {
            ends_sent(d, a, b, k)
        } else {
            ends_sent(d, b, a, k)
        }
    };
    let other = |e: usize, from: usize| {
        let (u, v, ..) = edges[e];
        if from == u { v } else { u }
    };
    // Each tree walked from a root: the atoms in walk order, each with the edge to its parent.
    let mut seen = vec![false; n];
    let mut walk: Vec<usize> = Vec::with_capacity(n);
    let mut up_edge: Vec<Option<usize>> = vec![None; n];
    for r in 0..n {
        if seen[r] {
            continue;
        }
        seen[r] = true;
        let mut stack = vec![r];
        while let Some(i) = stack.pop() {
            walk.push(i);
            for &e in &adj[i] {
                let j = other(e, i);
                if !seen[j] {
                    seen[j] = true;
                    up_edge[j] = Some(e);
                    stack.push(j);
                }
            }
        }
    }
    // From the leaves up: each atom's values over its subtree, and the message to its parent.
    let mut below: Vec<Ends> = own.clone();
    let mut to_parent: Vec<Ends> = vec![(None, None); n];
    for &i in walk.iter().rev() {
        if let Some(e) = up_edge[i] {
            to_parent[i] = sent(e, i, &below[i]);
            let p = other(e, i);
            below[p] = range_meet(&below[p], &to_parent[i]);
        }
    }
    // From the roots down: the message from each atom's parent, from the parent's values over
    // all but that atom's subtree, met from the other children's messages on each side.
    let mut from_parent: Vec<Ends> = vec![(None, None); n];
    for &i in &walk {
        let kids: Vec<(usize, usize)> = (adj[i].iter())
            .map(|&e| (e, other(e, i)))
            .filter(|&(e, j)| up_edge[j] == Some(e))
            .collect();
        let base = range_meet(&own[i], &from_parent[i]);
        let mut suffix: Vec<Ends> = vec![(None, None); kids.len() + 1];
        for t in (0..kids.len()).rev() {
            suffix[t] = range_meet(&suffix[t + 1], &to_parent[kids[t].1]);
        }
        let mut prefix = base;
        for (t, &(e, j)) in kids.iter().enumerate() {
            from_parent[j] = sent(e, i, &range_meet(&prefix, &suffix[t + 1]));
            prefix = range_meet(&prefix, &to_parent[j]);
        }
    }
    let ends: Vec<Ends> = (0..n)
        .map(|i| range_meet(&below[i], &from_parent[i]))
        .collect();
    let none = ends.iter().any(range_is_empty);
    let fin = |e: &Option<Int>, inf: End| e.as_ref().map_or(inf, |v| End::Fin(Num::from(v)));
    Ok(Some(
        (atoms.into_iter().zip(&ends))
            .map(|(a, e)| {
                let set = if none {
                    IntervalSet::empty()
                } else {
                    IntervalSet::range(fin(&e.0, End::NegInf), fin(&e.1, End::PosInf))
                };
                (a.clone(), set)
            })
            .collect(),
    ))
}

/// A smaller formula `g` with the same values of each atom `keep` holds at its points as `f`,
/// and a point exactly where `f` has one, by two exact steps on the conjuncts of `f`; `None`
/// where neither changes `f`. `f` has no product atom.
/// 1. Each disjunction that the rule of module `absorbing` shows to change no answer read over
///    the atoms other than those private to one of its disjuncts is removed; an atom `keep`
///    holds is never private, so `∃P f ≡ ∃P f'` over those atoms `P` (the proof: `absorb` in
///    `presburger.rs`), and the values of each kept atom at the points of `f` and of `f'` are
///    the same, as is whether there is a point.
/// 2. The rows `R` of what is left, `R ∧ D` with `D` the conjuncts that are not rows, are
///    replaced by `K`, `R` with every atom eliminated that `keep` does not hold and `D` does
///    not read ([`super::eliminated`], exact over the integers, `None` where it is not, and
///    `R` is then kept): `K` holds at a point of its atoms exactly where `R` holds at some
///    values of the atoms eliminated, which `D` does not read, so `∃E (R ∧ D) ≡ K ∧ D`.
///
/// The cover then asks its questions of `g`, whose rows are those `D` and the kept atoms reach.
// Complexity tradeoff: the cover asked each question of the whole formula, so a star of n
// leaves, each with a disjunction tied to the hubs, cost a run of the solver on O(n) rows a
// question, past the work limit at 770 leaves (`l01_38_omega_test::bench::names::project_each_
// on_tied_disjunctions_scales`, refused with Questions). The solver itself removes those
// disjunctions first (`absorb`, COMPLEXITY.md row DECIDE-disj-chain) and projects each
// disjunct with the base eliminated onto its atoms (`project_parts`, its kernels, Pugh's exact
// projection, Pugh 1991/1992, sec. 2.3.2, doi:10.1145/125826.125848 and
// doi:10.1145/135226.135233, in the crate root's References); the cover did
// neither. Used: the same two steps, once for
// each part of a call, keeping every symbol of the call: the rule reads each row and each
// disjunct once, O(t log t) for t terms, a conjunct that is not a disjunction of rows read once
// for its atoms (a part shared by k such conjuncts is read k times). That reading is not
// charged, as [`split`], the pass of the same kind before it, is not; the elimination is
// metered as the solver meters it (`eliminated_counted`), so a shadow that grows is refused at
// the limit and the formula is then covered whole. Run once for each symbol, with only that
// symbol kept, it removed more, but cost O(k t) for k symbols, quadratic on the callers that
// project every atom (`Scope::framed`). Naive alternative: the questions of the whole formula,
// each O(n) or more. Trigger: a formula whose disjunctions are few or private, linked through
// rows; a formula whose disjunctions read most of its atoms keeps them, and the cover asks its
// questions of nearly the whole of it, as before.
fn reduced(
    f: &Formula,
    keep: &dyn Fn(&Atom) -> bool,
    work: &mut Work,
) -> Result<Option<Formula>, Refusal> {
    let conjuncts = f.conjuncts();
    let mut rows: Vec<&Con> = Vec::new();
    let mut rest: Vec<&Formula> = Vec::new();
    for g in conjuncts {
        match g {
            Formula::Con(c) => rows.push(c),
            g => rest.push(g),
        }
    }
    if rest.is_empty() {
        // A conjunction of rows, which [`direct`] reads as it is.
        return Ok(None);
    }
    // Each conjunct as a disjunction of arms: a disjunct of rows alone is read by the rule, any
    // other part is nested, and holds its atoms.
    fn atoms_in(g: &Formula) -> Vec<&Atom> {
        let mut out: Vec<&Atom> = Vec::new();
        each_constraint(g, |c| out.extend(c.lin.terms.keys()));
        out
    }
    fn arm(g: &Formula) -> absorbing::Arm<'_> {
        let flat: Option<Vec<&Con>> = match g {
            Formula::Con(c) => Some(vec![c]),
            Formula::And(gs) => (gs.iter())
                .map(|h| match h {
                    Formula::Con(c) => Some(c),
                    _ => None,
                })
                .collect(),
            _ => None,
        };
        let atoms = atoms_in(g);
        match flat {
            Some(rows) => absorbing::Arm {
                rows,
                nested: false,
                atoms,
            },
            None => absorbing::Arm {
                rows: Vec::new(),
                nested: true,
                atoms,
            },
        }
    }
    let arms: Vec<Vec<absorbing::Arm<'_>>> = (rest.iter())
        .map(|g| match g {
            Formula::Or(ds) => ds.iter().map(arm).collect(),
            g => vec![absorbing::Arm {
                rows: Vec::new(),
                nested: true,
                atoms: atoms_in(g),
            }],
        })
        .collect();
    let (removed, _) = absorbing::removable(&rows, &arms, keep);
    let left: Vec<&Formula> = (rest.iter().zip(&removed))
        .filter(|(_, r)| !**r)
        .map(|(g, _)| *g)
        .collect();
    let want: HashSet<&Atom> = arms
        .iter()
        .zip(&removed)
        .filter(|(_, r)| !**r)
        .flat_map(|(ds, _)| ds.iter().flat_map(|d| d.atoms.iter().copied()))
        .collect();
    let owned: Vec<Con> = rows.iter().map(|&c| c.clone()).collect();
    let counted = work.solver.eliminated_counted;
    let kernel = work.metered(|| counted(&owned, &|a| keep(a) || want.contains(a)))?;
    let changed_rows = kernel.as_ref().is_some_and(|k| *k != owned);
    if !changed_rows && left.len() == rest.len() {
        return Ok(None);
    }
    let rows = kernel.unwrap_or(owned);
    let parts = (rows.into_iter().map(Formula::Con)).chain(left.into_iter().cloned());
    Ok(Some(Formula::and(parts.collect())))
}

/// The values of `s` at which the conjunction `rows` has a point, by [`super::eliminated`];
/// `None` where an atom cannot be eliminated exactly. Its rows charged to `work`.
fn projected(rows: &[Con], s: &Atom, work: &mut Work) -> Result<Option<IntervalSet>, Refusal> {
    Ok(work
        .eliminate(rows, &|a| a == s)?
        .map(|left| bounded(&left, s)))
}

/// The atoms of `rows` other than `s`.
fn others(rows: &[Con], s: &Atom) -> HashSet<Atom> {
    (rows.iter())
        .flat_map(|k| k.lin.terms.keys())
        .filter(|a| *a != s)
        .cloned()
        .collect()
}

/// The values of `s` at which the conjunction `rows` has a point, `within` the set `s` is known
/// to lie in (the hull of the solver's set, or every value): [`projected`] where its
/// elimination is exact; else, where `s` is read by `rows` and so the elimination stopped at a
/// stride of another atom, Pugh's exact projection ([`projection::pugh`], a union of stride
/// sets) of `rows` with the ends of `within` added as rows, its ranges kept and its strides as
/// ranges met with a class. `None` where neither gives a set of ranges (a stride with no end).
///
/// Why the ends may be added: every value of `s` with a point of the formula lies in the
/// solver's set (`exact_each`), so in its hull, and the projection of `rows ∧ within` is that of
/// `rows` met with `within`. Where `rows` is a disjunct of a part of a split formula whose other
/// part has no point, the answer is made empty by `exact_each` anyway. [`direct`] combines the
/// blocks' sets only by union and meet, and both commute with meeting the hull `H`:
/// `(A ∩ H) ∪ (B ∩ H) = (A ∪ B) ∩ H` and `(A ∩ H) ∩ (B ∩ H) = (A ∩ B) ∩ H`. So its answer is the
/// exact projection met with `H`, which is the exact projection, since that lies in `H`.
fn block_set(
    rows: &[Con],
    s: &Atom,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<Option<Classed>, Refusal> {
    if let Some(set) = projected(rows, s, work)? {
        return Ok(Some(Classed::plain(set)));
    }
    if !rows.iter().any(|c| c.lin.terms.contains_key(s)) {
        return Ok(None);
    }
    let mut bounded_rows = rows.to_vec();
    if let Some((lo, hi)) = within.bounds() {
        let ends = [(lo, Int::from(1)), (hi, Int::from(-1))];
        for (end, sign) in ends {
            if let End::Fin(v) = end {
                // `s - lo >= 0`, `hi - s >= 0`.
                let lin = Lin {
                    terms: [(s.clone(), sign.clone())].into_iter().collect(),
                    constant: -&(&sign * &Int::from(v)),
                };
                bounded_rows.push(Con { lin, rel: Rel::Ge });
            }
        }
    }
    let parts = projection::pugh(&bounded_rows, s, within, work)?;
    // Complexity tradeoff: naive version (before PRES-interval-strided-piece), each value of a
    // part with a step of 2 or more listed as a range of its own, O(v) pieces for v values, and
    // every later join, meet and reader of the answer O(v) too: holes-cut and split-moved of
    // `l01_39_scope_relations::xst::s4::bench` answered each of O(n) calls with O(n) values one
    // a piece (1,044 pieces at size 512), O(n^2). Used: each such part kept as its range, its
    // first value to its last, met with its class ([`Classed`]), O(p) for p parts, where every
    // part with a step shares one class; where they do not, or a part of step 1 is joined to
    // one with a step, the join lists the values ([`Classed::join`]), O(v) as before. The work
    // charged is the same as listing's, each value [`LISTED`] and each value a piece, counted
    // and not listed, so the same calls are refused at the limit, and every answer is the same
    // set as before, written another way.
    let mut ranges: Vec<(End, End)> = Vec::new();
    let mut strided: Vec<Classed> = Vec::new();
    let mut values: u64 = 0;
    for p in parts {
        if p.step == Int::from(1) {
            let lo = p.lo.as_ref().map_or(End::NegInf, fin);
            let hi = p.hi.as_ref().map_or(End::PosInf, fin);
            ranges.push((lo, hi));
            continue;
        }
        // Complexity tradeoff (PRES-one-block-changes-goal, 2026-11-19): naive version, a
        // stride declined here (except inside [`cut_at_shared`]) and left to the cover, which
        // asks the solver of the whole formula and so does O(v) work for v values in every
        // call: `l01_39_reduced_product::scaling::bench::changes_of_one_block_hold_bounded_memory`,
        // where each step's `a + 2b == c` makes `a` a stride of about c/2 values, took 10.3
        // times the work at 8n (`cells_cover` grew from 814 M to 1,362 M bytes at size 1280 as
        // the stride grew). It was declined because the preimage stage's check that the boxes
        // are exact wrote each box as one disjunct a value, slower than linear in the values
        // (`l01_25` `bench::s22::remainder_chains_in_the_linear_stage_scale` past 60 s, 16ffcad7e).
        // That check now writes a box that is a progression as its range and a congruence
        // (`zedc-preimage` `linear`), so the stride is kept here as its range met with its class,
        // O(1) pieces: 8.5 times the work at 8n on the bench above, 0.99 on the s22 bench, and
        // the 25 cases of l01_25 `s22` refused while the stride was declined are answered
        // (PRES-direct-stride-answer-downstream). The work charged is
        // still that of listing each value, as below.
        let (Some(lo), Some(hi)) = (&p.lo, &p.hi) else {
            return Ok(None);
        };
        let first = lo + &(&p.res - lo).mod_floor(&p.step);
        if &first > hi {
            continue;
        }
        // The values `first, first + step, ..., <= hi`, counted.
        let count = (&(hi - &first).div_floor(&p.step) + &Int::from(1)).to_i128();
        let count = count
            .and_then(|c| u64::try_from(c).ok())
            .unwrap_or(u64::MAX);
        // Each value charged [`LISTED`], as `projection::listed` charges its own.
        work.charge(super::meter::LISTED.saturating_mul(count))?;
        values = values.saturating_add(count);
        strided.push(Classed::new(
            IntervalSet::range(fin(&first), fin(hi)),
            Congruence::new(Num::from(&p.step), Num::from(&p.res)),
        ));
    }
    work.charge(PIECE.saturating_mul((ranges.len() as u64).saturating_add(values) + 1))?;
    // One union of all, not one per class ([`Classed::join_all`]).
    let plain = Classed::plain(IntervalSet::from_pieces(ranges));
    Ok(Some(Classed::join_all(
        std::iter::once(plain).chain(strided),
    )))
}

/// A part of [`direct`] as a set: rows projected; a disjunction of blocks, the union of their
/// projections.
fn as_set(
    p: Part,
    s: &Atom,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<Option<(Classed, HashSet<Atom>)>, Refusal> {
    Ok(match p {
        Part::Set(set, atoms, ..) => Some((set, atoms)),
        Part::Rows(rows) => block_set(&rows, s, within, work)?.map(|set| (set, others(&rows, s))),
        Part::Alts(blocks, _) => blocks_set(&blocks, s, within, work)?,
    })
}

/// A disjunction of blocks as a set: the union of their projections, with the atoms other than
/// `s` the blocks read.
fn blocks_set(
    blocks: &[Vec<Con>],
    s: &Atom,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<Option<(Classed, HashSet<Atom>)>, Refusal> {
    let mut each = Vec::with_capacity(blocks.len());
    let mut atoms = HashSet::new();
    for b in blocks {
        let Some(p) = block_set(b, s, within, work)? else {
            return Ok(None);
        };
        each.push(p);
        atoms.extend(others(b, s));
    }
    // One union of all, not one per block: O(k log k) for k blocks of one range each, where
    // joining each in turn was O(k^2) ([`Classed::join_all`]).
    Ok(Some((Classed::join_all(each), atoms)))
}

/// The union of disjuncts for [`direct`]: where every disjunct is rows or blocks of rows, the
/// blocks, unprojected; else the union of their projections.
fn joined_parts(
    parts: Vec<Part>,
    s: &Atom,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<Option<Part>, Refusal> {
    // Complexity tradeoff: naive version, the blocks of every part copied into a new list, so a
    // chain of k disjunctions each holding the one below (an `if` chain) moved O(k) blocks at
    // each, O(k^2). Used: each list moved into the longest, O(k log k) moves over the chain,
    // and the bounds joined in O(min) each ([`dirs_join`]).
    if parts.iter().all(|p| !matches!(p, Part::Set(..))) {
        let mut blocks: Vec<Vec<Con>> = Vec::new();
        let mut dirs: Option<Dirs> = None;
        for p in parts {
            let (mut more, d) = match p {
                Part::Rows(rows) => {
                    let d = dirs_of(&rows);
                    (vec![rows], d)
                }
                Part::Alts(more, d) => (more, d),
                Part::Set(..) => unreachable!("no set among the parts"),
            };
            if more.len() > blocks.len() {
                std::mem::swap(&mut blocks, &mut more);
            }
            blocks.append(&mut more);
            dirs = Some(match dirs {
                None => d,
                Some(have) => dirs_join(have, d),
            });
        }
        return Ok(Some(Part::Alts(blocks, dirs.unwrap_or_default())));
    }
    let mut each = Vec::with_capacity(parts.len());
    let mut atoms: HashSet<Atom> = HashSet::new();
    let mut dirs: Option<Dirs> = None;
    for p in parts {
        let d = part_dirs(&p);
        dirs = Some(match dirs {
            None => d,
            Some(have) => dirs_join(have, d),
        });
        let Some((p, more)) = as_set(p, s, within, work)? else {
            return Ok(None);
        };
        each.push(p);
        if more.len() > atoms.len() {
            atoms = more.into_iter().chain(atoms).collect();
        } else {
            atoms.extend(more);
        }
    }
    // One union of all, not one per part ([`Classed::join_all`]).
    let set = Classed::join_all(each);
    Ok(Some(Part::Set(set, atoms, dirs.unwrap_or_default(), None)))
}

/// The bounds of a part ([`Dirs`]).
fn part_dirs(p: &Part) -> Dirs {
    match p {
        Part::Rows(rows) => dirs_of(rows),
        Part::Set(_, _, d, _) | Part::Alts(_, d) => d.clone(),
    }
}

/// The conjuncts `parts` less each disjunction of one-row blocks (a negated equation `t != 0`,
/// say) that the other conjuncts imply: one of its rows holds wherever the bounds of the rows
/// and of the other disjunctions of blocks hold ([`implied`]). Such a disjunction holds at every
/// point of the others, so the conjunction has the same points without it. Only rows, projected
/// parts and disjunctions with a block of two or more rows give bounds, so no dropped part is
/// read as evidence for another. The bounds of a projected part hold at the points of the
/// formula it was read from, so the formula, and its projection, are those of the conjunction.
// Complexity tradeoff: in an `if` chain whose guards are equations (`s22`
// `relational_equal_guards_scale`), each level is `t_i != 0 ∧ (inner ∨ arm)`, which `met`
// declined (a group with two disjunctions), and the cover then asked O(k) questions of the
// whole formula, one for each few values of the answer, O(k^2) in all, past the work limit at
// k = 64. Distributing the two disjunctions keeps it exact but copies the inner blocks at each
// level, O(k^2) too. Used: bounds kept with each disjunction ([`Dirs`], joined at a
// disjunction in O(min) and met at a conjunction in O(rows)); every block of `inner ∨ arm`
// has the equation of a later guard, whose bound on `t_i`'s term implies `t_i != 0`, so it is
// dropped here in O(|bounds|) and the level costs O(1) more. A disjunction not shown implied
// is kept, and `met` goes on as before.
fn implied_dropped(mut parts: Vec<Part>, work: &mut Work) -> Result<Vec<Part>, Refusal> {
    let candidate = |p: &Part| matches!(p, Part::Alts(bs, _) if bs.iter().all(|b| b.len() == 1));
    if parts.len() < 2 || !parts.iter().any(candidate) {
        return Ok(parts);
    }
    let mut d = Dirs::new();
    for p in &parts {
        match p {
            Part::Rows(rows) => {
                work.read(rows.len() as u64)?;
                dirs_meet(&mut d, dirs_of(rows));
            }
            Part::Set(_, _, more, _) => {
                work.read(more.len() as u64)?;
                dirs_meet(&mut d, more.clone());
            }
            Part::Alts(_, more) if !candidate(p) => {
                work.read(more.len() as u64)?;
                dirs_meet(&mut d, more.clone());
            }
            Part::Alts(..) => {}
        }
    }
    if d.is_empty() {
        return Ok(parts);
    }
    let mut checked = 0u64;
    parts.retain(|p| match p {
        Part::Alts(bs, _) if candidate(p) => {
            checked += bs.len() as u64;
            !bs.iter().any(|b| implied(&b[0], &d))
        }
        _ => true,
    });
    work.read(checked)?;
    Ok(parts)
}

/// The meet of conjuncts for [`direct`]: rows alone stay rows; else the groups that share no
/// atom but `s`, each projected, met. A group of rows `R` (possibly none) and one disjunction
/// of blocks `B1 ∨ ... ∨ Bk` projects as the union of the projections of `R ∧ Bi`; where it is
/// the only group, it stays the blocks `R ∧ Bi`, unprojected, for a conjunction above it.
fn met(
    parts: Vec<Part>,
    s: &Atom,
    within: &IntervalSet,
    cut: bool,
    work: &mut Work,
) -> Result<Option<Part>, Refusal> {
    let mut parts = implied_dropped(parts, work)?;
    // A lone part is the conjunction: kept as it is, a disjunction's blocks not copied (the
    // steps below give the same part, a copy of it).
    if parts.len() == 1 {
        return Ok(parts.pop());
    }
    if parts.iter().all(|p| matches!(p, Part::Rows(_))) {
        let mut all: Vec<Con> = Vec::new();
        for p in parts {
            if let Part::Rows(mut rows) = p {
                if rows.len() > all.len() {
                    std::mem::swap(&mut rows, &mut all);
                }
                all.extend(rows);
            }
        }
        return Ok(Some(Part::Rows(all)));
    }
    // The items: each row, then each projected part, joined through the atoms they read.
    let mut rows: Vec<Con> = Vec::new();
    let mut sets: Vec<(Classed, HashSet<Atom>)> = Vec::new();
    // Each disjunction of blocks, with the atoms other than `s` its blocks read, an item of its
    // own after the sets.
    let mut alts: Vec<(Vec<Vec<Con>>, HashSet<Atom>)> = Vec::new();
    // The bounds of each of `sets` and `alts`, in their order, and the blocks each of `sets`
    // was projected from, where it was a shared disjunction.
    let mut set_blocks: Vec<Option<Rc<[Vec<Con>]>>> = Vec::new();
    let mut set_dirs: Vec<Dirs> = Vec::new();
    let mut alt_dirs: Vec<Dirs> = Vec::new();
    for p in parts {
        match p {
            Part::Rows(r) => rows.extend(r),
            Part::Set(set, atoms, d, blocks) => {
                sets.push((set, atoms));
                set_dirs.push(d);
                set_blocks.push(blocks);
            }
            Part::Alts(blocks, d) => {
                let atoms = blocks.iter().flat_map(|b| others(b, s)).collect();
                alts.push((blocks, atoms));
                alt_dirs.push(d);
            }
        }
    }
    let r0 = rows.len();
    let a0 = r0 + sets.len();
    let n = a0 + alts.len();
    let mut parent = UnionFind::new(n);
    let mut first: HashMap<&Atom, usize> = HashMap::new();
    let items = (rows.iter().enumerate())
        .flat_map(|(i, k)| k.lin.terms.keys().map(move |a| (i, a)))
        .chain(
            (sets.iter().enumerate())
                .flat_map(|(j, (_, atoms))| atoms.iter().map(move |a| (r0 + j, a))),
        )
        .chain(
            (alts.iter().enumerate())
                .flat_map(|(j, (_, atoms))| atoms.iter().map(move |a| (a0 + j, a))),
        );
    let mut read = 0u64;
    for (i, a) in items {
        read += 1;
        if a == s {
            continue;
        }
        let j = *first.entry(a).or_insert(i);
        // The least index the root, so that a group, and the order of `groups` below, do not
        // depend on the order a hash set of atoms is read in (Sol, round 2 of PRES-pugh-xr).
        parent.union_least(i, j);
    }
    work.read(read)?;
    // Ordered, so that the work charged before a group not shown exact is the same on every run.
    type Group = (Vec<Con>, Vec<usize>, Vec<usize>);
    let mut groups: BTreeMap<usize, Group> = BTreeMap::new();
    for (i, k) in rows.iter().enumerate() {
        let r = parent.find(i);
        groups.entry(r).or_default().0.push(k.clone());
    }
    for j in 0..sets.len() {
        let r = parent.find(r0 + j);
        groups.entry(r).or_default().1.push(j);
    }
    for j in 0..alts.len() {
        let r = parent.find(a0 + j);
        groups.entry(r).or_default().2.push(j);
    }
    // `R ∧ Bi` for each block `Bi`, every row copied charged, and at least one unit a block, so
    // that empty blocks are not copied free (round-1 cross-review of
    // PRES-cover-moduli-two-disjunctions, gemini seat: m empty blocks on each side of two
    // disjunctions made m² copies for O(m) work,
    // `two_disjunctions_empty_blocks_charge_work_per_block`).
    let distribute = |group: &[Con], blocks: &[Vec<Con>], work: &mut Work| {
        let mut out = Vec::with_capacity(blocks.len());
        for b in blocks {
            work.read(((group.len() + b.len()) as u64).max(1))?;
            let mut block = group.to_vec();
            block.extend(b.iter().cloned());
            out.push(block);
        }
        Ok::<_, Refusal>(out)
    };
    // One disjunction and rows: `R ∧ (B1 ∨ … ∨ Bn)` is `(R ∧ B1) ∨ … ∨ (R ∧ Bn)` whether or
    // not the rows read the blocks' atoms, so every row is distributed, and the part stays
    // blocks. Projected by groups instead, rows apart from the blocks would lose their link
    // to the rows of a holder (an `if` arm `x == y + j && (case split of q)`: `x == y + j` is
    // a group of its own, its projection on `y` the whole line, and the box on `x` of the
    // holder could not be met with it).
    // Complexity tradeoff: O(|R| · n) rows copied, charged, where projecting each group is
    // O(|R|) and a set; the set made `direct` decline the holder, and the cover asked O(k)
    // questions of O(k) work on an `if` chain of k equation guards
    // (`l01_25_preimage_catalog::bench::s22::relational_equal_guards_scale`, refused at
    // k = 64). Each level of a chain that adds rows beside the chain below copies them into
    // every block below, as the single group always did.
    if sets.is_empty() && alts.len() == 1 {
        let (blocks, _) = alts.pop().expect("one disjunction");
        // Every block of `R ∧ Bi` holds `R` and `Bi`, so both one's bounds.
        let mut dirs = alt_dirs.pop().expect("one disjunction");
        dirs_meet(&mut dirs, dirs_of(&rows));
        return Ok(Some(Part::Alts(distribute(&rows, &blocks, work)?, dirs)));
    }
    let mut set = Classed::plain(IntervalSet::top());
    for (group, held, ors) in groups.values() {
        let p = match (group.is_empty(), held.as_slice(), ors.as_slice()) {
            (false, [], []) => match block_set(group, s, within, work)? {
                Some(p) => p,
                None => return Ok(None),
            },
            (true, [j], []) => sets[*j].0.clone(),
            // Rows linked to a shared disjunction, projected, through its other atoms: its set
            // lost the link, its blocks keep it. `R ∧ (B1 ∨ … ∨ Bn)` is `(R ∧ B1) ∨ … ∨
            // (R ∧ Bn)`, each projected exactly.
            // Complexity tradeoff: declining here sent the whole formula to the cover, one
            // question for each gap piece at O(size) work each, so O(k²) on an `if` chain of k
            // equation guards (`l01_25_preimage_catalog::bench::s22::relational_equal_guards_
            // scale`, refused at k = 64). Distributed, it is O(|R| · Σ|Bi|) work, charged, read
            // once by this holder; the result is a set, never blocks, so no holder copies a copy
            // and the exponential growth of distributing shared parts (`direct_noting`) cannot
            // return. Two or more holders each pay their own copy, as each pays its own rows.
            (false, [j], []) if set_blocks[*j].is_some() => {
                let held = set_blocks[*j].as_deref().expect("blocks kept");
                match blocks_set(&distribute(group, held, work)?, s, within, work)? {
                    Some((p, _)) => p,
                    None => return Ok(None),
                }
            }
            (_, [], [j]) => {
                let blocks = distribute(group, &alts[*j].0, work)?;
                match as_set(Part::Alts(blocks, Dirs::new()), s, within, work)? {
                    Some((p, _)) => p,
                    None => return Ok(None),
                }
            }
            // Only where `cut`: the inner call of `cut_at_shared` (cut false) declines a group
            // of two or more disjunctions, so the cut stays linear (round-1 cross-review,
            // gemini seat: distributing there made three disjunctions quadratic, and two that
            // the cut declines distributed twice).
            (_, [], [_, _, ..]) if cut => {
                match (cut_at_shared(group, ors, &alts, s, work)?, ors.as_slice()) {
                    (Some(true), _) => Classed::plain(IntervalSet::range(End::NegInf, End::PosInf)),
                    (Some(false), _) => Classed::plain(IntervalSet::empty()),
                    (None, [i, j]) => {
                        match two_distributed(group, &alts[*i].0, &alts[*j].0, s, within, work)? {
                            Some(p) => p,
                            None => return Ok(None),
                        }
                    }
                    (None, _) => return Ok(None),
                }
            }
            _ => return Ok(None),
        };
        set = set.meet(&p);
    }
    let mut atoms = others(&rows, s);
    for (_, more) in sets {
        atoms.extend(more);
    }
    for (_, more) in alts {
        atoms.extend(more);
    }
    // Every point of the conjunction holds each part, so each part's bounds.
    let mut dirs = dirs_of(&rows);
    for d in set_dirs.into_iter().chain(alt_dirs) {
        dirs_meet(&mut dirs, d);
    }
    Ok(Some(Part::Set(set, atoms, dirs, None)))
}

/// The projection onto `s` of a group of [`met`] with rows `group` and exactly two disjunctions
/// of blocks `a` and `b` (no projected part), where [`cut_at_shared`] does not answer it (the
/// group reads `s`, or no atom is shared by both): the answer is the union over the pairs
/// `(i, j)` of the projections of `R ∧ Ai ∧ Bj`, each a group of rows that [`met`] projects,
/// over only the pairs that can have a point. `None` where one of those is not shown exact.
///
/// Which pairs: each block's range of each atom that a row of it reads alone bounds, met with
/// the group's ([`atom_ranges`]); a block with no point by these is left out, and a pair whose
/// ranges miss on an atom has no point ([`ranges_meet`]). The pairs are found by a sweep over one
/// atom `t` ([`sweep_atom`]): only the pairs whose ranges of `t` meet
/// ([`zed_collections::intervals::meeting_pairs`], Bentley and Wood 1980), all pairs where no
/// atom is bounded on both sides. Every pair with a point is among them: at that point `t` lies
/// in the range of both blocks, so the two ranges meet. The sweep is the round-1 cross-review's
/// (gemini seat, its patch's per-block ranges and interval sweep, rewritten here on
/// `unary_bound` and the shared `meeting_pairs`).
///
/// Exact: `R ∧ (A1 ∨ … ∨ Ap) ∧ B` is `(R ∧ A1 ∧ B) ∨ … ∨ (R ∧ Ap ∧ B)` (conjunction distributes
/// over disjunction), and a value of `s` has a point of a disjunction exactly when it has a
/// point of one of its disjuncts, so the projection of the union is the union of the
/// projections, each exact by [`met`]'s rule for one disjunction.
///
/// PRES-cover-moduli-two-disjunctions (pres8, 2026-11-20): in every group of the 16 cases of
/// l01_25
/// `s22::the_cover_answers_where_the_solver_alone_answered_on_three_shapes_at_moduli_5_and_7`
/// declined here before this change (14 still refused when it was made, after
/// PRES-project-each-naming), one disjunction is the outer `if` of the shape
/// (`if x >= 0 {c} else {y}`, `if y >= 0 {c} else {y}` or `if c >= 1 {y} else {-y}`), 2 blocks, and
/// the other the remainder chain, 8 to 27 blocks; the two share the chain's result atom (and `s`),
/// so the group is one and the cover asked 11 to 36 questions of the whole formula, past
/// `EXACT_LIMIT`. Distributed, 2 copies of the chain.
///
/// Complexity tradeoff: naive version, declining (`None`), so the cover asks its questions of
/// the whole formula, each O(size) work, one for each few values of the answer. Used: first
/// [`two_ranges_of_one_value`], O(N log N) for N rows, where every row reads one value; else
/// the ranges, O(rows(A) + rows(B) + p·|R|) for p = |A|, q = |B| (each block's map starts from
/// the group's ranges it reads), the sweep, O((p + q) log(p + q) + k) for the k pairs whose
/// ranges of `t` meet, and for each of those a check, O(atoms bounded), and, where it passes, a
/// copy of |R| + |Ai| + |Bj| rows and its projection; then the union ([`Classed::join_all`]).
/// Where the blocks of each side are pairwise disjoint on `t` (the remainder chain's blocks
/// are, and two partitions of one atom are), k <= p + q (proof at `meeting_pairs`: each pair
/// is given to its interval that ends first, which is given at most one), so the whole is
/// O((p + q) log(p + q) + (p + q)·|R| + rows): two disjunctions of n disjoint ranges each,
/// empty answer, 58.55 times the instructions per eightfold n before the sweep (round-1
/// gemini seat's test `two_disjunctions_disjoint_on_shared_atom_scale_near_linear`), below 9
/// with it. Where they are not, up to p·q pairs: that answer alone can have p·q/2 pieces
/// (below), so no method is linear there; a product whose pairs pass what is left of the
/// allowance of [`tried`] is declined once they are counted, before any is formed
/// ([`past_what_is_left`]), and goes to the cover as before, and nothing answered before is
/// refused for it.
/// That quadratic case is QUESTIONS.md A171 for the author.
///
/// Why no method is linear in |A| + |B| in general (counting rows and pieces, as `work` does):
/// the answer alone can have |A| · |B| pieces. Let `A` be the blocks `t == M·2^i` (i < n) and
/// `B` the blocks `t == s + 2^j` (j < n), with `M > 2^(n+2)`: the projection onto `s` is the
/// n² values `M·2^i - 2^j`, all distinct, and no three of them are in arithmetic progression
/// (from `v1 + v3 == 2·v2`, `M·(2^i1 + 2^i3 - 2^(i2+1)) == 2^j1 + 2^j3 - 2^(j2+1)`, whose
/// right side is below `M` in size, so both sides are 0, and a sum of two powers of 2 is
/// `2^(k+1)` only as `2^k + 2^k`: `i1 == i2 == i3` and `j1 == j2 == j3`). So a piece, a range
/// met with one class (an arithmetic progression of members only), holds at most two of
/// them, and the answer has at least n²/2 pieces (test
/// `the_answer_of_two_disjunctions_can_have_n_squared_pieces`, round-1 cross-review, claude seat:
/// n² - n pieces at n = 3 and 6, as `M·2^i - 2` and `M·2^i - 1` are adjacent and make one
/// range). Here M has O(n) bits, so the input has
/// O(n²) bits. The bound holds in bits too, with input of O(n log n) bits (round-1
/// cross-review, codex seat, checked by its probe `projection-bounds.rs` and by the derivation
/// here): take for the a_i and b_j the n = 2^d numbers below 3^d whose ternary digits are 0
/// and 1, and M = 3^d, each constant O(d) = O(log n) bits; from `v1 + v3 == 2·v2`,
/// `M·(a1 + a3 - 2·a2) == b1 + b3 - 2·b2`, whose right side is at most 3^d - 1 in size, so
/// both are 0, and `a1 + a3 == 2·a2` with digits 0 and 1 adds with no carry, so digit by digit
/// `a1 == a2 == a3` (a set with no three terms in arithmetic progression, Salem and Spencer
/// 1942, doi:10.1073/pnas.28.12.561), and so for the b. Deciding emptiness alone is no easier
/// (codex seat, round 1; checked here): for lists a_i, b_j, c_k of 3SUM, let `A` be the blocks
/// `x == a_i`, `B` the blocks `y == b_j`, and `R` the rows `0 <= z_k <= 1`, `Σ z_k == 1` and
/// `x + y + Σ c_k·z_k == 0`. Integer `z_k` with sum 1 pick one k, so the group has a point
/// exactly when some a_i + b_j + c_k is 0, from input of linear size; a method near-linear on
/// every group would decide 3SUM in near-linear time, against the 3SUM conjecture
/// (Gajentaan and Overmars 1995, doi:10.1016/0925-7721(95)00022-2).
fn two_distributed(
    group: &[Con],
    a: &[Vec<Con>],
    b: &[Vec<Con>],
    s: &Atom,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<Option<Classed>, Refusal> {
    if TWO_DISTRIBUTED_OFF.get() {
        return Ok(None);
    }
    // A disjunction with a block of no rows holds at every point (that block, the empty
    // conjunction, does), so the group is its rows with the other disjunction alone, which
    // [`met`] projects by its rule for one disjunction, linear in the group: one pass over the
    // blocks here instead of |A|·|B| pairs (round-1 gemini seat's test
    // `two_disjunctions_empty_blocks_charge_work_per_block`: 57.6 times the instructions per
    // eightfold m before this, every pair formed).
    work.read((a.len() + b.len()) as u64)?;
    let true_in = |blocks: &[Vec<Con>]| blocks.iter().any(Vec::is_empty);
    if let Some(other) = (true_in(a).then_some(b)).or_else(|| true_in(b).then_some(a)) {
        let rows: usize = group.len() + other.iter().map(Vec::len).sum::<usize>();
        work.read((rows as u64).max(1))?;
        let parts = vec![
            Part::Rows(group.to_vec()),
            Part::Alts(other.to_vec(), Dirs::new()),
        ];
        let Some(p) = met(parts, s, within, false, work)? else {
            return Ok(None);
        };
        return Ok(as_set(p, s, within, work)?.map(|(p, _)| p));
    }
    if let Some(set) = two_ranges_of_one_value(group, a, b, s, work)? {
        return Ok(Some(set));
    }
    work.read(group.len() as u64)?;
    let empty = || Ok(Some(Classed::plain(IntervalSet::empty())));
    let Some(held) = atom_ranges(group, &HashMap::new()) else {
        return empty();
    };
    let ranges = |blocks: &[Vec<Con>], work: &mut Work| -> Result<Vec<_>, Refusal> {
        let mut out = Vec::with_capacity(blocks.len());
        for block in blocks {
            work.read((block.len() as u64).max(1))?;
            out.push(atom_ranges(block, &held));
        }
        Ok(out)
    };
    let (ra, rb) = (ranges(a, work)?, ranges(b, work)?);
    let t = sweep_atom(&ra, &rb);
    let mut each = Vec::new();
    let mut pair = |i: usize, j: usize, work: &mut Work| -> Result<Option<()>, Refusal> {
        let (Some(ma), Some(mb)) = (&ra[i], &rb[j]) else {
            return Ok(Some(()));
        };
        if !ranges_meet(ma, mb) {
            work.charge(PIECE)?;
            return Ok(Some(()));
        }
        work.read(((group.len() + a[i].len() + b[j].len()) as u64).max(1))?;
        let mut rows = group.to_vec();
        rows.extend(a[i].iter().cloned());
        rows.extend(b[j].iter().cloned());
        let Some(p) = met(vec![Part::Rows(rows)], s, within, false, work)? else {
            return Ok(None);
        };
        let Some((p, _)) = as_set(p, s, within, work)? else {
            return Ok(None);
        };
        each.push(p);
        Ok(Some(()))
    };
    match t {
        Some(t) => {
            // Each block's range of `t`; a block with no point, the empty range.
            let on_t = |m: &Option<HashMap<Atom, IntRange>>| -> IntRange {
                match m {
                    Some(m) => (m.get(t).or(held.get(t)).cloned()).unwrap_or((None, None)),
                    None => (Some(Int::from(1)), Some(Int::from(0))),
                }
            };
            let ia: Vec<IntRange> = ra.iter().map(on_t).collect();
            let ib: Vec<IntRange> = rb.iter().map(on_t).collect();
            work.read((ia.len() + ib.len()) as u64)?;
            let k = zed_collections::intervals::meeting_count(&ia, &ib);
            if past_what_is_left(k, work) {
                return Ok(None);
            }
            for (i, j) in zed_collections::intervals::meeting_pairs(&ia, &ib) {
                if pair(i, j, work)?.is_none() {
                    return Ok(None);
                }
            }
        }
        None => {
            let points = |r: &[Option<HashMap<Atom, IntRange>>]| r.iter().flatten().count() as u64;
            if past_what_is_left(points(&ra).saturating_mul(points(&rb)), work) {
                return Ok(None);
            }
            for i in 0..a.len() {
                for j in 0..b.len() {
                    if pair(i, j, work)?.is_none() {
                        return Ok(None);
                    }
                }
            }
        }
    }
    Ok(Some(Classed::join_all(each)))
}

/// Whether `pairs` pairs of [`two_distributed`] would pass what `work` has left, known before
/// any is formed: each costs at least [`PIECE`] (a pair whose ranges do not meet is charged
/// `PIECE`; one that is formed reads at least one row, [`super::meter::SOLVER_UNIT`] units,
/// more), so `pairs · PIECE` units past what is left would be refused at the limit in any case.
/// The steps: the pairs counted are exactly those the loops charge at least `PIECE` (the count
/// is of the pairs whose ranges meet, a block with no point having the empty range; on the
/// path with no ranges, of the pairs of blocks with a point); no [`Work::credit`] lies on a
/// pair's path (it is called only from [`shared_cells`], which only `exact_each_checked`
/// calls), and [`Work::exempt`], also only there, moves `used` and `limit` alike; the meter
/// refuses once `used > limit`, the strict test this one makes on `used + pairs · PIECE`; and
/// [`tried`] maps that refusal and `Ok(None)` both to `None`.
/// Declining then gives the answer that refusal gives (`None` from [`tried`]) at the cost of
/// the count alone, O((p + q) log(p + q)) ([`zed_collections::intervals::meeting_count`]),
/// instead of the limit's worth of pairs: the fast allowance of [`has_points`] is one for all
/// its parts, so a group that spent it all left no fast path for the parts after it (round-1
/// cross-review, claude seat F7 and codex seat's claim most likely wrong; before
/// `two_distributed` such a group declined at once). It also bounds the list of pairs that
/// [`zed_collections::intervals::meeting_pairs`] builds to what is left over `PIECE`, where
/// before it held all k pairs, up to p·q, whatever the limit (16 bytes each).
fn past_what_is_left(pairs: u64, work: &Work) -> bool {
    pairs.saturating_mul(PIECE) > work.limit.saturating_sub(work.used)
}

/// The range of each atom that a row of `rows` reads alone bounds, met with that atom's range in
/// `held` (the rows the block is met with); `None` where the rows have no point by these ranges
/// alone (a row of one atom with no root, a constant row that is false, or two ranges of one atom
/// that do not meet). Rows of two or more atoms, or of a product, bound nothing here.
///
/// Sound: every point of `rows ∧ held` has each atom in the range of each row of it alone
/// ([`super::slack::unary_bound`], by [`row_range`]) and in its range in `held`, so in their meet;
/// an empty meet, no point.
fn atom_ranges(rows: &[Con], held: &HashMap<Atom, IntRange>) -> Option<HashMap<Atom, IntRange>> {
    let mut out: HashMap<Atom, IntRange> = HashMap::new();
    for c in rows {
        let Some((x, r, none)) = super::slack::unary_bound(c) else {
            continue;
        };
        if none {
            return None;
        }
        let Some(x) = x else { continue };
        let range =
            (out.entry(x.clone())).or_insert_with(|| held.get(&x).cloned().unwrap_or((None, None)));
        meet_range(range, r);
        if range_is_empty(range) {
            return None;
        }
    }
    Some(out)
}

/// Whether two blocks' ranges ([`atom_ranges`], each already met with the group's) meet on every
/// atom both bound. Where they do not, the pair `R ∧ Ai ∧ Bj` has no point (its atom would lie in
/// two ranges that do not meet). An atom bounded by one block only is bounded in the other by the
/// group alone, which the first already met, so it cannot separate them. O(min(|ma|, |mb|)).
fn ranges_meet(ma: &HashMap<Atom, IntRange>, mb: &HashMap<Atom, IntRange>) -> bool {
    let (small, big) = if ma.len() <= mb.len() {
        (ma, mb)
    } else {
        (mb, ma)
    };
    small.iter().all(|(x, r)| {
        big.get(x)
            .is_none_or(|q| !range_is_empty(&range_meet(r, q)))
    })
}

/// The atom on which [`two_distributed`] sweeps its pairs: one that a block of each side bounds,
/// with a lower end on one side and an upper end on the other (only such an atom can separate a
/// pair), the one most blocks of both sides bound at both ends; ties by the order of atoms, so
/// the same atom on every run whatever the order of the maps. `None` where no atom separates.
/// Any choice gives the same answer; the choice changes only how many pairs are formed.
fn sweep_atom<'a>(
    ra: &'a [Option<HashMap<Atom, IntRange>>],
    rb: &'a [Option<HashMap<Atom, IntRange>>],
) -> Option<&'a Atom> {
    // For each atom: blocks with a lower end, an upper end, and both.
    let count = |ranges: &'a [Option<HashMap<Atom, IntRange>>]| {
        let mut n: BTreeMap<&'a Atom, (usize, usize, usize)> = BTreeMap::new();
        for (x, (lo, hi)) in ranges.iter().flatten().flatten() {
            let e = n.entry(x).or_default();
            e.0 += lo.is_some() as usize;
            e.1 += hi.is_some() as usize;
            e.2 += (lo.is_some() && hi.is_some()) as usize;
        }
        n
    };
    let (na, nb) = (count(ra), count(rb));
    let mut best: Option<((usize, usize, usize), &'a Atom)> = None;
    for (x, &(al, ah, ab)) in &na {
        let Some(&(bl, bh, bb)) = nb.get(x) else {
            continue;
        };
        let opposed = ah.min(bl) + al.min(bh);
        if opposed == 0 {
            continue;
        }
        let key = (ab.min(bb), ab + bb, opposed);
        if best.as_ref().is_none_or(|(k, _)| key > *k) {
            best = Some((key, *x));
        }
    }
    best.map(|(_, x)| x)
}

/// The projection onto `s` of the group of [`two_distributed`] where one row of `group` is
/// `s == t` (`s - t == 0` or `t - s == 0`) for an atom `t`, and every other row of `group` and
/// of the blocks of `a` and `b` reads `s` or `t` alone: then the answer is the range of the
/// other rows of `group`, met with the union of the ranges of the blocks of `a`, met with that
/// of `b`. `None` where the group is not of this form.
///
/// Exact: the group reads no atom but `s` and `t` (every row is checked), and at its points
/// `s == t`, so a point is one value v for both, and each row of one atom is a range of v
/// ([`row_range`]: `a·x + k >= 0` is `x >= ⌈-k/a⌉` for a > 0, `x <= ⌊k/-a⌋` for a < 0, an
/// equality its one root, or no value where `a` does not divide `k`). A block, a conjunction,
/// is the meet of its rows' ranges, one range; a disjunction the union of its blocks' ranges;
/// the group the meet of its rows' range and the two unions. A block with no rows is every
/// value (the empty meet). Test: `exact::tests::two_ranges_of_one_value_match_enumeration`
/// (2 000 random groups, values listed within a box, coefficients -3 to 3); it cannot catch
/// an error that shows only outside the box or at larger coefficients.
///
/// From the round-1 cross-review of PRES-cover-moduli-two-disjunctions (codex seat's
/// prototype, rewritten here on the shared [`row_range`], which also takes coefficients other
/// than ±1): two disjunctions of n disjoint ranges cost 59.5 times the work per eightfold n
/// when distributed, every pair formed though the answer is empty.
// Complexity tradeoff: naive version, the distribution of [`two_distributed`], O(|A|·|B|)
// pairs, each charged. Used: one pass over the N rows, each read by `row_range` (one or two
// floor divisions), one range per block, then two `IntervalSet::from_pieces` (sort and merge,
// O(N log N) time, O(N) bytes) and two meets, O(N) pieces: near-linear, with no pair formed.
// Measured by `disjoint_shared_intervals_scale_without_forming_pairs`.
fn two_ranges_of_one_value(
    group: &[Con],
    a: &[Vec<Con>],
    b: &[Vec<Con>],
    s: &Atom,
    work: &mut Work,
) -> Result<Option<Classed>, Refusal> {
    work.read(group.len() as u64)?;
    let wire = group.iter().position(|c| {
        let mut terms = c.lin.terms.iter();
        let (Some((x, kx)), Some((y, ky)), None) = (terms.next(), terms.next(), terms.next())
        else {
            return false;
        };
        c.rel == Rel::Eq
            && c.lin.constant.is_zero()
            && (x == s || y == s)
            && (kx == &Int::from(1) || kx == &Int::from(-1))
            && *ky == -kx
    });
    let Some(wire) = wire else {
        return Ok(None);
    };
    let t = (group[wire].lin.terms.keys())
        .find(|x| *x != s)
        .expect("the row `s == t` has an atom other than `s`")
        .clone();
    // The range of v that `rows` allow, or `None` where a row reads an atom other than `s` and
    // `t`, or more than one atom.
    let range = |rows: &mut dyn Iterator<Item = &Con>| -> Option<IntRange> {
        let mut r: IntRange = (None, None);
        for c in rows {
            let mut terms = c.lin.terms.iter();
            let (Some((x, k)), None) = (terms.next(), terms.next()) else {
                return None;
            };
            if x != s && *x != t {
                return None;
            }
            let (add, none) = row_range(k, &c.lin.constant, c.rel == Rel::Eq);
            if none {
                return Some((Some(Int::from(1)), Some(Int::from(0))));
            }
            meet_range(&mut r, add);
        }
        Some(r)
    };
    let piece = |r: IntRange| -> Option<(End, End)> {
        (!range_is_empty(&r)).then(|| {
            let end = |v: Option<Int>, inf: End| v.map_or(inf, |v| End::Fin(Num::from(&v)));
            (end(r.0, End::NegInf), end(r.1, End::PosInf))
        })
    };
    let Some(rows) = range(&mut (group[..wire].iter()).chain(&group[wire + 1..])) else {
        return Ok(None);
    };
    let mut answer = IntervalSet::from_pieces(piece(rows).into_iter().collect());
    for blocks in [a, b] {
        let mut pieces = Vec::with_capacity(blocks.len());
        for block in blocks {
            work.read(block.len() as u64 + 1)?;
            let Some(r) = range(&mut block.iter()) else {
                return Ok(None);
            };
            pieces.extend(piece(r));
        }
        answer = answer.meet(&IntervalSet::from_pieces(pieces));
    }
    Ok(Some(Classed::plain(answer)))
}

/// Whether a group of [`met`] with rows `group` and two or more disjunctions `ors` of `alts`
/// has a point, where none of it reads `s` (as in the emptiness check of [`has_points`], whose
/// `s` occurs nowhere): such a group bounds no value of `s`, so its projection onto `s` is every
/// value or none. The disjunctions are tied through atoms they share; where some atom `t` is
/// read by every one of them (the least such, so the same on every run), the group is projected
/// onto `t` by [`met`] itself, which joins its items through atoms other than `t` only, and has
/// a point exactly when that projection is not empty. `None` where no atom is shared by all, or
/// where the projection onto `t` declines (two or more disjunctions in one of its groups: that
/// inner call cuts no further and does not distribute, so the cut stays linear; the caller
/// then distributes a group of exactly two by [`two_distributed`]).
///
/// PRES-cover-refusals-moduli: in the 48 cases at moduli 5 and 7 of the l01_25 test
/// `the_cover_answers_where_the_solver_alone_answered_on_two_shapes_at_moduli_5_and_7`, 10
/// groups were declined here, each two disjunctions tied by `x` alone once the remainder atom
/// `q1` goes with the rows (a disjunction over `x` alone, and one over `x`, `q1` and `q2`), and
/// so asked as questions. The orchestrator's plan, splitting the group by the values of the
/// remainder atom, does not answer them: the disjunction over `x` alone reads no remainder,
/// so at every value of `q1` two disjunctions remain. Cost: one pass over the atoms of the
/// disjunctions to find `t`, then [`met`] on the group, linear in its rows and blocks plus
/// their projections, the same as the group would cost were it answered directly; one
/// cut per group, never nested, so a chain of tied groups cannot multiply it. Measured
/// (release, instructions less the startup run, 2026-11-18): 8.35 and 8.38 times the work per
/// eightfold n at m = 5 (n 64 to 4096), 8.18 and 8.24 at m = 40; eight times m costs no more
/// (1.25 G against 1.01 G at n = 4096).
fn cut_at_shared(
    group: &[Con],
    ors: &[usize],
    alts: &[(Vec<Vec<Con>>, HashSet<Atom>)],
    s: &Atom,
    work: &mut Work,
) -> Result<Option<bool>, Refusal> {
    let reads_s = |rows: &[Con]| rows.iter().any(|k| k.lin.terms.contains_key(s));
    work.read(group.len() as u64)?;
    if reads_s(group) {
        return Ok(None);
    }
    let mut shared: Option<HashSet<&Atom>> = None;
    for j in ors {
        let (blocks, atoms) = &alts[*j];
        work.read(blocks.iter().map(|b| b.len() as u64).sum::<u64>() + atoms.len() as u64)?;
        if blocks.iter().any(|b| reads_s(b)) {
            return Ok(None);
        }
        shared = Some(match shared {
            None => atoms.iter().collect(),
            Some(have) => have.into_iter().filter(|a| atoms.contains(*a)).collect(),
        });
    }
    let Some(t) = shared.and_then(|have| have.into_iter().min().cloned()) else {
        return Ok(None);
    };
    let mut parts = vec![Part::Rows(group.to_vec())];
    // No bounds kept with them: none is always sound, and `met` here has no `if` chain to cut.
    parts.extend((ors.iter()).map(|j| Part::Alts(alts[*j].0.clone(), Dirs::new())));
    let top = IntervalSet::top();
    let set = match met(parts, &t, &top, false, work)? {
        None => return Ok(None),
        Some(Part::Set(set, ..)) => set,
        Some(p @ (Part::Rows(_) | Part::Alts(..))) => match as_set(p, &t, &top, work)? {
            Some((set, _)) => set,
            None => return Ok(None),
        },
    };
    Ok(Some(!set.is_empty()))
}

/// A progression of values of a cell: `lo`, `lo + step`, ..., `hi`, `step` 2 or more. `absent`
/// holds the residues modulo `step` that a residue question of [`cells_cover`] found no point of
/// `f` in, with `s` from `lo` to `hi`: empty when the cell makes it.
struct Stride {
    step: Int,
    lo: Int,
    hi: Int,
    absent: IntervalSet,
}

/// The residues modulo `st.step` of the values of `found` from `st.lo` to `st.hi`, each piece
/// read charged [`PIECE`] units of `work`; a piece as long as the step holds every residue.
fn residues(found: &IntervalSet, st: &Stride, work: &mut Work) -> Result<IntervalSet, Refusal> {
    let mut have = IntervalSet::empty();
    for (l, u) in found
        .meet(&IntervalSet::range(fin(&st.lo), fin(&st.hi)))
        .pieces()
    {
        work.charge(PIECE)?;
        let (End::Fin(l), End::Fin(u)) = (l, u) else {
            continue;
        };
        let (l, u) = (Int::from(l), Int::from(u));
        if &u - &l >= &st.step - &Int::from(1) {
            return Ok(IntervalSet::range(
                fin(&Int::from(0)),
                fin(&(&st.step - &Int::from(1))),
            ));
        }
        let (a, b) = (l.mod_floor(&st.step), u.mod_floor(&st.step));
        if a <= b {
            have = have.join(&IntervalSet::range(fin(&a), fin(&b)));
        } else {
            have = have.join(&IntervalSet::range(
                fin(&a),
                fin(&(&st.step - &Int::from(1))),
            ));
            have = have.join(&IntervalSet::range(fin(&Int::from(0)), fin(&b)));
        }
    }
    Ok(have)
}

/// The pieces of `gap` from `st.lo` to `st.hi`, each cut to that span, that are shorter than
/// `st.step` and hold no value whose residue is in `have`; each piece read charged [`PIECE`]
/// units.
fn outside(
    gap: &IntervalSet,
    st: &Stride,
    have: &IntervalSet,
    work: &mut Work,
) -> Result<IntervalSet, Refusal> {
    let mut out = Vec::new();
    for (l, u) in gap
        .meet(&IntervalSet::range(fin(&st.lo), fin(&st.hi)))
        .pieces()
    {
        work.charge(PIECE)?;
        let (End::Fin(ln), End::Fin(un)) = (l, u) else {
            continue;
        };
        let (a, b) = (Int::from(ln), Int::from(un));
        if &b - &a >= &st.step - &Int::from(1) {
            continue;
        }
        let (ra, rb) = (a.mod_floor(&st.step), b.mod_floor(&st.step));
        let hit = if ra <= rb {
            !have
                .meet(&IntervalSet::range(fin(&ra), fin(&rb)))
                .is_empty()
        } else {
            let top = &st.step - &Int::from(1);
            !have
                .meet(&IntervalSet::range(fin(&ra), fin(&top)))
                .is_empty()
                || !have
                    .meet(&IntervalSet::range(fin(&Int::from(0)), fin(&rb)))
                    .is_empty()
        };
        if !hit {
            out.push((l.clone(), u.clone()));
        }
    }
    Ok(IntervalSet::from_pieces(out))
}

/// The cell of the point `m` for the symbol `s`: values of `s` in `within` (the hull of the
/// solver's answer), `m`'s among them, each with a point of `f`. Only `m`'s own value where
/// `s` is a product or a factor of one, since the solver may read a product more tightly than
/// as an atom of its own (`plain_rows`), so a point with `s` moved and the product kept may not
/// be one of the solver's. Each value of a progression is charged to `work`; with the cell,
/// each progression of two values or more whose step is not 1, as its step and its first and
/// last values (the residue questions of [`cover`]).
fn cell(
    f: &Formula,
    m: &Model,
    s: &Atom,
    factors: &HashSet<Atom>,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<(IntervalSet, Vec<Stride>, Vec<Strided>), Refusal> {
    let v = value(&Lin::atom(s.clone()), m);
    let own = IntervalSet::range(fin(&v), fin(&v));
    let mut strides = Vec::new();
    let mut holed = Vec::new();
    if matches!(s, Atom::Product(..)) || factors.contains(s) {
        return Ok((own, strides, holed));
    }
    let one = [(s.clone(), Int::from(1))];
    let mut c = shifted(&along(f, m, &one, &mut HashMap::new()), &v);
    debug_assert!(
        c.contains_end(&fin(&v)),
        "a point of the solver is not one of {f:?}"
    );
    c = c.join(&own);
    // The projection lies within `within`, and each value of the line has a point of `f`: so
    // when the line already holds `within`, it is the whole cell, and the implicant is not
    // projected. Complexity tradeoff: one subset test, at most linear in the pieces of the two
    // sets (`IntervalSet::is_subset`), against the projection of the implicant, whose
    // splinters can cost the whole limit (the repaired unit's `w`: 3.1M units, refused, for
    // `w == 0`).
    work.read((within.len() + c.len()) as u64 + 1)?;
    if within.is_subset(&c) {
        return Ok((c, strides, holed));
    }
    let mut rows = Vec::new();
    let mut truth = HashMap::new();
    if implicant(f, m, true, &mut rows, &mut HashSet::new(), &mut truth) {
        let rows = joined(&rows, s);
        let product = |k: &Con| (k.lin.terms.keys()).any(|a| matches!(a, Atom::Product(..)));
        let how = projection::method();
        let plain = !rows.iter().any(product) && matches!(how, Method::Pugh | Method::Liaproj);
        let quick = if plain {
            work.eliminate(&rows, &|a| a == s)?
        } else {
            None
        };
        if let Some(left) = quick {
            c = c.join(&bounded(&left, s));
        } else if plain {
            // The disjunct of the implicant's projection that holds `m` (`projection::liaproj`),
            // or with `Method::Pugh` the whole projection: its parts with no holes or with an
            // end are the cell's; those with holes and no end go to the cover, which joins
            // them with the other cells' (`projection::ranges`).
            let parts = if how == Method::Pugh {
                projection::pugh(&rows, s, &within.minus(&c), work)?
            } else {
                vec![projection::liaproj(&rows, s, m, work)?]
            };
            let (set, left) = projection::ranges(&parts, work)?;
            c = c.join(&set);
            let (closed, open): (Vec<Strided>, Vec<Strided>) = (parts.into_iter())
                .partition(|p| p.step == Int::from(1) || (p.lo.is_some() && p.hi.is_some()));
            let open = if left.is_empty() { Vec::new() } else { open };
            for p in closed.iter().filter(|p| p.step > Int::from(1)) {
                let (Some(lo), Some(hi)) = (&p.lo, &p.hi) else {
                    continue;
                };
                let first = lo + &(&p.res - lo).mod_floor(&p.step);
                let last = hi - &(hi - &p.res).mod_floor(&p.step);
                if first < last {
                    strides.push(Stride {
                        step: p.step.clone(),
                        lo: first,
                        hi: last,
                        absent: IntervalSet::empty(),
                    });
                }
            }
            holed = open;
        } else if !rows.iter().any(product) {
            if how == Method::Rays {
                let parts = projection::rays(&rows, s, constraints(f), work)?;
                let (plain, open): (Vec<Strided>, Vec<Strided>) =
                    parts.into_iter().partition(|p| p.step == Int::from(1));
                c = c.join(&projection::ranges(&plain, work)?.0);
                holed = open;
            }
            // The elimination that never grows the rows first, then the one that does every
            // exact step (`eliminated_whole`), the rows it makes charged as it makes them (so
            // that it stops at the limit, not after rows without bound) and the rows left
            // charged to the work.
            let left = match work.eliminate(&rows, &|a| a == s)? {
                Some(left) => Some(left),
                None => {
                    let whole = work.solver.eliminated_whole;
                    work.metered(|| whole(&rows, &|a| a == s))?
                }
            };
            if let Some(left) = left {
                work.read(left.len() as u64)?;
                c = c.join(&bounded(&left, s));
            } else {
                // A stride atom stops the exact elimination. With one, the runs of `s` at each
                // of its values (`runs`); else, or where that elimination is not exact either,
                // the run at the point's values of them all (`fixed`).
                let fix = stride_atoms(&rows, s);
                let one = match fix.as_slice() {
                    [q] => runs(&rows, s, q, within, work)?,
                    _ => None,
                };
                if let Some(r) = one {
                    c = c.join(&r);
                } else if !fix.is_empty()
                    && let Some(left) = work.eliminate(&fixed(&rows, &fix, m), &|a| a == s)?
                {
                    c = c.join(&bounded(&left, s));
                }
            }
            for d in directions(&rows, s, factors) {
                work.read(constraints(f))?;
                let steps = along(f, m, &d, &mut HashMap::new());
                let (p, stride) = progression(&steps, &v, &d[0].1, within, work)?;
                c = c.join(&p);
                strides.extend(stride);
            }
        }
    }
    Ok((c, strides, holed))
}

/// The directions that keep an equation of `rows` that holds `s`: for each other atom `q` of
/// such an equation `a·s + b·q + ... == 0`, `s` moved by `b/g` and `q` by `-a/g` (`g` the
/// greatest common divisor of `a` and `b`), `s` first; a stride (`x == 2·y`, `x == 1024·q + r`)
/// moves along them, where the line through `m` along `s` alone leaves its one value. Products
/// and factors of products are not moved (see [`cell`]).
fn directions(rows: &[Con], s: &Atom, factors: &HashSet<Atom>) -> Vec<Vec<(Atom, Int)>> {
    let mut out: Vec<Vec<(Atom, Int)>> = Vec::new();
    for k in rows.iter().filter(|k| k.rel == Rel::Eq) {
        let Some(a) = k.lin.terms.get(s) else {
            continue;
        };
        for (q, b) in &k.lin.terms {
            if q == s || matches!(q, Atom::Product(..)) || factors.contains(q) {
                continue;
            }
            let g = a.gcd(b);
            let mut ds = b.div_floor(&g);
            let mut dq = -&a.div_floor(&g);
            if ds.is_negative() {
                ds = -&ds;
                dq = -&dq;
            }
            let d = vec![(s.clone(), ds), (q.clone(), dq)];
            if !out.contains(&d) {
                out.push(d);
            }
        }
    }
    out
}

/// `steps` moved to start at `v`: each step `k` read as the value `v + k`.
fn shifted(steps: &IntervalSet, v: &Int) -> IntervalSet {
    let at = |e: &End| match e {
        End::Fin(n) => End::Fin(Num::from(&(&Int::from(n) + v))),
        e => e.clone(),
    };
    IntervalSet::from_pieces(steps.pieces().map(|(l, u)| (at(l), at(u))).collect())
}

/// The values `v + step·k` of `s` for the steps `k` of `steps`, those in `within`; each value
/// charged one unit of `work` where `step` is not ±1 (a value apart from the next), and none
/// where the values of `s` would have no end (an unbounded `within`: the cover asks for them
/// one piece at a time, and stops at the work limit).
fn progression(
    steps: &IntervalSet,
    v: &Int,
    step: &Int,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<(IntervalSet, Option<Stride>), Refusal> {
    let Some((lo, hi)) = within.bounds() else {
        return Ok((IntervalSet::empty(), None));
    };
    // The steps `k` with `lo <= v + step·k <= hi`, `step` above zero.
    let mut keep = Vec::new();
    if let End::Fin(lo) = lo {
        let lin = Lin {
            terms: [(Atom::Sym("k".into()), step.clone())]
                .into_iter()
                .collect(),
            constant: v - &Int::from(lo),
        };
        keep.push(Con { lin, rel: Rel::Ge });
    }
    if let End::Fin(hi) = hi {
        let lin = Lin {
            terms: [(Atom::Sym("k".into()), -step)].into_iter().collect(),
            constant: &Int::from(hi) - v,
        };
        keep.push(Con { lin, rel: Rel::Ge });
    }
    let steps = steps.meet(&bounded(&keep, &Atom::Sym("k".into())));
    if step.abs() == Int::from(1) {
        return Ok((shifted(&steps, v), None));
    }
    let mut pieces = Vec::new();
    for (l, u) in steps.pieces() {
        let (End::Fin(l), End::Fin(u)) = (l, u) else {
            return Ok((IntervalSet::empty(), None));
        };
        let (mut k, u) = (Int::from(l), Int::from(u));
        while k <= u {
            work.charge(1)?;
            let x = fin(&(v + &(step * &k)));
            pieces.push((x.clone(), x));
            k = &k + &Int::from(1);
        }
    }
    let stride = match (pieces.first(), pieces.last()) {
        (Some((End::Fin(a), _)), Some((End::Fin(b), _))) if pieces.len() >= 2 => Some(Stride {
            step: step.clone(),
            lo: Int::from(a),
            hi: Int::from(b),
            absent: IntervalSet::empty(),
        }),
        _ => None,
    };
    Ok((IntervalSet::from_pieces(pieces), stride))
}

/// The atoms other than `s` with a coefficient other than ±1 in an equation of `rows`: the
/// atoms of a stride (`q` of `x == 1024·q + r`), in order.
fn stride_atoms(rows: &[Con], s: &Atom) -> Vec<Atom> {
    let mut fix = std::collections::BTreeSet::new();
    for k in rows.iter().filter(|k| k.rel == Rel::Eq) {
        for (a, c) in &k.lin.terms {
            if a != s && c.abs() != Int::from(1) {
                fix.insert(a.clone());
            }
        }
    }
    fix.into_iter().collect()
}

/// `rows` with each atom of `fix` replaced by its value in `at`.
fn fixed(rows: &[Con], fix: &[Atom], at: &Model) -> Vec<Con> {
    (rows.iter())
        .map(|k| {
            let mut lin = k.lin.clone();
            for a in fix {
                if let Some(c) = lin.terms.remove(a) {
                    let v = at.get(a).cloned().unwrap_or_else(|| Int::from(0));
                    lin.constant = &lin.constant + &(&c * &v);
                }
            }
            Con { lin, rel: k.rel }
        })
        .collect()
}

/// The values of `s` in `within` at the points of the implicant `rows` whose one stride atom
/// is `q`: every other atom eliminated exactly, the rows left over `s` and `q` read at each
/// value of `q` that they and `within` allow, each a run of `s` (`1024·q` to `1024·q + 36` for
/// `x == 1024·q + r` with `r` in `0..=36`); `None` where the elimination is not exact or `q`
/// has no finite range. Each value of `q` is charged its rows to `work`. Every value given has
/// a point of the rows, so of `f`; the runs of all the values of `q` are the projection of the
/// rows, so a point in any of them gives all of them at once, where with `q` fixed at the
/// point's value (`fixed`) each run would take its own point and question.
fn runs(
    rows: &[Con],
    s: &Atom,
    q: &Atom,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<Option<IntervalSet>, Refusal> {
    let Some(mut two) = work.eliminate(rows, &|a| a == s || a == q)? else {
        return Ok(None);
    };
    if let Some((lo, hi)) = within.bounds() {
        let one = |k: i64, c: Int| Lin {
            terms: [(s.clone(), Int::from(k))].into_iter().collect(),
            constant: c,
        };
        if let End::Fin(lo) = lo {
            two.push(Con {
                lin: one(1, -&Int::from(lo)),
                rel: Rel::Ge,
            });
        }
        if let End::Fin(hi) = hi {
            two.push(Con {
                lin: one(-1, Int::from(hi)),
                rel: Rel::Ge,
            });
        }
    }
    let Some(over_q) = work.eliminate(&two, &|a| a == q)? else {
        return Ok(None);
    };
    let range = bounded(&over_q, q);
    let mut pieces = Vec::new();
    for (l, u) in range.pieces() {
        let (End::Fin(l), End::Fin(u)) = (l, u) else {
            return Ok(None);
        };
        let (mut v, u) = (Int::from(l), Int::from(u));
        while v <= u {
            work.read(two.len() as u64)?;
            let at: Model = [(q.clone(), v.clone())].into_iter().collect();
            pieces.extend(
                bounded(&fixed(&two, std::slice::from_ref(q), &at), s)
                    .pieces()
                    .cloned(),
            );
            v = &v + &Int::from(1);
        }
    }
    Ok(Some(IntervalSet::from_pieces(pieces)))
}

/// The steps `k` at which `f` holds at the point `m + k·d`, each atom of the direction `d` moved
/// by `k` times its step and every other atom at its value in `m`: each constraint becomes
/// `a·k + r` (with `a` the sum of its coefficients times their steps and `r` its value at `m`),
/// a bound, a point or nothing, and the connectives meet, join and complement them. A part
/// that two holders share is read once (`memo`, by [`Id`]). With `d` the symbol alone at step
/// 1, the steps are the line through `m` along that symbol, shifted by its value.
fn along(
    f: &Formula,
    m: &Model,
    d: &[(Atom, Int)],
    memo: &mut HashMap<Id, IntervalSet>,
) -> IntervalSet {
    let con = |c: &Con| {
        let mut a = Int::from(0);
        for (x, step) in d {
            if let Some(k) = c.lin.terms.get(x) {
                a = &a + &(k * step);
            }
        }
        let r = value(&c.lin, m);
        match a.is_zero() {
            true => {
                let holds = match c.rel {
                    Rel::Ge => !r.is_negative(),
                    Rel::Eq => r.is_zero(),
                };
                if holds {
                    IntervalSet::top()
                } else {
                    IntervalSet::empty()
                }
            }
            false => {
                let k = &d[0].0;
                let one = Con {
                    lin: Lin {
                        terms: [(k.clone(), a)].into_iter().collect(),
                        constant: r,
                    },
                    rel: c.rel,
                };
                bounded(std::slice::from_ref(&one), k)
            }
        }
    };
    let join = |f: &Formula, parts: Vec<IntervalSet>| match f {
        Formula::Not(_) => IntervalSet::top().minus(&parts[0]),
        Formula::And(_) => parts.iter().fold(IntervalSet::top(), |acc, p| acc.meet(p)),
        _ => parts
            .iter()
            .fold(IntervalSet::empty(), |acc, p| acc.join(p)),
    };
    fold(f, Id::of, memo, con, join)
}

/// A step of [`fold`]: a part to read, or a compound part whose parts are read.
enum Step<'a> {
    Read(&'a Formula),
    Join(&'a Formula),
}

/// The value of `f` given by `con` at each constraint and by `join` at each compound part, of
/// the values of its parts in order; a part with a key (`key`) is read once (`memo`). The
/// parts wait on an explicit stack, not on the thread's: a nest can be deeper than a thread's
/// stack allows (`l01_38_presburger::bench::nest_empty`, 512 levels in 256 KiB, and
/// `bench::ids`, whose recursive walks here overflowed). Every part is read, where the
/// recursive walks stopped a conjunction at its first false part: at most the parts the
/// caller's charge of `f`'s size counts.
fn fold<T: Clone>(
    f: &Formula,
    key: impl Fn(&Formula) -> Option<Id>,
    memo: &mut HashMap<Id, T>,
    mut con: impl FnMut(&Con) -> T,
    mut join: impl FnMut(&Formula, Vec<T>) -> T,
) -> T {
    let mut stack = vec![Step::Read(f)];
    let mut values: Vec<T> = Vec::new();
    while let Some(step) = stack.pop() {
        match step {
            Step::Read(g) => {
                if let Some(v) = key(g).and_then(|k| memo.get(&k)) {
                    values.push(v.clone());
                    continue;
                }
                match g {
                    Formula::Con(c) => values.push(con(c)),
                    Formula::Not(h) => stack.extend([Step::Join(g), Step::Read(h)]),
                    Formula::And(gs) | Formula::Or(gs) => {
                        stack.push(Step::Join(g));
                        stack.extend(gs.iter().rev().map(Step::Read));
                    }
                }
            }
            Step::Join(g) => {
                let n = match g {
                    Formula::And(gs) | Formula::Or(gs) => gs.len(),
                    _ => 1,
                };
                // A part pushed twice is read once: the first, read to its end before the
                // second is popped (the stack is last in, first out), leaves its value in
                // `memo` when it has a key, and a part with none has one holder.
                let parts = values.split_off(values.len() - n);
                let v = join(g, parts);
                if let Some(k) = key(g) {
                    memo.insert(k, v.clone());
                }
                values.push(v);
            }
        }
    }
    values.pop().expect("the value of `f`")
}

/// Whether `f` is `want` at `m`, read as [`value`] reads atoms; and where it is, the
/// constraints of an implicant pushed to `rows`: constraints that hold at `m` and whose
/// conjunction makes `f` `want` (a constraint that fails at `m` is pushed negated, an equation
/// by the side `m` is on). Of a disjunction that holds (or a conjunction that fails), the first
/// part that does is taken. A shared part already taken is not walked again (`seen`, by
/// [`Id`] and `want`), its constraints being pushed already.
fn implicant(
    f: &Formula,
    m: &Model,
    want: bool,
    rows: &mut Vec<Con>,
    seen: &mut HashSet<(Id, bool)>,
    truth: &mut HashMap<Id, bool>,
) -> bool {
    if holds_as(f, m, truth) != want {
        return false;
    }
    // Each part on the stack is `want` at `m`: `f` is; the part of a negation is the other;
    // every part of a conjunction that holds or a disjunction that fails is the same as it;
    // and the one part taken of the others is chosen so. The stack, not recursion, holds the
    // parts waiting (see [`fold`]); they are popped in the order the recursive walk took
    // them, first part first, so the rows come in the same order.
    let mut stack: Vec<(&Formula, bool)> = vec![(f, want)];
    while let Some((g, want)) = stack.pop() {
        if let Some(k) = Id::of(g)
            && !seen.insert((k, want))
        {
            continue;
        }
        match g {
            Formula::Con(c) => rows.push(if want {
                c.clone()
            } else {
                negated(c, &value(&c.lin, m))
            }),
            Formula::Not(h) => stack.push((h, !want)),
            Formula::And(gs) | Formula::Or(gs) => {
                // A conjunction that holds, or a disjunction that fails, needs every part; the
                // others need one.
                if matches!(g, Formula::And(_)) == want {
                    stack.extend(gs.iter().rev().map(|h| (h, want)));
                } else if let Some(h) = gs.iter().find(|h| holds_as(h, m, truth) == want) {
                    stack.push((h, want));
                }
            }
        }
    }
    true
}

/// Whether `f` holds at `m`, read as [`value`] reads atoms; each compound part is read once
/// (`memo`, by [`Id`]).
///
/// Complexity tradeoff: [`implicant`] asks this of each part of every disjunction it passes
/// on its way down, and a part holds the nest below it. Memoized for shared parts alone, as
/// `along` is, each level of a nest d deep read the whole nest below it again, O(d^2) for
/// one cell, against the `size` units [`cover`] charges for it: `heavy` of `l01_39_scope_
/// relations::deep_condition` took 0.58 and 21.9 s at d = 180 and 1440, 37 times, for 6.8
/// and 24.2 M units. With every compound part memoized, one cell reads each part once, O(the
/// size of `f`) with one hash insert for each compound part, the cost the meter charges. The
/// memo changes no answer: each memo serves one model `m` (the caller makes one per cell), and
/// an [`Id`] names one part and is never reused, so an entry is this function's own value at
/// that part and `m`, read again.
fn holds_as(f: &Formula, m: &Model, memo: &mut HashMap<Id, bool>) -> bool {
    let key = |g: &Formula| (!matches!(g, Formula::Con(_))).then(|| Id::any(g));
    let join = |g: &Formula, parts: Vec<bool>| match g {
        Formula::Not(_) => !parts[0],
        Formula::And(_) => parts.iter().all(|&b| b),
        _ => parts.iter().any(|&b| b),
    };
    fold(f, key, memo, |c| holds_at(c, &value(&c.lin, m)), join)
}

/// The negation of `c`, which fails at a point where its form is `v`: `-t - 1 >= 0` for
/// `t >= 0`, and for `t == 0`, `t - 1 >= 0` or `-t - 1 >= 0` by the side of `v`.
fn negated(c: &Con, v: &Int) -> Con {
    let mut lin = c.lin.clone();
    let below = match c.rel {
        Rel::Ge => true,
        Rel::Eq => v.is_negative(),
    };
    if below {
        for k in lin.terms.values_mut() {
            *k = -&*k;
        }
        lin.constant = -&lin.constant;
    }
    lin.constant = &lin.constant - &Int::ONE;
    Con { lin, rel: Rel::Ge }
}

/// The number of constraints of `f`, each shared part counted once.
fn constraints(f: &Formula) -> u64 {
    let mut n = 0;
    each_constraint(f, |_| n += 1);
    n.max(1)
}

/// The atoms that are factors of a product atom of `f`.
fn factors(f: &Formula) -> HashSet<Atom> {
    let mut out = HashSet::new();
    each_constraint(f, |c| {
        for a in c.lin.terms.keys() {
            if let Atom::Product(p, q) = a {
                for x in [p, q] {
                    out.insert(match x {
                        Factor::Sym(n) => Atom::Sym(n.clone()),
                        Factor::Aux(i) => Atom::Aux(*i),
                    });
                }
            }
        }
    });
    out
}

/// The answers of [`exact_each`] read off a smaller formula, where two or more atoms of `f`
/// have the same coefficient in every constraint (the same column), or `None` where none do,
/// or where the smaller formula's answers are not all exact.
///
/// Proof. Let C be such a class, with coefficient `c_r` in row r. Each row reads the atoms of
/// C through `c_r·Σ_C z` alone, so f(x, z_C) = g(x, Σ_C z), with g the formula with every
/// member but the least, m, dropped from every row and m standing for the sum. (a) An atom y
/// outside every class: ∃(rest, z_C) f ⟺ ∃(rest, s) g(·, s), as each s is Σ_C z for some z_C
/// (all on m, the others 0), so y has the same projection in f and in g. (b) A member a of
/// C with |C| ≥ 2: given any point (x, s) of g and any value v, set z_a = v, a second member
/// to s − v and the others to 0; this is a point of f. So a takes every integer where g has a
/// point and none where it has none. Each answer below is the exact projection, as are
/// those of [`exact_each`] with no cause, and the exact projection has one form ([`Classed`]):
/// where both paths answer, they answer the same. A solver's set for y is a set over the
/// projection of y in f, so in g too, and is passed on; m's is every integer.
// Complexity: O(t) for t terms of the distinct constraints, to find the columns and rebuild;
// the covers then run over g, whose rows have one term per class. Before: a k-term sum row
// made each of its k symbols' covers O(k), so O(k^2) for the call (`families::bench::wide`).
fn by_columns(
    f: &Formula,
    syms: &[Atom],
    each: &[Result<IntervalSet, Refusal>],
    solver: Solver,
) -> Option<EachClassed> {
    let mut rows: Vec<&Con> = Vec::new();
    each_constraint(f, |c| rows.push(c));
    let mut columns: HashMap<&Atom, Vec<(usize, &Int)>> = HashMap::new();
    for (r, c) in rows.iter().enumerate() {
        for (a, k) in &c.lin.terms {
            if matches!(a, Atom::Product(..)) {
                return None;
            }
            columns.entry(a).or_default().push((r, k));
        }
    }
    let mut classes: HashMap<&[(usize, &Int)], Vec<&Atom>> = HashMap::new();
    for (a, col) in &columns {
        classes.entry(col.as_slice()).or_default().push(*a);
    }
    // Each member of a class of two or more, to the least member, which stands for the sum.
    let mut least: HashMap<Atom, Atom> = HashMap::new();
    for (_, mut ms) in classes {
        if ms.len() < 2 {
            continue;
        }
        ms.sort();
        for m in &ms {
            least.insert((*m).clone(), ms[0].clone());
        }
    }
    if least.is_empty() {
        return None;
    }
    let g = f.map_cons(&|c| {
        let mut c = c.clone();
        c.lin
            .terms
            .retain(|a, _| least.get(a).is_none_or(|m| m == a));
        Formula::Con(c)
    });
    let asked: Vec<Atom> = (syms.iter())
        .map(|s| least.get(s).unwrap_or(s).clone())
        .collect();
    let given: Vec<Result<IntervalSet, Refusal>> = (syms.iter().zip(each))
        .map(|(s, h)| match least.get(s) {
            Some(_) => Ok(IntervalSet::top()),
            None => h.clone(),
        })
        .collect();
    let got = exact_each(&g, &asked, (given, Vec::new()), solver);
    if !got.causes.is_empty() {
        return None;
    }
    let mut sets = Vec::with_capacity(syms.len());
    for ((s, h), r) in syms.iter().zip(each).zip(got.sets) {
        sets.push(match (h, r) {
            (Err(e), _) => Err(e.clone()),
            (Ok(_), Err(_)) => return None,
            (Ok(_), Ok(set)) if least.contains_key(s) => {
                Ok(Classed::plain(if set.ranges.is_empty() {
                    IntervalSet::empty()
                } else {
                    IntervalSet::top()
                }))
            }
            (Ok(_), Ok(set)) => Ok(set),
        });
    }
    Some(EachClassed {
        sets,
        causes: Vec::new(),
    })
}

/// The rows of `rows` joined to `s` through shared atoms. The others hold at the point the
/// implicant was read at and share no atom with these, so each point of these, with the
/// point's values for the other atoms, is a point of all: projecting onto `s` needs these
/// alone, and a stride elsewhere (a second remainder) does not stop their elimination.
// Complexity: union-find over the atoms, O(r·t·α) for r rows of t terms; the naive repeated
// pass adding each row that meets the atoms so far is O(r^2·t).
fn joined(rows: &[Con], s: &Atom) -> Vec<Con> {
    let mut index: HashMap<&Atom, usize> = HashMap::new();
    let mut parent = UnionFind::default();
    for k in rows {
        let mut first = None;
        for a in k.lin.terms.keys() {
            let n = parent.len();
            let i = *index.entry(a).or_insert(n);
            if i == n {
                parent.push();
            }
            match first {
                None => first = Some(i),
                Some(f) => {
                    parent.union(f, i);
                }
            }
        }
    }
    let Some(&at) = index.get(s) else {
        return Vec::new();
    };
    let top = parent.find(at);
    (rows.iter())
        .filter(|k| (k.lin.terms.keys().next()).is_some_and(|a| parent.find(index[a]) == top))
        .cloned()
        .collect()
}

/// The rows of the conjunction `rows` in groups that share no atom, each group in the order of
/// its first row and its rows in their order, so the same on every run; one group, all of
/// `rows`, where some row reads no atom (it holds or fails whatever the atoms are, and so
/// belongs with no group in particular). Each term read is charged.
// Complexity tradeoff: union-find over the atoms with path halving, O(t α) for t terms, as
// [`joined`], which keeps the one group of a given atom; this keeps every group, for
// [`read_once`], which projects each group onto its own atoms.
fn row_groups(rows: &[Con], work: &mut Work) -> Result<Vec<Vec<Con>>, Refusal> {
    work.read(rows.iter().map(|c| c.lin.terms.len() as u64).sum())?;
    if rows.iter().any(|c| c.lin.terms.is_empty()) {
        return Ok(vec![rows.to_vec()]);
    }
    let mut index: HashMap<&Atom, usize> = HashMap::new();
    let mut parent = UnionFind::default();
    for k in rows {
        let mut first = None;
        for a in k.lin.terms.keys() {
            let n = parent.len();
            let i = *index.entry(a).or_insert(n);
            if i == n {
                parent.push();
            }
            match first {
                None => first = Some(i),
                Some(f) => {
                    parent.union_least(f, i);
                }
            }
        }
    }
    let mut of: HashMap<usize, usize> = HashMap::new();
    let mut groups: Vec<Vec<Con>> = Vec::new();
    for k in rows {
        let a = k
            .lin
            .terms
            .keys()
            .next()
            .expect("every row reads an atom here");
        let r = parent.find(index[a]);
        let g = *of.entry(r).or_insert_with(|| {
            groups.push(Vec::new());
            groups.len() - 1
        });
        groups[g].push(k.clone());
    }
    Ok(groups)
}

// The tests are a file of their own: they name the solver (`presburger.rs`), which calls this
// module, and a test module kept here would make the two import each other
// (`s_01f_import_graph`, row PRES-cover-wire).
#[cfg(test)]
mod tests;
