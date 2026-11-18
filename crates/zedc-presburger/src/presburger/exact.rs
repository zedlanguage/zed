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
// Complexity tradeoff: naive version, one decision of `f` with the symbol at each value of
// `h` (as the per-value check of the step 1 measurement did): exact, |h| questions for each
// symbol, and nothing for an unbounded `h`. Pugh's exact projection (the Omega test's
// splinters and strides, "The Omega test", 1991, section 3) gives a union of stride sets for
// one conjunction, but a disjunctive formula first needs its disjunctive normal form, which
// is exponential in the number of disjunctions, and the solver already avoids it. Used: the
// model-guided cover, one question for each cell and one more, each question one run of the
// solver on `f` and the gap, and O(|f|) for each cell: where the solver's hull was exact and
// the first point's cell covers it, as most do, one question in all for every symbol of the
// call together (the points found are kept for the other symbols). Measured on the families
// of step 1 (COMPLEXITY.md row PRES-pugh-work-budget).
// Trigger: a holed disjunct (a stride, `x + 2 * y == 0`), or values each disjunction allows
// through a different disjunct. Tests: `exact::tests`; zedc_preimage
// `or_if_projections_keep_the_gaps_the_if_reading_shows` needs the cover on the checker's
// path and is kept out of the tree until row PRES-cover-wire puts it there
// (/home/luke/Work/wt/failing-tests/FAIL-or-if-projection-not-exact.rs).

use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::lattice::Congruence;

use super::absorbing;
use super::formula::{Ends, Id};
pub use super::meter::{
    DIRECT_OFF, EXACT_LIMIT, EXACT_LIMIT_SET, EXACT_OFF, EXACT_QUESTIONS, EXACT_WORK, FAST_WORK,
    GUARDED_OFF, QUESTION_WORK, SOLVER_UNIT,
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
    if EXACT_OFF.get() {
        return EachClassed::plain(found);
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
        return EachClassed::plain((out, Vec::new()));
    }
    if let Some(out) = by_columns(f, syms, &each, solver) {
        return out;
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
    // points a cover keeps are those of the model enumeration (Monniaux, CAV 2010, sec. 3);
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
    // each of the P pieces of `h`, with no question; the loop of the cover asks at least one
    // question a value where each value is its own cell (guards-beyond: one for each value of
    // `i`, each a run of the solver on the whole formula, O(v·r·t) or more for v values), and on
    // the chain of absolute values the reading alone spent 2,971,100 of 3,100,000 units at 1,100
    // levels, all of them at 8,800, against the certificate's 70,512 and 563,312. Where it
    // declines, its work, at most the part's allowance, is taken from the reading and the
    // fast paths, never from the loops (PRES-cover-bench-guards-beyond, -chains-abs).
    let mut certified: HashMap<&Atom, IntervalSet> = HashMap::new();
    let mut once: Vec<(Option<ReadOnce>, u64)> = Vec::with_capacity(parts.len());
    for ((p, &k), mine) in parts.iter().zip(&asked).zip(&members) {
        if !p.factors.is_empty() || k == 0 {
            once.push((None, 0));
            continue;
        }
        let allowed = limit.saturating_mul(k);
        let mut left = allowed;
        let mut open = k;
        if !GUARDED_OFF.get() {
            for &(s, h) in mine {
                if let Some(set) = tried(&mut left, solver, |w| guarded::forward(&p.f, s, h, w)) {
                    certified.insert(s, set);
                    open -= 1;
                }
            }
        }
        let got = if open > 0 {
            tried(&mut left, solver, |w| read_once(&p.f, w))
        } else {
            None
        };
        once.push((got, allowed - left));
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
    let mut small_points: Vec<Vec<Model>> = vec![Vec::new(); parts.len()];
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
                // `h` is not empty here (above), and each of its values has a point of the part.
                if let Some(set) = certified.remove(s) {
                    shown[i] = true;
                    return Ok(Classed::plain(set));
                }
                if let (Some((has, sets)), _) = &once[i] {
                    shown[i] |= *has;
                    return Ok(Classed::plain(match (sets.get(s), has) {
                        (Some(set), _) => set.clone(),
                        (None, true) => IntervalSet::range(End::NegInf, End::PosInf),
                        (None, false) => IntervalSet::empty(),
                    }));
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
                    fast,
                    &mut work,
                )?;
                wider |= kept;
                Ok(set)
            })();
            (s, answer)
        })
        .collect();
    let out: Vec<Result<Classed, Refusal>> = syms.iter().map(|s| answers[s].clone()).collect();
    if !many {
        return EachClassed {
            sets: out,
            causes: if wider {
                vec![Refusal::Repeats]
            } else {
                Vec::new()
            },
        };
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
    EachClassed {
        sets: out,
        causes: if wider {
            vec![Refusal::Repeats]
        } else {
            Vec::new()
        },
    }
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
    let mut parent: Vec<usize> = (0..conjuncts.len()).collect();
    fn root(p: &mut [usize], mut i: usize) -> usize {
        while p[i] != i {
            p[i] = p[p[i]];
            i = p[i];
        }
        i
    }
    let mut first: HashMap<Atom, usize> = HashMap::new();
    let mut reads: Vec<HashSet<Atom>> = Vec::with_capacity(conjuncts.len());
    for (i, g) in conjuncts.iter().enumerate() {
        let atoms = atoms_of(g);
        for a in &atoms {
            let j = *first.entry(a.clone()).or_insert(i);
            let (ri, rj) = (root(&mut parent, i), root(&mut parent, j));
            parent[ri.max(rj)] = ri.min(rj);
        }
        reads.push(atoms);
    }
    // The groups in the order of their first conjunct, so the same on every run.
    let mut order: Vec<usize> = Vec::new();
    let mut of: HashMap<usize, usize> = HashMap::new();
    let mut groups: Vec<(Vec<Formula>, HashSet<Atom>)> = Vec::new();
    for (i, g) in conjuncts.iter().enumerate() {
        let r = root(&mut parent, i);
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
/// solver then, so no answer rests on a branch left untried. `f` has no product atom.
// Complexity tradeoff: a question of the solver on a part of 7 constraints cost 40,800 units
// and 0.65 ms (`bench::omega::independent_stages_scale`, load 60), so one for each of n parts
// cost 1.2 s at n = 1,800. Naive alternative: every branch of the disjunctive normal form,
// exponential in the disjunctions. Used: the first branches, stopped at `room` rows read,
// which the caller sets to the rows the question it replaces is charged to read, so this never
// costs more than that charge, plus the elimination and solve of the branches read (charged by
// the solver's meter).
fn quick_point(f: &Formula, room: u64, work: &mut Work) -> Result<Option<Model>, Refusal> {
    // A list shared by the branches that hold it, so a branch is copied in O(1).
    struct Node<T>(T, List<T>);
    type List<T> = Option<Rc<Node<T>>>;
    // A branch: the rows taken, and the parts still to take, each with its sign.
    type Branch<'a> = (List<Con>, List<(&'a Formula, bool)>);
    fn push<T>(l: &List<T>, x: T) -> List<T> {
        Some(Rc::new(Node(x, l.clone())))
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
    let done = |branches: Vec<Branch>| {
        for (r, t) in branches {
            unwind(r);
            unwind(t);
        }
    };
    let mut branches: Vec<Branch> = vec![(None, push(&None, (f, true)))];
    let mut read = 0u64;
    let mut charged = 0u64;
    'branch: while let Some((mut rows, mut todo)) = branches.pop() {
        while let Some(top) = todo.clone() {
            let (g, pos) = top.0;
            todo = top.1.clone();
            match g {
                Formula::Con(c) => match (pos, c.rel) {
                    (true, _) => rows = push(&rows, c.clone()),
                    (false, Rel::Ge) => rows = push(&rows, negated(c, &Int::from(-1))),
                    (false, Rel::Eq) => {
                        // `t != 0`: `t >= 1`, else `t <= -1`.
                        read += 1;
                        branches.push((push(&rows, negated(c, &Int::from(-1))), todo.clone()));
                        rows = push(&rows, negated(c, &Int::from(1)));
                    }
                },
                Formula::Not(h) => todo = push(&todo, (&**h, !pos)),
                Formula::And(gs) | Formula::Or(gs) => {
                    if matches!(g, Formula::And(_)) == pos {
                        for h in gs.iter().rev() {
                            todo = push(&todo, (h, pos));
                        }
                    } else if let Some((first, rest)) = gs.split_first() {
                        // The later disjuncts wait, the next one first.
                        for h in rest.iter().rev() {
                            read += 1;
                            branches.push((rows.clone(), push(&todo, (h, pos))));
                        }
                        todo = push(&todo, (first, pos));
                    } else {
                        // An empty disjunction (or a negated empty conjunction) is false.
                        continue 'branch;
                    }
                }
            }
            if read > room {
                work.read(read - charged)?;
                unwind(rows);
                unwind(todo);
                done(branches);
                return Ok(None);
            }
        }
        let mut leaf = Vec::new();
        let mut at = &rows;
        while let Some(node) = at {
            leaf.push(node.0.clone());
            at = &node.1;
        }
        unwind(rows);
        read += leaf.len() as u64;
        work.read(read - charged)?;
        charged = read;
        if read > room {
            done(branches);
            return Ok(None);
        }
        let point_of = work.solver.point_of;
        if let Some(m) = work.metered(|| point_of(&leaf, false))?
            && holds_as(f, &m, &mut HashMap::new())
        {
            done(branches);
            return Ok(Some(m));
        }
    }
    work.read(read - charged)?;
    Ok(None)
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
    let mut fast = fast;
    if factors.is_empty()
        && !DIRECT_OFF.get()
        && let Some(set) = tried(&mut fast, work.solver, |w| direct(f, s, &h.hull(), w))
    {
        return Ok((set, false));
    }
    let (set, kept) = cells_cover(f, s, h, size, factors, points, work)?;
    Ok((Classed::plain(set), kept))
}

/// [`cover`] by cells and questions, once [`direct`] has not answered.
fn cells_cover(
    f: &Formula,
    s: &Atom,
    h: &IntervalSet,
    size: u64,
    factors: &HashSet<Atom>,
    points: &mut Vec<Model>,
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
    // `f` has `s` in `h`, so its cell is read as a question's point would be.
    if points.is_empty()
        && factors.is_empty()
        && let Some(m) = quick_point(f, 2 * (size + 2), work)?
    {
        points.push(m);
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
        if let Some(st) = strides.pop() {
            let have = residues(&found, &st, work)?;
            let all = IntervalSet::range(fin(&Int::from(0)), fin(&(&st.step - &Int::from(1))));
            let other = all.minus(&have);
            if other.is_empty() {
                continue;
            }
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
                super::member(&j, &other),
            ]);
            // A refusal of this question for another cause leaves the gap to the questions by
            // piece; past the work limit, the cover stops here at once.
            match work.ask(&q) {
                Err(_) if work.used > work.limit => return Err(Refusal::Questions),
                Err(_) => {}
                Ok(None) => gap = gap.minus(&outside(&gap, &st, &have, work)?),
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
        work.question(size + 2)?;
        EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
        let piece = IntervalSet::range(piece.0, piece.1);
        let q = Formula::and(vec![f.clone(), super::member(s, &piece)]);
        match work.ask(&q)? {
            None => gap = gap.minus(&piece),
            Some(m) => points.push(m),
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
/// it (PRES-cover-refusals-moduli).
#[derive(Clone)]
enum Part {
    Rows(Vec<Con>),
    Set(Classed, HashSet<Atom>),
    Alts(Vec<Vec<Con>>),
}

/// `run`, a fast path, given what is left of `fast`, the fast paths' own allowance (a quarter
/// of the limit, set by the caller once for its `Work`): its answer, or `None` where it fails
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
// sec. 2.2 and 3, with model-based cells after Bjørner and Janota, "Playing with Quantified
// Satisfaction", LPAR-20, 2015, sec. 2.2; `direct` is Pugh's structural exact shadow, "A
// practical algorithm for exact array dependence analysis", CACM 35(8), 1992, p. 106.
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
///   where the group has a point (Pugh's exact shadow, "The Omega test", 1992); a group of one
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
// `tried`; a group with two disjunctions is not distributed (`None`, the cover is asked).
fn direct(
    f: &Formula,
    s: &Atom,
    within: &IntervalSet,
    work: &mut Work,
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
    let mut memo: HashMap<(Id, bool), Part> = HashMap::new();
    let mut stack = vec![Go::Read(f, true)];
    let mut values: Vec<Part> = Vec::new();
    while let Some(step) = stack.pop() {
        match step {
            Go::Read(g, pos) => {
                if let Some(v) = Id::of(g).and_then(|k| memo.get(&(k, pos))) {
                    match v {
                        Part::Rows(rows) => work.read(rows.len() as u64)?,
                        Part::Alts(blocks) => {
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
                            // `t != 0` is `t <= -1 or t >= 1`, two blocks.
                            (false, Rel::Eq) => Part::Alts(vec![
                                vec![negated(c, &Int::from(-1))],
                                vec![negated(c, &Int::from(1))],
                            ]),
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
                let v = if matches!(g, Formula::And(_)) == pos {
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
                    if let Part::Alts(_) = v {
                        let Some((set, atoms)) = as_set(v, s, within, false, work)? else {
                            return Ok(None);
                        };
                        v = Part::Set(set, atoms);
                    }
                    memo.insert((k, pos), v.clone());
                }
                values.push(v);
            }
        }
    }
    Ok(as_set(
        values.pop().expect("the part of `f`"),
        s,
        within,
        false,
        work,
    )?
    .map(|(set, _)| set))
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
/// (Opus and Sol, round 1 of XR-cover-hybrid; the two passes of Darwiche and Marquis, "A
/// knowledge compilation map", JAIR 17, 2002, sec. 4, for decomposable forms).
///
/// An atom may also be read by several blocks, provided no conjunction has two parts that read
/// it (the tree is decomposable, Darwiche and Marquis sec. 2). The values of `s` are then every
/// value where some disjunction that reads `s`, with `ctx` there, has a part with a point that
/// does not read `s`, else the union of the projections onto `s` of the blocks `B` that read it
/// with `ctx(B)`. Proof: by the rule above, node by node, a conjunction's values of `s` are those
/// of its one part that reads `s` where its other parts have points; a disjunction's are the
/// union of those of its parts, every value for a part with a point that does not read `s`.
/// Unrolled from the root, that is the rule stated. Such a disjunction is found among the nodes
/// where the paths to the blocks of `s` part (their lowest common ancestors), checked one by one,
/// and on the paths between them, where one part alone reads `s` and `esc` is counted as before
/// (Sol, round 2 of XR-cover-hybrid).
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
        // A conjunction's one block of rows, if any, and its other parts; the block joins
        // the parts once the nodes are built.
        And(Option<usize>, Vec<usize>),
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
                // in `nodes`, unreached.
                let mut rows: Vec<Con> = Vec::new();
                let mut kids: Vec<usize> = Vec::new();
                let take_rows = |rows: &mut Vec<Con>, mut more: Vec<Con>| {
                    if more.len() > rows.len() {
                        std::mem::swap(rows, &mut more);
                    }
                    rows.append(&mut more);
                };
                for i in parts {
                    match std::mem::replace(&mut nodes[i], Node::Or(Vec::new())) {
                        Node::Block(r) => take_rows(&mut rows, r),
                        Node::And(block, mut more) => {
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
                if kids.is_empty() {
                    nodes.push(Node::Block(rows));
                } else {
                    let block = (!rows.is_empty()).then(|| {
                        nodes.push(Node::Block(rows));
                        nodes.len() - 1
                    });
                    nodes.push(Node::And(block, kids));
                }
                values.push(nodes.len() - 1);
            }
        }
    }
    let root = values.pop().expect("the node of `f`");
    for n in &mut nodes {
        if let Node::And(block, kids) = n
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
        if let Node::And(_, cs) | Node::Or(cs) = &nodes[i] {
            for &c in cs {
                reached[c] = true;
            }
        }
    }
    // The blocks that read each atom, each once.
    let mut blocks_of: HashMap<&Atom, Vec<usize>> = HashMap::new();
    for (i, n) in nodes.iter().enumerate() {
        if let (true, Node::Block(rows)) = (reached[i], n) {
            for a in rows.iter().flat_map(|c| c.lin.terms.keys()) {
                let bs = blocks_of.entry(a).or_default();
                if bs.last() != Some(&i) {
                    bs.push(i);
                }
            }
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
                let mut all = true;
                for group in row_groups(rows, work)? {
                    let sets = if let Some(sets) = forest(&group, work)? {
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
            Node::And(_, cs) => cs.iter().all(|&c| sat[c]),
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
    ctx[root] = true;
    for i in (0..nodes.len()).rev() {
        if !reached[i] {
            continue;
        }
        if let Node::And(_, cs) | Node::Or(cs) = &nodes[i] {
            work.read(cs.len() as u64)?;
            live[i] = cs.iter().filter(|&&c| sat[c]).count();
            for &c in cs {
                let others = live[i] - usize::from(sat[c]);
                parent[c] = i;
                depth[c] = depth[i] + 1;
                if matches!(nodes[i], Node::And(..)) {
                    ctx[c] = ctx[i] && others == cs.len() - 1;
                    escs[c] = escs[i];
                } else {
                    ctx[c] = ctx[i];
                    escs[c] = escs[i] + usize::from(ctx[i] && others > 0);
                }
            }
        }
    }
    // Where some atom is read by two blocks: the order of a walk of the tree from the root, and
    // the ancestors of each node 2^j steps up.
    let mut order = vec![0usize; nodes.len()];
    let mut lift: Vec<Vec<usize>> = Vec::new();
    if blocks_of.values().any(|bs| bs.len() > 1) {
        let mut stack = vec![root];
        let mut at = 0;
        while let Some(i) = stack.pop() {
            order[i] = at;
            at += 1;
            if let Node::And(_, cs) | Node::Or(cs) = &nodes[i] {
                stack.extend(cs.iter().copied());
            }
        }
        lift.push(parent.clone());
        while 1usize << lift.len() <= at {
            let up = lift.last().expect("one level");
            let next = (0..nodes.len()).map(|i| up[up[i]]).collect();
            lift.push(next);
        }
    }
    let up_to = |mut i: usize, d: usize| {
        let mut steps = depth[i].saturating_sub(d);
        let mut j = 0;
        while steps > 0 {
            if steps & 1 == 1 {
                i = lift[j][i];
            }
            steps >>= 1;
            j += 1;
        }
        i
    };
    let lca = |a: usize, b: usize| {
        let (mut a, mut b) = (up_to(a, depth[b]), up_to(b, depth[a]));
        if a == b {
            return a;
        }
        for up in lift.iter().rev() {
            if up[a] != up[b] {
                a = up[a];
                b = up[b];
            }
        }
        parent[a]
    };
    let every = IntervalSet::range(End::NegInf, End::PosInf);
    let mut out = HashMap::new();
    for (a, mut bs) in blocks_of {
        let escaped = if bs.len() == 1 {
            escs[bs[0]] > 0
        } else {
            work.read(bs.len() as u64)?;
            // The blocks with the lowest common ancestors of neighbors in walk order: a set
            // closed under lowest common ancestors, in which each node's lowest ancestor is the
            // lowest common ancestor of it and the node before it in walk order.
            bs.sort_by_key(|&b| order[b]);
            let mut vs = bs.clone();
            vs.extend(bs.windows(2).map(|w| lca(w[0], w[1])));
            vs.sort_by_key(|&v| order[v]);
            vs.dedup();
            let mut escaped = escs[vs[0]] > 0;
            let mut parts: HashMap<usize, Vec<usize>> = HashMap::new();
            for w in vs.windows(2) {
                let x = lca(w[0], w[1]);
                let c = up_to(w[1], depth[x] + 1);
                escaped |= escs[w[1]] > escs[c];
                parts.entry(x).or_default().push(c);
            }
            for (x, mut cs) in parts {
                if matches!(nodes[x], Node::And(..)) {
                    return Ok(None);
                }
                cs.sort_unstable();
                cs.dedup();
                let reading = cs.iter().filter(|&&c| sat[c]).count();
                escaped |= ctx[x] && live[x] > reading;
            }
            escaped
        };
        let set = if escaped {
            every.clone()
        } else {
            let pieces = (bs.iter().filter(|&&b| ctx[b]))
                .flat_map(|&b| own[b][a].pieces().cloned())
                .collect();
            IntervalSet::from_pieces(pieces)
        };
        out.insert(a.clone(), set);
    }
    Ok(Some((sat[root], out)))
}

/// The intersection of two intervals, each end `None` where it is unbounded; empty where the
/// least is above the greatest.
fn ends_meet(a: &Ends, b: &Ends) -> Ends {
    let lo = match (&a.0, &b.0) {
        (Some(x), Some(y)) => Some(x.max(y).clone()),
        (x, y) => x.clone().or_else(|| y.clone()),
    };
    let hi = match (&a.1, &b.1) {
        (Some(x), Some(y)) => Some(x.min(y).clone()),
        (x, y) => x.clone().or_else(|| y.clone()),
    };
    (lo, hi)
}

fn ends_empty(a: &Ends) -> bool {
    matches!(a, (Some(lo), Some(hi)) if lo > hi)
}

/// The values of `y` for which some `x` in `d` has `a·x + b·y + k >= 0`, for `a` and `b` not
/// zero: every `y` where `a·x` is unbounded above on `d`, else `b·y >= -(k + max a·x)`.
fn ends_sent(d: &Ends, a: &Int, b: &Int, k: &Int) -> Ends {
    if ends_empty(d) {
        return (Some(Int::ONE), Some(Int::ZERO));
    }
    let end = if a.is_positive() { &d.1 } else { &d.0 };
    let Some(x) = end else {
        return (None, None);
    };
    let t = -&(k + &(a * x));
    if b.is_positive() {
        (Some(-&(-&t).div_floor(b)), None)
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
/// backtrack-free search", JACM 29, 1982, for trees; each message an interval, by the rounding
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
    // The trees joined so far, by union-find with halving.
    let mut root: Vec<usize> = (0..n).collect();
    let find = |root: &mut Vec<usize>, mut i: usize| {
        while root[i] != i {
            root[i] = root[root[i]];
            i = root[i];
        }
        i
    };
    for c in rows {
        if let Some((a, lo, hi)) = super::formula::one_bound(c) {
            let i = index[a];
            own[i] = ends_meet(&own[i], &(lo, hi));
            continue;
        }
        let mut ts = c.lin.terms.iter();
        let (Some((x, a)), Some((y, b))) = (ts.next(), ts.next()) else {
            return Ok(None);
        };
        let (u, v) = (index[x], index[y]);
        let (ru, rv) = (find(&mut root, u), find(&mut root, v));
        if ru == rv {
            return Ok(None);
        }
        root[ru] = rv;
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
            below[p] = ends_meet(&below[p], &to_parent[i]);
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
        let base = ends_meet(&own[i], &from_parent[i]);
        let mut suffix: Vec<Ends> = vec![(None, None); kids.len() + 1];
        for t in (0..kids.len()).rev() {
            suffix[t] = ends_meet(&suffix[t + 1], &to_parent[kids[t].1]);
        }
        let mut prefix = base;
        for (t, &(e, j)) in kids.iter().enumerate() {
            from_parent[j] = sent(e, i, &ends_meet(&prefix, &suffix[t + 1]));
            prefix = ends_meet(&prefix, &to_parent[j]);
        }
    }
    let ends: Vec<Ends> = (0..n)
        .map(|i| ends_meet(&below[i], &from_parent[i]))
        .collect();
    let none = ends.iter().any(ends_empty);
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
// shadow, "The Omega test", 1992); the cover did neither. Used: the same two steps, once for
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
/// sets) of `rows` with the ends of `within` added as rows, its ranges kept and, with `list`,
/// its strides as ranges met with a class. `None` where
/// neither gives a set of ranges (a stride, without
/// `list` or with no end).
///
/// Why the ends may be added: every value of `s` with a point of the formula lies in the
/// solver's set (`exact_each`), so in its hull, and the projection of `rows ∧ within` is that of
/// `rows` met with `within`. Where `rows` is a disjunct of a part of a split formula whose other
/// part has no point, the answer is made empty by `exact_each` anyway.
fn block_set(
    rows: &[Con],
    s: &Atom,
    within: &IntervalSet,
    list: bool,
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
        // A stride leaves `direct` only with `list` (the projection inside [`cut_at_shared`],
        // read only for emptiness). Elsewhere it is declined: the preimage stage's check that
        // the boxes are exact (`member` of each box, one disjunct a value, then `decide`) is
        // slower than linear in the values: `l01_25`
        // `bench::s22::remainder_chains_in_the_linear_stage_scale` (y even over
        // [-100000, 100000]) ran past 60 s, 4.4 s with the stride left to the cover (profile
        // 2026-11-18: 37% in `probe_kept_status` under `decide` from `preimage_in`), and still
        // past 60 s with the stride kept as one class (16ffcad7e). 26 of the 48 cases of
        // `s22::the_cover_answers_where_the_solver_alone_answered_on_two_shapes_at_moduli_5_and_7`
        // are refused again (`REFUSED_AT_A_STRIDE`, PRES-direct-stride-answer-downstream).
        let (true, Some(lo), Some(hi)) = (list, &p.lo, &p.hi) else {
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
    let mut set = Classed::plain(IntervalSet::from_pieces(ranges));
    for c in &strided {
        set = set.join(c);
    }
    Ok(Some(set))
}

/// A part of [`direct`] as a set: rows projected; a disjunction of blocks, the union of their
/// projections.
fn as_set(
    p: Part,
    s: &Atom,
    within: &IntervalSet,
    list: bool,
    work: &mut Work,
) -> Result<Option<(Classed, HashSet<Atom>)>, Refusal> {
    Ok(match p {
        Part::Set(set, atoms) => Some((set, atoms)),
        Part::Rows(rows) => {
            block_set(&rows, s, within, list, work)?.map(|set| (set, others(&rows, s)))
        }
        Part::Alts(blocks) => {
            let mut set = Classed::plain(IntervalSet::empty());
            let mut atoms = HashSet::new();
            for b in &blocks {
                let Some(p) = block_set(b, s, within, list, work)? else {
                    return Ok(None);
                };
                set = set.join(&p);
                atoms.extend(others(b, s));
            }
            Some((set, atoms))
        }
    })
}

/// The union of disjuncts for [`direct`]: where every disjunct is rows or blocks of rows, the
/// blocks, unprojected; else the union of their projections.
fn joined_parts(
    parts: Vec<Part>,
    s: &Atom,
    within: &IntervalSet,
    work: &mut Work,
) -> Result<Option<Part>, Refusal> {
    if parts.iter().all(|p| !matches!(p, Part::Set(..))) {
        let mut blocks: Vec<Vec<Con>> = Vec::new();
        for p in parts {
            match p {
                Part::Rows(rows) => blocks.push(rows),
                Part::Alts(more) => blocks.extend(more),
                Part::Set(..) => unreachable!("no set among the parts"),
            }
        }
        return Ok(Some(Part::Alts(blocks)));
    }
    let mut set = Classed::plain(IntervalSet::empty());
    let mut atoms: HashSet<Atom> = HashSet::new();
    for p in parts {
        let Some((p, more)) = as_set(p, s, within, false, work)? else {
            return Ok(None);
        };
        set = set.join(&p);
        if more.len() > atoms.len() {
            atoms = more.into_iter().chain(atoms).collect();
        } else {
            atoms.extend(more);
        }
    }
    Ok(Some(Part::Set(set, atoms)))
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
    for p in parts {
        match p {
            Part::Rows(r) => rows.extend(r),
            Part::Set(set, atoms) => sets.push((set, atoms)),
            Part::Alts(blocks) => {
                let atoms = blocks.iter().flat_map(|b| others(b, s)).collect();
                alts.push((blocks, atoms));
            }
        }
    }
    let r0 = rows.len();
    let a0 = r0 + sets.len();
    let n = a0 + alts.len();
    let mut parent: Vec<usize> = (0..n).collect();
    fn root(p: &mut [usize], mut i: usize) -> usize {
        while p[i] != i {
            p[i] = p[p[i]];
            i = p[i];
        }
        i
    }
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
        let (ri, rj) = (root(&mut parent, i), root(&mut parent, j));
        // The least index the root, so that a group, and the order of `groups` below, do not
        // depend on the order a hash set of atoms is read in (Sol, round 2 of PRES-pugh-xr).
        parent[ri.max(rj)] = ri.min(rj);
    }
    work.read(read)?;
    // Ordered, so that the work charged before a group not shown exact is the same on every run.
    type Group = (Vec<Con>, Vec<usize>, Vec<usize>);
    let mut groups: BTreeMap<usize, Group> = BTreeMap::new();
    for (i, k) in rows.iter().enumerate() {
        let r = root(&mut parent, i);
        groups.entry(r).or_default().0.push(k.clone());
    }
    for j in 0..sets.len() {
        let r = root(&mut parent, r0 + j);
        groups.entry(r).or_default().1.push(j);
    }
    for j in 0..alts.len() {
        let r = root(&mut parent, a0 + j);
        groups.entry(r).or_default().2.push(j);
    }
    // `R ∧ Bi` for each block `Bi`, every row copied charged.
    let distribute = |group: &[Con], blocks: &[Vec<Con>], work: &mut Work| {
        let mut out = Vec::with_capacity(blocks.len());
        for b in blocks {
            work.read((group.len() + b.len()) as u64)?;
            let mut block = group.to_vec();
            block.extend(b.iter().cloned());
            out.push(block);
        }
        Ok::<_, Refusal>(out)
    };
    if groups.len() == 1 && sets.is_empty() && alts.len() == 1 {
        let (group, _, _) = groups.into_values().next().expect("one group");
        let (blocks, _) = alts.pop().expect("one disjunction");
        return Ok(Some(Part::Alts(distribute(&group, &blocks, work)?)));
    }
    let mut set = Classed::plain(IntervalSet::top());
    for (group, held, ors) in groups.values() {
        let p = match (group.is_empty(), held.as_slice(), ors.as_slice()) {
            (false, [], []) => match block_set(group, s, within, !cut, work)? {
                Some(p) => p,
                None => return Ok(None),
            },
            (true, [j], []) => sets[*j].0.clone(),
            (_, [], [j]) => {
                let blocks = distribute(group, &alts[*j].0, work)?;
                match as_set(Part::Alts(blocks), s, within, !cut, work)? {
                    Some((p, _)) => p,
                    None => return Ok(None),
                }
            }
            (_, [], [_, _, ..]) if cut => match cut_at_shared(group, ors, &alts, s, work)? {
                Some(true) => Classed::plain(IntervalSet::range(End::NegInf, End::PosInf)),
                Some(false) => Classed::plain(IntervalSet::empty()),
                None => return Ok(None),
            },
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
    Ok(Some(Part::Set(set, atoms)))
}

/// Whether a group of [`met`] with rows `group` and two or more disjunctions `ors` of `alts`
/// has a point, where none of it reads `s` (as in the emptiness check of [`has_points`], whose
/// `s` occurs nowhere): such a group bounds no value of `s`, so its projection onto `s` is every
/// value or none. The disjunctions are tied through atoms they share; where some atom `t` is
/// read by every one of them (the least such, so the same on every run), the group is projected
/// onto `t` by [`met`] itself, which joins its items through atoms other than `t` only, and has
/// a point exactly when that projection is not empty. `None` where no atom is shared by all, or
/// where the projection onto `t` is not exact (again two disjunctions in one of its groups;
/// that inner call cuts no further).
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
    parts.extend(ors.iter().map(|j| Part::Alts(alts[*j].0.clone())));
    let top = IntervalSet::top();
    let set = match met(parts, &t, &top, false, work)? {
        None => return Ok(None),
        Some(Part::Set(set, _)) => set,
        Some(p @ (Part::Rows(_) | Part::Alts(_))) => match as_set(p, &t, &top, true, work)? {
            Some((set, _)) => set,
            None => return Ok(None),
        },
    };
    Ok(Some(!set.is_empty()))
}

/// A progression of values of a cell: `lo`, `lo + step`, ..., `hi`, `step` 2 or more.
struct Stride {
    step: Int,
    lo: Int,
    hi: Int,
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
    let mut parent: Vec<usize> = Vec::new();
    fn root(p: &mut [usize], mut i: usize) -> usize {
        while p[i] != i {
            p[i] = p[p[i]];
            i = p[i];
        }
        i
    }
    for k in rows {
        let mut first = None;
        for a in k.lin.terms.keys() {
            let n = parent.len();
            let i = *index.entry(a).or_insert(n);
            if i == n {
                parent.push(n);
            }
            match first {
                None => first = Some(i),
                Some(f) => {
                    let (x, y) = (root(&mut parent, f), root(&mut parent, i));
                    parent[x] = y;
                }
            }
        }
    }
    let Some(&at) = index.get(s) else {
        return Vec::new();
    };
    let top = root(&mut parent, at);
    (rows.iter())
        .filter(|k| (k.lin.terms.keys().next()).is_some_and(|a| root(&mut parent, index[a]) == top))
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
    let mut parent: Vec<usize> = Vec::new();
    fn root(p: &mut [usize], mut i: usize) -> usize {
        while p[i] != i {
            p[i] = p[p[i]];
            i = p[i];
        }
        i
    }
    for k in rows {
        let mut first = None;
        for a in k.lin.terms.keys() {
            let n = parent.len();
            let i = *index.entry(a).or_insert(n);
            if i == n {
                parent.push(n);
            }
            match first {
                None => first = Some(i),
                Some(f) => {
                    let (x, y) = (root(&mut parent, f), root(&mut parent, i));
                    parent[x.max(y)] = x.min(y);
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
        let r = root(&mut parent, index[a]);
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
