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

use super::absorbing;
use super::formula::Id;
pub use super::meter::{
    EXACT_LIMIT, EXACT_LIMIT_SET, EXACT_OFF, EXACT_QUESTIONS, EXACT_WORK, FAST_WORK, QUESTION_WORK,
    SOLVER_UNIT,
};
use super::meter::{PIECE, Solver, Work};
use super::{Atom, Con, Each, Factor, Formula, Lin, Model, Refusal, Rel};

mod projection;
pub use projection::{METHOD, Method};
use projection::{Strided, Tail, bounded, fin, holds_at, value};

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
pub(super) fn exact_each(f: &Formula, syms: &[Atom], found: Each, solver: Solver) -> Each {
    if EXACT_OFF.get() {
        return found;
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
        return (out, Vec::new());
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
    let mut small_points: Vec<Vec<Model>> = vec![Vec::new(); parts.len()];
    let mut shown = vec![false; parts.len()];
    let mut wider = false;
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
    let answers: BTreeMap<&Atom, Result<IntervalSet, Refusal>> = (sorted.into_iter())
        .map(|(s, got)| {
            // Each symbol's cover has a limit of its own, as each refusal names one symbol: a
            // limit shared by the call would refuse a symbol by the work of those before it in
            // the order above, and batch where single answers (PRES-pugh-xr round 2, D).
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
                    return Ok(IntervalSet::range(End::NegInf, End::PosInf));
                };
                let p = &parts[i];
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
                        &mut alone,
                    );
                    if let Ok((set, kept)) = got {
                        shown[i] |= !set.is_empty();
                        wider |= kept;
                        return Ok(set);
                    }
                }
                let (set, kept) =
                    cover(&p.f, s, &h, p.size, &p.factors, &mut points[i], &mut work)?;
                wider |= kept;
                Ok(set)
            })();
            (s, answer)
        })
        .collect();
    let out: Vec<Result<IntervalSet, Refusal>> = syms.iter().map(|s| answers[s].clone()).collect();
    if !many {
        return (
            out,
            if wider {
                vec![Refusal::Repeats]
            } else {
                Vec::new()
            },
        );
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
            (Ok(false), _) => Ok(IntervalSet::empty()),
            (Err(e), _) => Err(e.clone()),
        })
        .collect();
    (
        out,
        if wider {
            vec![Refusal::Repeats]
        } else {
            Vec::new()
        },
    )
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
            && let Some(set) = tried(&mut fast, work.solver, |w| direct(f, &none, w))
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
/// with `true`, wider than exact for that cause ([`Refusal::Repeats`]).
fn cover(
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
    // No value has a point where the solver's set, which holds every value with one, is empty.
    if h.is_empty() {
        return Ok((IntervalSet::empty(), false));
    }
    // The exact projection read from the structure of `f`, with no question (`direct`). It lies
    // within `h` where `f` is the whole formula; for a part of it (`split`) it may not, where
    // another part has no point, and then every answer is made empty (`exact_each`).
    if factors.is_empty()
        && let Some(set) = tried(&mut { work.limit }, work.solver, |w| direct(f, s, w))
    {
        return Ok((set, false));
    }
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
/// projection of the part onto the symbol, with the atoms other than the symbol it reads.
#[derive(Clone)]
enum Part {
    Rows(Vec<Con>),
    Set(IntervalSet, HashSet<Atom>),
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
fn direct(f: &Formula, s: &Atom, work: &mut Work) -> Result<Option<IntervalSet>, Refusal> {
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
                    if let Part::Rows(rows) = v {
                        work.read(rows.len() as u64)?;
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
                            (false, Rel::Eq) => {
                                let mut set = IntervalSet::empty();
                                for v in [Int::from(-1), Int::from(1)] {
                                    let Some(p) = projected(&[negated(c, &v)], s, work)? else {
                                        return Ok(None);
                                    };
                                    set = set.join(&p);
                                }
                                Part::Set(set, others(std::slice::from_ref(c), s))
                            }
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
                    met(parts, s, work)?
                } else {
                    joined_parts(parts, s, work)?
                };
                let Some(v) = v else {
                    return Ok(None);
                };
                if let Some(k) = Id::of(g)
                    && holders.get(&k).is_some_and(|&n| n > 1)
                {
                    memo.insert((k, pos), v.clone());
                }
                values.push(v);
            }
        }
    }
    match values.pop().expect("the part of `f`") {
        Part::Rows(rows) => projected(&rows, s, work),
        Part::Set(set, _) => Ok(Some(set)),
    }
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

/// A part of [`direct`] as a set: rows projected.
fn as_set(
    p: Part,
    s: &Atom,
    work: &mut Work,
) -> Result<Option<(IntervalSet, HashSet<Atom>)>, Refusal> {
    Ok(match p {
        Part::Set(set, atoms) => Some((set, atoms)),
        Part::Rows(rows) => projected(&rows, s, work)?.map(|set| (set, others(&rows, s))),
    })
}

/// The union of disjuncts for [`direct`]: the union of their projections.
fn joined_parts(parts: Vec<Part>, s: &Atom, work: &mut Work) -> Result<Option<Part>, Refusal> {
    let mut set = IntervalSet::empty();
    let mut atoms: HashSet<Atom> = HashSet::new();
    for p in parts {
        let Some((p, more)) = as_set(p, s, work)? else {
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
/// atom but `s`, each projected, met.
fn met(parts: Vec<Part>, s: &Atom, work: &mut Work) -> Result<Option<Part>, Refusal> {
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
    let mut sets: Vec<(IntervalSet, HashSet<Atom>)> = Vec::new();
    for p in parts {
        match p {
            Part::Rows(r) => rows.extend(r),
            Part::Set(set, atoms) => sets.push((set, atoms)),
        }
    }
    let r0 = rows.len();
    let n = r0 + sets.len();
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
    let mut groups: BTreeMap<usize, (Vec<Con>, Vec<usize>)> = BTreeMap::new();
    for (i, k) in rows.iter().enumerate() {
        let r = root(&mut parent, i);
        groups.entry(r).or_default().0.push(k.clone());
    }
    for j in 0..sets.len() {
        let r = root(&mut parent, rows.len() + j);
        groups.entry(r).or_default().1.push(j);
    }
    let mut set = IntervalSet::range(End::NegInf, End::PosInf);
    for (group, held) in groups.values() {
        let p = match (group.is_empty(), held.as_slice()) {
            (false, []) => match projected(group, s, work)? {
                Some(p) => p,
                None => return Ok(None),
            },
            (true, [j]) => sets[*j].0.clone(),
            _ => return Ok(None),
        };
        set = set.meet(&p);
    }
    let mut atoms = others(&rows, s);
    for (_, more) in sets {
        atoms.extend(more);
    }
    Ok(Some(Part::Set(set, atoms)))
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
                projection::pugh(&rows, s, work)?
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

/// Calls `at` on each constraint of `f`, a shared part read once (by [`Id`]), the parts
/// waiting on an explicit stack (see [`fold`]).
fn each_constraint<'a>(f: &'a Formula, mut at: impl FnMut(&'a Con)) {
    let mut seen: HashSet<Id> = HashSet::new();
    let mut stack = vec![f];
    while let Some(g) = stack.pop() {
        if let Some(k) = Id::of(g)
            && !seen.insert(k)
        {
            continue;
        }
        match g {
            Formula::Con(c) => at(c),
            Formula::Not(h) => stack.push(h),
            Formula::And(gs) | Formula::Or(gs) => stack.extend(gs.iter()),
        }
    }
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

// The tests are a file of their own: they name the solver (`presburger.rs`), which calls this
// module, and a test module kept here would make the two import each other
// (`s_01f_import_graph`, row PRES-cover-wire).
#[cfg(test)]
mod tests;
