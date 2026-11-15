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
// of step 1 (COMPLEXITY.md row PRES-project-exact-solver).
// Trigger: a holed disjunct (a stride, `x + 2 * y == 0`), or values each disjunction allows
// through a different disjunct. Tests: `exact::tests`, zedc_preimage
// `or_if_projections_keep_the_gaps_the_if_reading_shows`.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};

use super::formula::Id;
use super::{Atom, Con, Each, Factor, Formula, Lin, Model, Refusal, Rel};

mod projection;
pub use projection::{METHOD, Method};
use projection::{Strided, Tail};

/// The work allowed to one call of `exact_each`, in units of one constraint read: a
/// question of the solver is charged the constraints of the formula asked, and a cell the
/// constraints read to make it. Past it the symbols left are refused with
/// [`Refusal::Work`].
pub const EXACT_LIMIT: u64 = 20_000_000;

thread_local! {
    /// Test control: a work limit in place of [`EXACT_LIMIT`].
    pub static EXACT_LIMIT_SET: Cell<Option<u64>> = const { Cell::new(None) };
    /// Test control: the solver's answer as it is, with no cover (the answer before
    /// PRES-project-exact-solver), for the tests that compare the two.
    pub static EXACT_OFF: Cell<bool> = const { Cell::new(false) };
    /// The questions `exact_each` has asked on this thread, read by tests.
    pub static EXACT_QUESTIONS: Cell<u64> = const { Cell::new(0) };
    /// The work `exact_each` has used on this thread, read by tests and benchmarks.
    pub static EXACT_WORK: Cell<u64> = const { Cell::new(0) };
}

/// The units of work used and allowed.
struct Work {
    used: u64,
    limit: u64,
}

impl Work {
    fn charge(&mut self, units: u64) -> Result<(), Refusal> {
        self.used = self.used.saturating_add(units);
        EXACT_WORK.set(EXACT_WORK.get().saturating_add(units));
        if self.used > self.limit {
            return Err(Refusal::Work);
        }
        Ok(())
    }
}

/// The exact projection of `f` onto each of `syms`, from `found`, the solver's answer, each of
/// its sets holding every value with a point (with any disjunction it left out, wider but
/// still holding them). A symbol the solver refused keeps its refusal; a symbol whose cover
/// is refused or passes the work limit is refused with that cause. The causes of the
/// disjunctions left out are kept only where a symbol is still refused, since each set
/// answered here is the exact one.
pub(super) fn exact_each(f: &Formula, syms: &[Atom], found: Each) -> Each {
    if EXACT_OFF.get() || std::env::var_os("ZED_EXACT_OFF").is_some() {
        return found;
    }
    let (each, skipped) = found;
    let size = constraints(f);
    let factors = factors(f);
    let mut work = Work {
        used: 0,
        limit: EXACT_LIMIT_SET.get().unwrap_or(EXACT_LIMIT),
    };
    let mut points: Vec<Model> = Vec::new();
    let mut out = Vec::with_capacity(each.len());
    for (s, got) in syms.iter().zip(each) {
        let t0 = std::time::Instant::now();
        let q0 = EXACT_QUESTIONS.get();
        let h0 = got.clone(); // TMPDBG
        if std::env::var_os("ZED_EXACT_TRACE").is_some() {
            eprintln!("ENTER s={s:?} h={got:?} f={f:?}");
        } // TMPDBG
        out.push(got.and_then(|h| cover(f, s, &h, size, &factors, &mut points, &mut work)));
        if std::env::var_os("ZED_EXACT_TRACE").is_some() {
            let ms = t0.elapsed().as_micros();
            eprintln!(
                "TRACE {ms}us q={} size={size} s={s:?} h={:?} out={:?} f={f:?}",
                EXACT_QUESTIONS.get() - q0,
                h0.as_ref().map(|h| h.pieces().count()),
                out.last().map(|r| r.as_ref().map(|o| o.pieces().count()))
            );
        } // TMPDBG
    }
    let skipped = if out.iter().any(Result::is_err) {
        skipped
    } else {
        Vec::new()
    };
    (out, skipped)
}

/// The values of `s` with a point of `f`, given `h`, a set holding them all: the cover of the
/// module note. `points` are points of `f` found before, for this symbol or another, and
/// those found here are added to them.
fn cover(
    f: &Formula,
    s: &Atom,
    h: &IntervalSet,
    size: u64,
    factors: &HashSet<Atom>,
    points: &mut Vec<Model>,
    work: &mut Work,
) -> Result<IntervalSet, Refusal> {
    let mut found = IntervalSet::empty();
    let mut gap = h.clone();
    let within = h.hull();
    let mut strides: Vec<Stride> = Vec::new();
    // The parts with holes and no end found by the cells, and the pieces with no end of their
    // union that ranges cannot hold (`projection::ranges`).
    let mut open: Vec<Strided> = Vec::new();
    let mut tails: Vec<Tail> = Vec::new();
    let mut read = 0;
    loop {
        while read < points.len() && !gap.is_empty() {
            let m = points[read].clone();
            read += 1;
            if gap.contains_end(&fin(&value(&Lin::atom(s.clone()), &m))) {
                work.charge(size)?;
                let (mut c, more, holed) = cell(f, &m, s, factors, &within, work)?;
                if !holed.is_empty() {
                    // The parts with holes and no end of every cell so far, joined: where the
                    // values found fill a tail up to an end, the values left of it are listed.
                    open.extend(holed);
                    let (filled, left) = projection::ranges(&open, work)?;
                    c = c.join(&filled);
                    let known = found.join(&c);
                    tails = Vec::new();
                    let mut listed = Vec::new();
                    for t in left {
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
                gap = gap.minus(&c);
                found = found.join(&c);
                strides.extend(more);
            }
        }
        if gap.is_empty() {
            return Ok(found);
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
            work.charge(size + 4)?;
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
            match super::satisfiable(&q)? {
                None => return Err(Refusal::Work),
                Some(m) => points.push(m),
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
            work.charge(size + 4)?;
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
            // A refusal of this question only leaves the gap to the questions by piece.
            match super::satisfiable(&q) {
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
            return Ok(found);
        };
        work.charge(size + 2)?;
        EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
        let piece = IntervalSet::range(piece.0, piece.1);
        let q = Formula::and(vec![f.clone(), super::member(s, &piece)]);
        match super::satisfiable(&q)? {
            None => gap = gap.minus(&piece),
            Some(m) => points.push(m),
        }
    }
}

/// A progression of values of a cell: `lo`, `lo + step`, ..., `hi`, `step` 2 or more.
struct Stride {
    step: Int,
    lo: Int,
    hi: Int,
}

/// The residues modulo `st.step` of the values of `found` from `st.lo` to `st.hi`, each piece
/// read charged one unit of `work`; a piece as long as the step holds every residue.
fn residues(found: &IntervalSet, st: &Stride, work: &mut Work) -> Result<IntervalSet, Refusal> {
    let mut have = IntervalSet::empty();
    for (l, u) in found
        .meet(&IntervalSet::range(fin(&st.lo), fin(&st.hi)))
        .pieces()
    {
        work.charge(1)?;
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
/// `st.step` and hold no value whose residue is in `have`; each piece read charged one unit.
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
        work.charge(1)?;
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

/// The value of `l` at `m`, each atom absent from `m` zero and each product read as an atom of
/// its own, as the solver reads its points.
fn value(l: &Lin, m: &Model) -> Int {
    let mut v = l.constant.clone();
    for (a, k) in &l.terms {
        if let Some(x) = m.get(a) {
            v = &v + &(k * x);
        }
    }
    v
}

fn fin(v: &Int) -> End {
    End::Fin(Num::from(v))
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
    let mut rows = Vec::new();
    let mut truth = HashMap::new();
    if implicant(f, m, true, &mut rows, &mut HashSet::new(), &mut truth) {
        let rows = joined(&rows, s);
        let product = |k: &Con| (k.lin.terms.keys()).any(|a| matches!(a, Atom::Product(..)));
        let how = projection::method();
        if !rows.iter().any(product) && how == Method::Pugh {
            // The exact projection of the implicant: its parts with no holes or with an end are
            // the cell's; those with holes and no end go to the cover, which joins them with
            // the other cells' (`projection::ranges`).
            let parts = projection::pugh(&rows, s, work)?;
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
            // exact step (`eliminated_whole`), its rows charged to the work.
            let left = super::eliminated(&rows, &|a| a == s)
                .or_else(|| super::eliminated_whole(&rows, &|a| a == s));
            if let Some(left) = left {
                work.charge(left.len() as u64)?;
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
                    && let Some(left) = super::eliminated(&fixed(&rows, &fix, m), &|a| a == s)
                {
                    c = c.join(&bounded(&left, s));
                }
            }
            for d in directions(&rows, s, factors) {
                work.charge(constraints(f))?;
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
    let Some(mut two) = super::eliminated(rows, &|a| a == s || a == q) else {
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
    let Some(over_q) = super::eliminated(&two, &|a| a == q) else {
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
            work.charge(two.len() as u64)?;
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

/// The values of `s` that rows over `s` alone allow (each row with no atom holding or not).
fn bounded(rows: &[Con], s: &Atom) -> IntervalSet {
    let mut lo: Option<Int> = None;
    let mut hi: Option<Int> = None;
    for k in rows {
        let Some(a) = k.lin.terms.get(s) else {
            if !holds_at(k, &k.lin.constant) {
                return IntervalSet::empty();
            }
            continue;
        };
        let c = &k.lin.constant;
        let (l, u) = match k.rel {
            // `a·s + c >= 0`: `s >= ceil(-c / a)` with `a` above zero, else `s <= floor(c / -a)`.
            Rel::Ge if a.is_positive() => (Some(-&c.div_floor(a)), None),
            Rel::Ge => (None, Some(c.div_floor(&-a))),
            Rel::Eq => {
                if !c.mod_floor(a).is_zero() {
                    return IntervalSet::empty();
                }
                let v = -&c.div_floor(a);
                (Some(v.clone()), Some(v))
            }
        };
        if let Some(l) = l
            && lo.as_ref().is_none_or(|x| &l > x)
        {
            lo = Some(l);
        }
        if let Some(u) = u
            && hi.as_ref().is_none_or(|x| &u < x)
        {
            hi = Some(u);
        }
    }
    if let (Some(l), Some(u)) = (&lo, &hi)
        && l > u
    {
        return IntervalSet::empty();
    }
    IntervalSet::range(
        lo.as_ref().map_or(End::NegInf, fin),
        hi.as_ref().map_or(End::PosInf, fin),
    )
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
    let key = Id::of(f);
    if let Some(k) = key
        && let Some(v) = memo.get(&k)
    {
        return v.clone();
    }
    let out = match f {
        Formula::Con(c) => {
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
        }
        Formula::Not(g) => IntervalSet::top().minus(&along(g, m, d, memo)),
        Formula::And(gs) => {
            let mut acc = IntervalSet::top();
            for g in gs.iter() {
                acc = acc.meet(&along(g, m, d, memo));
                if acc.is_empty() {
                    break;
                }
            }
            acc
        }
        Formula::Or(gs) => {
            let mut acc = IntervalSet::empty();
            for g in gs.iter() {
                acc = acc.join(&along(g, m, d, memo));
            }
            acc
        }
    };
    if let Some(k) = key {
        memo.insert(k, out.clone());
    }
    out
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
    let key = Id::of(f);
    if let Some(k) = key
        && seen.contains(&(k, want))
    {
        return true;
    }
    let ok = match f {
        Formula::Con(c) => {
            let v = value(&c.lin, m);
            let holds = match c.rel {
                Rel::Ge => !v.is_negative(),
                Rel::Eq => v.is_zero(),
            };
            if holds == want {
                rows.push(if want { c.clone() } else { negated(c, &v) });
            }
            holds == want
        }
        Formula::Not(g) => implicant(g, m, !want, rows, seen, truth),
        Formula::And(gs) | Formula::Or(gs) => {
            // A conjunction that holds, or a disjunction that fails, needs every part; the
            // others need one.
            let every = matches!(f, Formula::And(_)) == want;
            if every {
                gs.iter().all(|g| implicant(g, m, want, rows, seen, truth))
            } else {
                let at = rows.len();
                let mut any = false;
                for g in gs.iter() {
                    if holds_as(g, m, truth) == want {
                        any = implicant(g, m, want, rows, seen, truth);
                        break;
                    }
                }
                if !any {
                    rows.truncate(at);
                }
                any
            }
        }
    };
    if ok && let Some(k) = key {
        seen.insert((k, want));
    }
    ok
}

/// Whether `f` holds at `m`, read as [`value`] reads atoms; a shared part is read once (`memo`,
/// by [`Id`]).
fn holds_as(f: &Formula, m: &Model, memo: &mut HashMap<Id, bool>) -> bool {
    let key = Id::of(f);
    if let Some(k) = key
        && let Some(&b) = memo.get(&k)
    {
        return b;
    }
    let out = match f {
        Formula::Con(c) => holds_at(c, &value(&c.lin, m)),
        Formula::Not(g) => !holds_as(g, m, memo),
        Formula::And(gs) => gs.iter().all(|g| holds_as(g, m, memo)),
        Formula::Or(gs) => gs.iter().any(|g| holds_as(g, m, memo)),
    };
    if let Some(k) = key {
        memo.insert(k, out);
    }
    out
}

/// Whether the constraint `c` holds where its form is `v`.
fn holds_at(c: &Con, v: &Int) -> bool {
    match c.rel {
        Rel::Ge => !v.is_negative(),
        Rel::Eq => v.is_zero(),
    }
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
    fn walk(f: &Formula, seen: &mut HashSet<Id>) -> u64 {
        if let Some(k) = Id::of(f)
            && !seen.insert(k)
        {
            return 0;
        }
        match f {
            Formula::Con(_) => 1,
            Formula::Not(g) => walk(g, seen),
            Formula::And(gs) | Formula::Or(gs) => gs.iter().map(|g| walk(g, seen)).sum(),
        }
    }
    walk(f, &mut HashSet::new()).max(1)
}

/// The atoms that are factors of a product atom of `f`.
fn factors(f: &Formula) -> HashSet<Atom> {
    fn walk(f: &Formula, out: &mut HashSet<Atom>, seen: &mut HashSet<Id>) {
        if let Some(k) = Id::of(f)
            && !seen.insert(k)
        {
            return;
        }
        match f {
            Formula::Con(c) => {
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
            }
            Formula::Not(g) => walk(g, out, seen),
            Formula::And(gs) | Formula::Or(gs) => gs.iter().for_each(|g| walk(g, out, seen)),
        }
    }
    let mut out = HashSet::new();
    walk(f, &mut out, &mut HashSet::new());
    out
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

#[cfg(test)]
mod tests {
    use super::super::{member, project_each};
    use super::*;

    /// A pseudo-random number generator (xorshift64), seeded by [`crate::seed::seed`]: a new
    /// seed on each run, printed, which `ZED_TEST_SEED` repeats.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }

        fn int(&mut self, lo: i64, hi: i64) -> i64 {
            lo + self.below((hi - lo + 1) as u64) as i64
        }
    }

    fn a(s: &str) -> Atom {
        Atom::Sym(s.into())
    }

    fn lin(terms: &[(&str, i64)], k: i64) -> Lin {
        Lin {
            terms: (terms.iter())
                .filter(|(_, c)| *c != 0)
                .map(|(s, c)| (a(s), Int::from(*c)))
                .collect(),
            constant: Int::from(k),
        }
    }

    fn ge(terms: &[(&str, i64)], k: i64) -> Formula {
        Formula::Con(Con::ge(&lin(terms, k), &Lin::constant(0)))
    }

    fn eq(terms: &[(&str, i64)], k: i64) -> Formula {
        Formula::Con(Con::eq(&lin(terms, k), &Lin::constant(0)))
    }

    const NAMES: [&str; 3] = ["x", "y", "z"];
    const B: i64 = 4;

    /// `f` with each of x, y and z in `-B..=B`.
    fn boxed(f: Formula) -> Formula {
        let mut all: Vec<Formula> = (NAMES.iter())
            .map(|n| member(&a(n), &IntervalSet::of(-B, B)))
            .collect();
        all.push(f);
        Formula::and(all)
    }

    /// The values of `sym` at the points of `f` in the box, by trying every point.
    fn brute(f: &Formula, sym: &str) -> IntervalSet {
        let at = NAMES.iter().position(|n| *n == sym).unwrap();
        let mut set = IntervalSet::empty();
        let r = -B..=B;
        for x in r.clone() {
            for y in r.clone() {
                for z in r.clone() {
                    let p = [x, y, z];
                    let m: Model = (NAMES.iter().zip(p))
                        .map(|(n, v)| (a(n), Int::from(v)))
                        .collect();
                    if f.holds(&m) {
                        set = set.join(&IntervalSet::single(p[at]));
                    }
                }
            }
        }
        set
    }

    /// A random constraint over one to three of x, y and z, coefficients from -3 to 3.
    fn constraint(rng: &mut Rng) -> Formula {
        let terms: Vec<(&str, i64)> = NAMES.iter().map(|n| (*n, rng.int(-3, 3))).collect();
        let terms: Vec<(&str, i64)> = if terms.iter().all(|t| t.1 == 0) {
            vec![("x", 1)]
        } else {
            terms
        };
        let k = rng.int(-4, 4);
        if rng.below(3) == 0 {
            eq(&terms, k)
        } else {
            ge(&terms, k)
        }
    }

    fn formula(rng: &mut Rng, depth: u32) -> Formula {
        if depth == 0 || rng.below(4) == 0 {
            return constraint(rng);
        }
        let n = 2 + rng.below(2) as usize;
        let parts: Vec<Formula> = (0..n).map(|_| formula(rng, depth - 1)).collect();
        match rng.below(5) {
            0 => Formula::negate(Formula::and(parts)),
            1 | 2 => Formula::and(parts),
            _ => Formula::or(parts),
        }
    }

    /// The projections of random formulas over x, y and z in a box, with strides
    /// (coefficients from -3 to 3, equations) and nested disjunctions and negations, are the
    /// sets of values that trying each of the 729 points gives: never wider, never narrower.
    /// The solver alone (`EXACT_OFF`) gives wider sets on some of them; a refusal is counted
    /// and printed with its cause.
    #[test]
    fn random_formulas_project_to_the_values_of_their_points() {
        let seed = crate::seed::seed("random_formulas_project_to_the_values_of_their_points");
        let mut rng = Rng(seed | 1);
        let syms: Vec<Atom> = NAMES.iter().map(|n| a(n)).collect();
        let (mut wrong, mut refused, mut wider_before) = (Vec::new(), Vec::new(), 0);
        for round in 0..300 {
            let f = boxed(formula(&mut rng, 3));
            let each = project_each(&f, &syms);
            EXACT_OFF.set(true);
            let before = project_each(&f, &syms);
            EXACT_OFF.set(false);
            for (k, n) in NAMES.iter().enumerate() {
                let want = brute(&f, n);
                if let Ok((b, _)) = &before
                    && let Ok(b) = &b[k]
                    && b != &want
                {
                    wider_before += 1;
                }
                match each.as_ref().map(|e| &e.0[k]) {
                    Ok(Ok(got)) if got == &want => {}
                    Ok(Ok(got)) => wrong.push(format!("round {round} {n}: {got} not {want}: {f}")),
                    Ok(Err(e)) | Err(e) => refused.push(format!("round {round} {n}: {e:?}")),
                }
            }
        }
        println!("seed {seed}: {wider_before} wider before, refused {refused:#?}");
        assert!(wrong.is_empty(), "seed {seed}: {wrong:#?}");
        assert!(refused.len() <= 3, "seed {seed}: {refused:#?}");
    }

    /// A value that each disjunction allows through a different disjunct, where no one
    /// combination of them does: `(x == 1 && y == 0 || x == 3 && y == 1) && (x == 1 && y == 1 ||
    /// x == 3 && y == 0)` has no point, while the solver's meet of the unions of hulls keeps
    /// x in {1, 3}.
    #[test]
    fn values_two_disjunctions_allow_only_apart_are_left_out() {
        let d = |p: i64, q: i64, r: i64, s: i64| {
            Formula::or(vec![
                Formula::and(vec![eq(&[("x", 1)], -p), eq(&[("y", 1)], -q)]),
                Formula::and(vec![eq(&[("x", 1)], -r), eq(&[("y", 1)], -s)]),
            ])
        };
        let f = boxed(Formula::and(vec![d(1, 0, 3, 1), d(1, 1, 3, 0)]));
        let each = project_each(&f, &[a("x"), a("y")]).unwrap();
        assert_eq!(each.0[0], Ok(IntervalSet::empty()), "{f}");
        assert_eq!(each.0[1], Ok(IntervalSet::empty()), "{f}");
    }

    /// A disjunct with a stride keeps its holes: `x != 1 || x + 2 * y == 0` (the shape of the
    /// zedc_preimage test of FAIL-or-if-projection-not-exact) gives `x` every value but 1, and
    /// `(y >= 1 || y <= -1) && x == 3 * y + 1` the values of `3 * y + 1` in the box.
    #[test]
    fn a_disjunct_with_a_stride_keeps_its_holes() {
        let f = boxed(Formula::or(vec![
            ge(&[("x", 1)], -2),
            ge(&[("x", -1)], 0),
            eq(&[("x", 1), ("y", 2)], 0),
        ]));
        let x = project(&f, "x");
        assert_eq!(x, brute(&f, "x"), "{f}");
        assert!(!x.contains(1), "{x}");
        let f = boxed(Formula::and(vec![
            Formula::or(vec![ge(&[("y", 1)], -1), ge(&[("y", -1)], -1)]),
            eq(&[("x", 1), ("y", -3)], -1),
        ]));
        assert_eq!(
            project(&f, "x"),
            IntervalSet::from_pieces(vec![(End::of(-2), End::of(-2)), (End::of(4), End::of(4)),])
        );
    }

    fn project(f: &Formula, s: &str) -> IntervalSet {
        project_each(f, &[a(s)]).unwrap().0.remove(0).unwrap()
    }

    /// A formula whose cover takes one question for each even value of x in `0..=2k`, the
    /// stride of `x == 2 * y` kept apart from the box by a disjunction.
    fn evens(k: i64) -> Formula {
        Formula::and(vec![
            Formula::or(vec![
                eq(&[("x", 1), ("y", -2)], 0),
                eq(&[("x", 1), ("z", -2)], 0),
            ]),
            member(&a("x"), &IntervalSet::of(0, 2 * k)),
            member(&a("z"), &IntervalSet::of(0, 2 * k)),
        ])
    }

    /// The work limit on both sides: allowed exactly the work the cover of [`evens`] takes, it
    /// answers with the exact set (the even values); allowed one unit less, it refuses with
    /// [`Refusal::Work`]. The work is counted, so both runs stop at the same point.
    #[test]
    fn the_work_limit_is_met_alike_on_both_sides() {
        let f = evens(20);
        let want =
            IntervalSet::from_pieces((0..=20).map(|v| (End::of(2 * v), End::of(2 * v))).collect());
        EXACT_WORK.set(0);
        assert_eq!(project(&f, "x"), want);
        let used = EXACT_WORK.replace(0);
        assert!(used > 0);
        EXACT_LIMIT_SET.set(Some(used));
        assert_eq!(project(&f, "x"), want);
        assert_eq!(
            EXACT_WORK.replace(0),
            used,
            "the work is not the same on a second run"
        );
        EXACT_LIMIT_SET.set(Some(used - 1));
        let r = project_each(&f, &[a("x")]).unwrap().0.remove(0);
        EXACT_LIMIT_SET.set(None);
        assert_eq!(r, Err(Refusal::Work));
    }

    /// An unbounded set with holes, the even values of `x == 2 * y || x == 2 * z` with no
    /// bound, is not a finite union of ranges, so no answer is exact: it is refused at the work
    /// limit, here set low.
    #[test]
    fn an_unbounded_set_with_holes_is_refused_at_the_work_limit() {
        let f = Formula::or(vec![
            eq(&[("x", 1), ("y", -2)], 0),
            eq(&[("x", 1), ("z", -2)], 0),
        ]);
        EXACT_LIMIT_SET.set(Some(10_000));
        let r = project_each(&f, &[a("x")]).unwrap().0.remove(0);
        EXACT_LIMIT_SET.set(None);
        assert_eq!(r, Err(Refusal::Work));
    }

    /// The conjunction of a pendants part that ran forever (l01_39 `pendants`, rows 5 to 9):
    /// `w == 2·a - b` with `a <= -14`, so `w` unbounded below. The elimination that never
    /// grows its rows leaves atoms of it, so each cell was one line and each question found
    /// one more value; with every exact step done (`eliminated_whole`) one cell covers it.
    #[test]
    fn an_unbounded_conjunction_needs_one_cell() {
        let f = Formula::and(vec![
            ge(&[("a", -1)], -14),
            ge(&[("b", 1)], -1),
            ge(&[("b", -1)], 8),
            ge(&[("z2", -1)], -9),
            ge(&[("z3", -1)], 2),
            ge(&[("a", -2), ("b", -1), ("c", -1), ("z2", 1)], -7),
            ge(&[("a", -1), ("b", -2), ("z2", 1)], -2),
            eq(&[("a", -1), ("c", -1), ("z3", 1)], -5),
            ge(&[("a", 1), ("b", 1), ("c", 1), ("z2", -1)], 6),
            ge(&[("z2", -1), ("z3", 1)], -11),
            eq(&[("w", -1), ("a", 2), ("b", -1)], 0),
            ge(&[("w", -1)], -29),
        ]);
        EXACT_QUESTIONS.set(0);
        // Every `w <= -31`, and -29: -30 needs `a == -14`, `b == 2`, so `z2 >= -8`, past `z2 <= -9`.
        let want = IntervalSet::from_pieces(vec![
            (End::NegInf, End::of(-31)),
            (End::of(-29), End::of(-29)),
        ]);
        assert_eq!(project(&f, "w"), want);
        assert!(
            EXACT_QUESTIONS.get() <= 2,
            "{} questions",
            EXACT_QUESTIONS.get()
        );
    }
    /// The questions of the cover on a stride, as the remainder reading writes one (`y == 2·q
    /// + r` with `r == 0`), and on remainders kept in a range (`x == 1024·q + r` with `r` in
    /// `0..=36`), each in a box: the even values of `y` (but -4 and -2, which a case leaves out) from one point, along the direction that
    /// keeps the equation (`directions`); a run of 37 values of `x` from each point, with `q`
    /// fixed (`strides_fixed`).
    #[test]
    fn strides_and_remainders_are_covered_a_few_points_each() {
        let f = Formula::and(vec![
            eq(&[("y", 1), ("q", -2), ("r", -1)], 0),
            eq(&[("r", 1)], 0),
            member(&a("y"), &IntervalSet::of(-1000, 1000)),
            Formula::or(vec![ge(&[("y", 1)], 0), ge(&[("y", -1)], -5)]),
        ]);
        let evens = (-500..=500).filter(|v| !(-2..=-1).contains(v));
        let want =
            IntervalSet::from_pieces(evens.map(|v| (End::of(2 * v), End::of(2 * v))).collect());
        EXACT_QUESTIONS.set(0);
        assert_eq!(project(&f, "y"), want);
        assert!(
            EXACT_QUESTIONS.get() <= 4,
            "{} questions",
            EXACT_QUESTIONS.get()
        );
        let f = Formula::and(vec![
            eq(&[("x", 1), ("q", -1024), ("r", -1)], 0),
            member(&a("r"), &IntervalSet::of(0, 1023)),
            member(&a("x"), &IntervalSet::of(-10240, 10239)),
            Formula::or(vec![ge(&[("r", -1)], 36), ge(&[("r", 1)], -2000)]),
        ]);
        let want = IntervalSet::from_pieces(
            (-10..10)
                .map(|q| (End::of(1024 * q), End::of(1024 * q + 36)))
                .collect(),
        );
        EXACT_QUESTIONS.set(0);
        assert_eq!(project(&f, "x"), want);
        assert!(
            EXACT_QUESTIONS.get() <= 2 * 20 + 2,
            "{} questions",
            EXACT_QUESTIONS.get()
        );
    }
}
