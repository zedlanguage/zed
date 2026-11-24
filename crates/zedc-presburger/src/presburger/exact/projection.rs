//! Two ways to give a cell of the cover (`super::cover`) the values of an implicant that run
//! without end, which the elimination of `super::cell` leaves out (PRES-pugh-exact-projection-
//! research; the stuck case is `an_unbounded_conjunction_needs_one_cell`, whose cells each held
//! eight values of a ray, so the cover never ended):
//! - [`pugh`]: the exact projection of the implicant onto the symbol, by the Omega test's
//!   projection (Pugh, "A practical algorithm for exact array dependence analysis", CACM 35(8),
//!   1992, the sections "Equality Constraints", "Detecting integer solutions using
//!   Fourier-Motzkin variable elimination" and "Projection of Integer Programming Problems",
//!   secs. 2.2, 2.3.2 and 4 of the expanded text; the crate root's References. Sec. 4.1: a
//!   protected variable is never eliminated by Fourier-Motzkin, and in an equality with `g`
//!   the gcd of the coefficients of the unprotected variables, `g > 1` adds a protected `σ` and
//!   the row `g·σ = sum over the protected i of (a_i mod g)·x_i`, after which that gcd is 1):
//!   equalities removed with Pugh's `mod^` step, the symbol kept as a protected variable
//!   whose residue is fixed when every other coefficient shares a factor, then each other
//!   variable removed by an exact Fourier-Motzkin step where every lower or every upper
//!   coefficient is 1, else by the dark shadow and every splinter next to a lower bound.
//!   The answer is a union of stride sets `{lo <= v <= hi, v == res mod step}`.
//! - [`rays`]: the recession directions of the implicant: a direction `d` with `A·d >= 0`
//!   over its inequalities, `E·d == 0` over its equalities and the symbol's step `d_s` below
//!   (or above) zero; with `g = |d_s|`, one point of the implicant in each residue of the
//!   symbol modulo `g` gives a ray of values from that point on. About `g + 1` questions.
//! - [`liaproj`]: the one disjunct of the implicant's projection that holds the cell's point,
//!   by model-based projection (Komuravelli, Gurfinkel and Chaki, "SMT-based model checking
//!   for recursive programs", CAV 2014, LIAProj), with Pugh's dark shadow chosen by the point
//!   where no divisibility literal holds the variable.
//!
//! Both are measured against each other and against the old cell in
//! docs/handoff/PRES-pugh-findings.md; they are switched by [`METHOD`] for that comparison.
//!
//! Published work used in this file. Each site names the author; the full citation is in the
//! crate's `lib.rs`, "References". Pugh 1991, doi:10.1145/125826.125848, and 1992,
//! doi:10.1145/135226.135233; Komuravelli, Gurfinkel and Chaki 2014,
//! doi:10.1007/978-3-319-08867-9_2, whose entry also covers Cooper's method.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashSet};

use zedc_int::int::{Int, IntRange, meet_range, row_range};
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::lattice::{Congruence, Lattice};

use super::super::formula::Id;
use super::super::meter::{EXACT_QUESTIONS, LISTED, PIECE, Work};
use super::super::{Atom, Classed, Con, Formula, Lin, Model, Refusal, Rel};
use super::classes::ClassUnion;

/// The in-cell step for the values an implicant has without end.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Method {
    /// The cell as before this research: elimination where it is exact, else runs or a fixed
    /// stride atom.
    Old,
    /// Pugh's exact projection of the implicant (`pugh`).
    Pugh,
    /// The old cell and the recession rays of the implicant (`rays`).
    Rays,
    /// The disjunct of the implicant's projection that holds the point, by model-based
    /// projection (`liaproj`).
    Liaproj,
}

thread_local! {
    /// Test control: the in-cell method, in place of [`Method::Pugh`]. Set by the tests that
    /// compare the methods; read from no environment variable (PRES-pugh-xr round 3: the rules
    /// allow no debug switch read from the environment in delivered code).
    pub static METHOD: Cell<Option<Method>> = const { Cell::new(None) };
}

/// The method in force: [`METHOD`] where set, else Pugh's. Model-based projection
/// ([`Method::Liaproj`]) is not the default: on the 38 tests of
/// PRES-cover-bench-regressions it passed 15 where Pugh passed 12, failing the same 22 for the
/// same causes (questions, memory); it asks 6 questions where
/// `an_unbounded_conjunction_needs_one_cell` allows 2, and refuses the repaired unit's `y`
/// with Growth (2026-11-18). Pugh with the cell's goal (PRES-pugh-goal) passes 14 of the 38
/// and answers all four names of the repaired unit.
pub fn method() -> Method {
    METHOD.get().unwrap_or(Method::Pugh)
}

/// `{v : lo <= v <= hi, v == res mod step}`, an absent end infinite, `step >= 1`,
/// `0 <= res < step`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Strided {
    pub(super) lo: Option<Int>,
    pub(super) hi: Option<Int>,
    pub(super) step: Int,
    pub(super) res: Int,
}

/// The exact projection of the conjunction `rows` onto `s`, as a union of stride sets, or as
/// much of it as holds `goal`; each row made is charged its terms and one more to `work`.
/// `rows` hold no product atom.
///
/// `goal` is the set of values the caller still needs: once the parts found so far hold all
/// of it, no further dark shadow or splinter is projected, so the answer may then leave out
/// values outside `goal`. The cell (`super::cell`) passes the hull of the solver's set less the
/// values it already has. Proof that the cell loses no value: every value of the projection is
/// the value of a point of `rows`, whose conjunction implies the formula (`super::implicant`;
/// `super::joined` drops only rows that share no atom with `s` and hold at the point, which
/// leaves the projection the same), so the value lies in the solver's set and in its hull;
/// a value left out is then one the cell already holds. Every value given is still one of the
/// projection, so the cell holds no value without a point. `IntervalSet::top()` asks for the
/// whole projection.
///
/// Complexity tradeoff: naive version, every splinter of every dark shadow projected
/// (Pugh 1992, "Projection"), exponential in the atoms removed: the repaired unit's `x`
/// (`exact::tests::every_name_of_the_repaired_unit_has_its_exact_answer`) took 4.8M units
/// against the limit of 3.1M, 1,562 parts. Used: an emptiness test of the values left before
/// each step of the projection, O(1), and each part found taken from them ([`Held::push`]); the
/// worst case is unchanged (a `goal` never held), and where it is held the splinters left are
/// not made: that `x` takes 180k units, 55 parts (2026-11-18).
pub(super) fn pugh(
    rows: &[Con],
    s: &Atom,
    goal: &IntervalSet,
    work: &mut Work,
) -> Result<Vec<Strided>, Refusal> {
    let mut out = Vec::new();
    let mut fresh = 0u32;
    let mut at = Int::from(1);
    let mut from = Int::from(0);
    let mut held = Held {
        left: Classed::plain(goal.clone()),
    };
    project(
        rows.to_vec(),
        s,
        &mut at,
        &mut from,
        work,
        &mut fresh,
        &mut held,
        &mut out,
    )?;
    Ok(out)
}

/// The values of the goal of [`pugh`] that no part found so far holds, or more: `left` holds
/// every such value, and may hold values a part holds where taking them would list them
/// ([`Held::push`]).
///
/// Proof that a `left` wider than the values not yet held changes no part found. `left` is
/// read in two places only: [`Held::done`], which stops the projection once it is empty, and
/// [`Held::push`], which takes a part's values from it. Let `T` be the values of the goal no
/// part found so far holds, and `L ⊇ T` (at the start `L = T`, the goal). (1) `done` is true
/// only where `L` is empty, so `T` is empty too: the projection stops only where the exact
/// `left` would have stopped it, and every part it pushes is one of the projection, so the
/// parts found are a subset of the projection's and a superset of those the exact `left` finds
/// (the projection is the same depth-first walk, and each step it takes with the exact `left`
/// it takes here, `L` being empty no sooner; the charges differ, so either may be refused at
/// the limit where the other is not, and a refusal gives no parts at all). (2) A push of part
/// `P` makes `T' = T \ P`, and
/// `L'` is `L \ X` for some `X ⊆ P` (`X` empty where `L` is kept): `T' = T \ P ⊆ L \ P ⊆
/// L \ X = L'`, so `L' ⊇ T'` again. By induction `L ⊇ T` at every step. The cell (`super::cell`)
/// reads only the parts, every one of which is a part of the projection, so its values all have
/// points; it may get more parts than with the exact `left`, never a value without a point.
struct Held {
    left: Classed,
}

impl Held {
    /// Whether every value of the goal is held.
    fn done(&self) -> bool {
        self.left.is_empty()
    }

    /// `p` added to `out`, and its values taken from those left: a part with no holes as one
    /// range; a part with holes by its class, but only in the finite pieces of what is left
    /// within its ends, and only where the values left stay one class within ranges
    /// ([`Classed::minus_unlisted`]); else `left` is kept as it is, wider than the values not
    /// yet held, which the proof at [`Held`] allows. Each piece read and each piece taken is
    /// charged [`PIECE`].
    ///
    /// Complexity tradeoff (PERF-exact-strided-unlisted): naive version (before), a part with
    /// holes taken by [`Classed::minus`], which lists the values left where they are no one
    /// class (the range `[0, R]` less the even values of `[0, X]`: the odd values there and
    /// every value past `X`), and each value of the part charged [`LISTED`] and each value left
    /// [`PIECE`] (the counts of the values, [`Classed::count`] and [`Classed::listed_len`]), so
    /// the exact projection of a hub held to a class charged O(R) units and was refused near
    /// R = 10^5 (`l01_38_presburger::strided`). Used: O(p log p) for the p ranges of `left`
    /// and the part, charged [`PIECE`] for each range read and taken, and `left` kept where
    /// taking would list; the cost of keeping it is at most the splinters the exact `left`
    /// would have spared (a later [`Held::done`] that is false where it would be true).
    ///
    /// Complexity tradeoff: naive version, a part with holes taken from what is left by a set
    /// of its values, which has no end for a part with no end. Before
    /// PRES-interval-strided-piece: each finite piece of `left` within the part's ends read
    /// once, and each of the part's values in it listed and taken from `left` as a range of
    /// its own, O(v) for the v values of the goal, on each projection: the holes-cut and
    /// split-moved benchmarks of `l01_39_scope_relations::xst::s4::bench` project a stride
    /// over a goal of O(n) values O(n) times, O(n^2) (eu-stack samples, 2026-11-18: 11 of 19
    /// samples in `project_classes` were here). Used: `left` kept as ranges met with one class
    /// ([`Classed`]) and the part taken by its range and class ([`Classed::minus`]), O(p log p)
    /// for p ranges where the values left stay one class (every integer less the odd values,
    /// then less the even ones), and listed, O(v) as before, where they do not (until
    /// PERF-exact-strided-unlisted, above).
    fn push(&mut self, p: Strided, out: &mut Vec<Strided>, work: &mut Work) -> Result<(), Refusal> {
        let lo = p.lo.as_ref().map_or(End::NegInf, fin);
        let hi = p.hi.as_ref().map_or(End::PosInf, fin);
        let within = if let Some((l, u)) = self.left.ranges.bounds()
            && *l >= lo
            && *u <= hi
        {
            self.left.clone()
        } else {
            self.left.meet(&Classed::plain(IntervalSet::range(lo, hi)))
        };
        // Each range of `within` read once.
        let read = PIECE.saturating_mul((within.ranges.len() as u64).saturating_add(1));
        if p.step == Int::from(1) {
            work.charge(read)?;
            // `within` may be read in a finer class than `left` (`Classed::new` finds the
            // class of its values), so the difference may list too.
            if let Some(left) = self.left.minus_unlisted(&within) {
                self.left = left;
            }
        } else if !within.is_empty() {
            work.charge(read)?;
            // The finite pieces of `within`; a piece with no end is skipped (the goal is then
            // not held by this part alone). With a class other than every integer every piece
            // is finite already. Complexity tradeoff: naive version, always collect and rebuild
            // all pieces via `from_pieces`, O(p) allocations per push (`changes_of_one_block`);
            // used: reuse `within.ranges` in O(1) when its ends are already finite.
            let finite = if matches!(within.ranges.bounds(), Some((End::Fin(_), End::Fin(_)))) {
                within.ranges.clone()
            } else {
                IntervalSet::from_pieces(
                    (within.ranges.pieces())
                        .filter(|(l, u)| matches!((l, u), (End::Fin(_), End::Fin(_))))
                        .map(|(l, u)| (l.clone(), u.clone()))
                        .collect(),
                )
            };
            let class = Congruence::new(Num::from(&p.step), Num::from(&p.res));
            let taken = Classed::new(finite, within.class.meet(&class));
            // Each range taken charged [`PIECE`]; no value is listed.
            work.charge(PIECE.saturating_mul((taken.ranges.len() as u64).saturating_add(1)))?;
            if let Some(left) = self.left.minus_unlisted(&taken) {
                self.left = left;
            }
        }
        out.push(p);
        Ok(())
    }
}

/// A divisibility literal `d | lin`, `d >= 2`, of [`liaproj`].
struct Div {
    d: Int,
    lin: Lin,
}

/// The values of `s` of the one disjunct, chosen by the point `m` of the conjunction `rows`,
/// of the projection of `rows` onto `s`: the model-based projection for linear integer
/// arithmetic, `LIAProj`, of Komuravelli, Gurfinkel and Chaki ("SMT-based model checking for
/// recursive programs", CAV 2014, section "Model Based Projection for Linear Integer
/// Arithmetic", in the appendix of arXiv 1405.4028, read 2026-11-21 in its LaTeX source; the
/// definition, the paper's choice of disjunct and the departures below are in the crate's
/// References), which keeps of Cooper's quantifier elimination for each atom
/// the one disjunct that `m` satisfies. `m` satisfies `rows`; `rows` hold no product atom.
/// Every value of the answer has a point of `rows`, and `m`'s value of `s` is one of them.
///
/// Each atom `x` other than `s` is removed in turn:
/// - with an equation `a·x + t == 0` (the least `|a|` of all equations, so a unit coefficient
///   when there is one): `|a|·x` is replaced by `-sign(a)·t` in every literal scaled by `|a|`,
///   and `|a| | t` is added; this step is exact.
/// - else, with `L` the lcm of `x`'s coefficients, every literal is scaled so that `x` comes
///   as `±y`, `y = L·x`, and `L | y` is added; `D` is the lcm of `L` and the moduli of the
///   divisibility literals over `y`. With lower and upper bounds, `y` is replaced by
///   `l + i`, `l` the greatest lower bound at `m`, `i = (m(y) - m(l)) mod D` (Cooper's disjunct
///   `l + i` that holds `m`); with bounds on one side only, those bounds are dropped and `y`
///   is `m(y) mod D` in the divisibility literals (Cooper's infinite disjunct).
///
/// Left are bounds on `s` and literals `d | c·s + e`, each a residue class of `s` modulo
/// `d / gcd(d, c)`, which `m` satisfies: the answer is the bounds and one residue class
/// modulo the lcm of those.
///
/// Complexity tradeoff: naive version, the exact projection of the implicant ([`pugh`]):
/// every splinter of each dark shadow, exponential in the atoms removed (the repaired unit's
/// `x`, `exact::tests::every_name_of_the_repaired_unit_has_its_exact_answer`, past the whole
/// limit). Used: one disjunct per atom, each literal rewritten once, so O(n·r·t) operations on
/// integers for n atoms, r rows and t terms a row, the rows never more than at the start plus
/// one divisibility literal per atom. The integers grow: each step scales a literal by at
/// most `L` (or `|a|`), so a coefficient after n steps is at most the product of the
/// coefficients' lcms, and the step of the answer divides that product; each row is divided
/// by the gcd of its coefficients after each step, which keeps unit coefficients at 1. The
/// cost moves to the cover: one cell holds one disjunct, so the cover asks once for each
/// disjunct it needs, at most (choices of bound per atom) times (residues modulo the step).
pub(super) fn liaproj(
    rows: &[Con],
    s: &Atom,
    m: &Model,
    work: &mut Work,
) -> Result<Strided, Refusal> {
    let mut rows: Vec<Con> = rows.to_vec();
    let mut divs: Vec<Div> = Vec::new();
    loop {
        let size: u64 = (rows.iter().map(|k| &k.lin))
            .chain(divs.iter().map(|k| &k.lin))
            .map(|l| l.terms.len() as u64 + 1)
            .sum();
        work.read(size)?;
        normalized(&mut rows, &mut divs); // An equation over an atom other than `s`, the one of least coefficient.
        let eq = (rows.iter().enumerate())
            .filter(|(_, k)| k.rel == Rel::Eq)
            .flat_map(|(i, k)| {
                (k.lin.terms.iter())
                    .filter(|(a, _)| *a != s)
                    .map(move |(a, c)| (c.abs(), i, a))
            })
            .min_by(|p, q| p.0.cmp(&q.0))
            .map(|(k, i, a)| (k, i, a.clone()));
        if let Some((k, i, x)) = eq {
            let e = rows.swap_remove(i);
            let a = e.lin.terms[&x].clone();
            let mut t = e.lin;
            t.terms.remove(&x);
            // `a·x + t == 0`: `k·x == -sign(a)·t`, `k = |a|`, and `k | t`.
            let kx = if a.is_negative() {
                t.clone()
            } else {
                t.times(-1)
            };
            let put = |l: &Lin| {
                let mut l = l.clone();
                let b = l.terms.remove(&x).expect("a literal over x");
                let mut l = l.times(k.clone());
                l.plus_assign(&kx.times(b));
                l
            };
            for r in rows.iter_mut().filter(|r| r.lin.terms.contains_key(&x)) {
                r.lin = put(&r.lin);
            }
            for v in divs.iter_mut().filter(|v| v.lin.terms.contains_key(&x)) {
                v.lin = put(&v.lin);
                v.d = &v.d * &k;
            }
            if k > Int::ONE {
                divs.push(Div { d: k, lin: t });
            }
            continue;
        }
        let Some(x) = (rows.iter().map(|k| &k.lin))
            .chain(divs.iter().map(|k| &k.lin))
            .flat_map(|l| l.terms.keys())
            .filter(|a| *a != s)
            .min()
            .cloned()
        else {
            break;
        };
        if !divs.iter().any(|v| v.lin.terms.contains_key(&x)) {
            rows = dark(rows, &x, m);
            continue;
        }
        let coef = |l: &Lin| l.terms.get(&x).cloned();
        let big_l = (rows.iter().map(|k| &k.lin))
            .chain(divs.iter().map(|k| &k.lin))
            .filter_map(coef)
            .fold(Int::ONE, |l, c| l.lcm(&c.abs()));
        let y_at = &big_l * &value(&Lin::atom(x.clone()), m);
        // A literal `c·x + r` scaled by `L / |c|`: `sign(c)·y + rest`, the sign and the rest.
        let scaled = |l: &Lin, c: &Int| {
            let mut r = l.clone();
            r.terms.remove(&x);
            (c.is_positive(), r.times(big_l.div_floor(&c.abs())))
        };
        let (with, without): (Vec<Con>, Vec<Con>) =
            (rows.into_iter()).partition(|k| k.lin.terms.contains_key(&x));
        let mut big_d = big_l.clone();
        let mut over_y = Vec::new();
        let mut others = Vec::new();
        for v in divs {
            if let Some(c) = coef(&v.lin) {
                let d = &v.d * &big_l.div_floor(&c.abs());
                big_d = big_d.lcm(&d);
                over_y.push((d, scaled(&v.lin, &c)));
            } else {
                others.push(v);
            }
        }
        let ge: Vec<(bool, Lin)> = (with.iter())
            .map(|k| {
                debug_assert_eq!(k.rel, Rel::Ge, "an equation over x is removed first");
                scaled(&k.lin, &coef(&k.lin).expect("a row over x"))
            })
            .collect();
        let (has_lo, has_hi) = (ge.iter().any(|g| g.0), ge.iter().any(|g| !g.0));
        // `y + rest >= 0` is the lower bound `y >= -rest`: the greatest at `m` has the least
        // `m(rest)`.
        let term = if has_lo && has_hi {
            let rest = (ge.iter().filter(|g| g.0))
                .map(|g| &g.1)
                .min_by(|p, q| value(p, m).cmp(&value(q, m)))
                .expect("a lower bound");
            let l = rest.times(-1);
            let i = (&y_at - &value(&l, m)).mod_floor(&big_d);
            l.plus(&Lin::constant(i))
        } else {
            Lin::constant(y_at.mod_floor(&big_d))
        };
        let at = |(pos, rest): &(bool, Lin)| term.times(if *pos { 1 } else { -1 }).plus(rest);
        rows = without;
        if has_lo && has_hi {
            rows.extend(ge.iter().map(|g| Con {
                lin: at(g),
                rel: Rel::Ge,
            }));
        }
        divs = others;
        divs.extend(over_y.iter().map(|(d, g)| Div {
            d: d.clone(),
            lin: at(g),
        }));
        divs.push(Div {
            d: big_l,
            lin: term,
        });
    }
    let v = value(&Lin::atom(s.clone()), m);
    let step = (divs.iter()).fold(Int::ONE, |step, k| {
        let c = k.lin.terms.get(s).expect("a literal over s alone");
        step.lcm(&k.d.div_floor(&k.d.gcd(c)))
    });
    let set = bounded(&rows, s);
    debug_assert!(
        set.contains_end(&fin(&v)),
        "the point is not one of its rows"
    );
    let end = |e: &End| match e {
        End::Fin(n) => Some(Int::from(n)),
        _ => None,
    };
    let (lo, hi) = set.pieces().next().expect("the point's value");
    Ok(Strided {
        lo: end(lo),
        hi: end(hi),
        res: v.mod_floor(&step),
        step,
    })
}

/// The rows of [`liaproj`] read as bounds on `x`: `out` the rows without `x`, `lower` and
/// `upper` the bounds `c·x + t >= 0` as `(|c|, t)`, and where there are both, the pair of
/// [`dark`].
struct Shadow {
    out: Vec<Con>,
    lower: Vec<(Int, Lin)>,
    upper: Vec<(Int, Lin)>,
    pair: Option<Pair>,
}

/// The greatest lower bound `lower[i]` and the least upper bound `upper[j]` at the point,
/// the slack `(a - 1)·(b - 1)` of their dark shadow, and whether the point lies in it.
struct Pair {
    i: usize,
    j: usize,
    slack: Int,
    inside: bool,
}

fn shadow(rows: &[Con], x: &Atom, m: &Model) -> Shadow {
    let mut out = Vec::new();
    let mut lower: Vec<(Int, Lin)> = Vec::new();
    let mut upper: Vec<(Int, Lin)> = Vec::new();
    for k in rows {
        let Some(c) = k.lin.terms.get(x) else {
            out.push(k.clone());
            continue;
        };
        debug_assert_eq!(k.rel, Rel::Ge, "an equation over x is removed first");
        let mut t = k.lin.clone();
        t.terms.remove(x);
        if c.is_positive() {
            lower.push((c.clone(), t));
        } else {
            upper.push((c.abs(), t));
        }
    }
    if lower.is_empty() || upper.is_empty() {
        return Shadow {
            out,
            lower,
            upper,
            pair: None,
        };
    }
    // A lower bound `a·x >= -t` is `x >= -t/a`: the greatest at `m` has the least `t/a`;
    // an upper bound `b·x <= t` is `x <= t/b`: the least has the least `t/b`. Compared as
    // `t_1·a_2 < t_2·a_1`, the first of equal ones kept.
    let least = |bounds: &[(Int, Lin)]| {
        let at: Vec<Int> = bounds.iter().map(|(_, t)| value(t, m)).collect();
        (0..bounds.len())
            .min_by(|&i, &j| (&at[i] * &bounds[j].0).cmp(&(&at[j] * &bounds[i].0)))
            .expect("a bound")
    };
    let (i, j) = (least(&lower), least(&upper));
    let (a, tl) = &lower[i];
    let (b, tu) = &upper[j];
    let slack = &(a - &Int::ONE) * &(b - &Int::ONE);
    // `a·β - b·α - (a - 1)·(b - 1)` at `m`, with `α = -tl`, `β = tu`.
    let gap = &(&(&value(tu, m) * a) + &(&value(tl, m) * b)) - &slack;
    Shadow {
        pair: Some(Pair {
            i,
            j,
            slack,
            inside: !gap.is_negative(),
        }),
        out,
        lower,
        upper,
    }
}

/// `rows` without `x`, which no divisibility literal holds and no equation of `rows` holds,
/// where `m` lies in the dark shadow of the greatest lower bound `a·x >= α` and the least
/// upper bound `b·x <= β` of `x` at `m` (Pugh, "The Omega test", 1991, "dark shadow"):
/// the rows without `x`, each other lower bound at most `α/a` (`a·α_j <= a_j·α`), each other
/// upper bound at least `β/b`, and `a·β - b·α >= (a - 1)·(b - 1)`, which leaves an integer
/// `x` between `α/a` and `β/b` and so above every lower bound and below every upper bound.
/// With bounds on one side only, the rows without `x`, since some `x` then holds every row.
/// Where `m` is in a splinter, outside that dark shadow, `rows` and the equation of the
/// splinter that holds `m`, `a·x == α + i` with `i = a·m(x) - m(α)` (Pugh's splinters,
/// `0 <= i < a` there, since `a·β - b·α < (a - 1)·(b - 1)` and `α <= a·m(x) <= a·β/b`),
/// for the step of an equation to remove `x`.
fn dark(rows: Vec<Con>, x: &Atom, m: &Model) -> Vec<Con> {
    let Shadow {
        mut out,
        lower,
        upper,
        pair,
    } = shadow(&rows, x, m);
    let Some(Pair {
        i,
        j,
        slack,
        inside,
    }) = pair
    else {
        return out;
    };
    let (a, tl) = &lower[i];
    let (b, tu) = &upper[j];
    if !inside {
        let mut lin = Lin::atom(x.clone()).times(a.clone()).plus(tl);
        lin.constant = &lin.constant - &value(&lin, m);
        let mut rows = rows;
        rows.push(Con { lin, rel: Rel::Eq });
        return rows;
    }
    // `a·β - b·α >= (a - 1)·(b - 1)` with `α = -tl`, `β = tu`.
    let pair = tu.times(a.clone()).plus(&tl.times(b.clone()));
    let pair = pair.plus(&Lin::constant(-&slack));
    out.push(Con {
        lin: pair,
        rel: Rel::Ge,
    });
    // Another lower bound `-t_k/a_k <= -tl/a`: `a·t_k - a_k·tl >= 0`; another upper bound
    // `t_k/b_k >= tu/b`: `b·t_k - b_k·tu >= 0`.
    for (_, (c, t)) in lower.iter().enumerate().filter(|&(k, _)| k != i) {
        out.push(Con {
            lin: t.times(a.clone()).minus(&tl.times(c.clone())),
            rel: Rel::Ge,
        });
    }
    for (_, (c, t)) in upper.iter().enumerate().filter(|&(k, _)| k != j) {
        out.push(Con {
            lin: t.times(b.clone()).minus(&tu.times(c.clone())),
            rel: Rel::Ge,
        });
    }
    out
}

/// `rows` and `divs` of [`liaproj`] with each literal divided by the gcd of its coefficients
/// (an inequality's constant rounded down, a divisibility literal's modulus and constant
/// divided too, its coefficients first taken modulo its modulus), and literals with no atom,
/// which hold at the point, dropped.
fn normalized(rows: &mut Vec<Con>, divs: &mut Vec<Div>) {
    rows.retain_mut(|k| {
        let g = (k.lin.terms.values()).fold(Int::ZERO, |g, c| g.gcd(c));
        if g.is_zero() {
            debug_assert!(holds_at(k, &k.lin.constant), "a row the point fails");
            return false;
        }
        if g > Int::ONE {
            debug_assert!(k.rel == Rel::Ge || k.lin.constant.mod_floor(&g).is_zero());
            for c in k.lin.terms.values_mut() {
                *c = c.div_floor(&g);
            }
            k.lin.constant = k.lin.constant.div_floor(&g);
        }
        true
    });
    divs.retain_mut(|v| {
        let d = v.d.clone();
        for c in v.lin.terms.values_mut() {
            *c = c.mod_floor(&d);
        }
        v.lin.terms.retain(|_, c| !c.is_zero());
        v.lin.constant = v.lin.constant.mod_floor(&d);
        let g = (v.lin.terms.values())
            .chain([&v.lin.constant])
            .fold(d.clone(), |g, c| g.gcd(c));
        if g > Int::ONE {
            for c in v.lin.terms.values_mut() {
                *c = c.div_floor(&g);
            }
            v.lin.constant = v.lin.constant.div_floor(&g);
            v.d = v.d.div_floor(&g);
        }
        if v.lin.terms.is_empty() {
            debug_assert!(v.lin.constant.is_zero(), "a divisibility the point fails");
            return false;
        }
        v.d > Int::ONE
    });
}

/// `rows` with `x` replaced by `e`.
fn substituted(rows: Vec<Con>, x: &Atom, e: &Lin) -> Vec<Con> {
    rows.into_iter()
        .map(|mut k| {
            if let Some(c) = k.lin.terms.remove(x) {
                k.lin.plus_assign(&e.times(c));
            }
            k
        })
        .collect()
}

/// `rows` divided by the gcd of each row's coefficients (an inequality's constant rounded
/// down, an equality whose constant the gcd does not divide has no point), rows with no
/// atom checked and dropped, and inequalities over the same terms kept once at their
/// tightest; a pair `t + c >= 0`, `-t + d >= 0` with `c + d < 0` has no point and with
/// `c + d == 0` is the equality `t + c == 0`. `None` where the rows have no point.
fn tidied(rows: Vec<Con>) -> Option<Vec<Con>> {
    let mut eqs: BTreeMap<BTreeMap<Atom, Int>, Int> = BTreeMap::new();
    let mut ges: BTreeMap<BTreeMap<Atom, Int>, Int> = BTreeMap::new();
    for k in rows {
        let Lin { terms, constant } = k.lin;
        if terms.is_empty() {
            let ok = match k.rel {
                Rel::Ge => !constant.is_negative(),
                Rel::Eq => constant.is_zero(),
            };
            if !ok {
                return None;
            }
            continue;
        }
        let g = terms.values().fold(Int::from(0), |g, c| g.gcd(c));
        let (terms, constant) = if g == Int::from(1) {
            (terms, constant)
        } else {
            if k.rel == Rel::Eq && !constant.mod_floor(&g).is_zero() {
                return None;
            }
            let terms = terms
                .into_iter()
                .map(|(a, c)| (a, c.div_floor(&g)))
                .collect();
            (terms, constant.div_floor(&g))
        };
        match k.rel {
            Rel::Eq => {
                // `t + c == 0` and `-t - c == 0` are one row: keep the one whose first
                // coefficient is above zero.
                let flip = terms.values().next().is_some_and(Int::is_negative);
                let (terms, constant) = if flip {
                    (
                        terms.into_iter().map(|(a, c)| (a, -&c)).collect(),
                        -&constant,
                    )
                } else {
                    (terms, constant)
                };
                match eqs.get(&terms) {
                    Some(c) if c != &constant => return None,
                    _ => {
                        eqs.insert(terms, constant);
                    }
                }
            }
            Rel::Ge => {
                let e = ges.entry(terms).or_insert_with(|| constant.clone());
                if constant < *e {
                    *e = constant;
                }
            }
        }
    }
    let mut out: Vec<Con> = Vec::with_capacity(eqs.len() + ges.len());
    let mut paired: BTreeSet<BTreeMap<Atom, Int>> = BTreeSet::new();
    for (terms, c) in &ges {
        if paired.contains(terms) {
            continue;
        }
        let neg: BTreeMap<Atom, Int> = terms.iter().map(|(a, k)| (a.clone(), -k)).collect();
        if let Some(d) = ges.get(&neg) {
            let sum = c + d;
            if sum.is_negative() {
                return None;
            }
            if sum.is_zero() {
                paired.insert(terms.clone());
                paired.insert(neg);
                out.push(Con {
                    lin: Lin {
                        terms: terms.clone(),
                        constant: c.clone(),
                    },
                    rel: Rel::Eq,
                });
                continue;
            }
        }
        out.push(Con {
            lin: Lin {
                terms: terms.clone(),
                constant: c.clone(),
            },
            rel: Rel::Ge,
        });
    }
    for (terms, c) in eqs {
        out.push(Con {
            lin: Lin { terms, constant: c },
            rel: Rel::Eq,
        });
    }
    Some(out)
}

/// The values `at·t + from` of `s` at the points of `rows`, `t` standing for `s` (`at` zero
/// once `t` is fixed), added to `out`; nothing more once `held` is done ([`pugh`]).
#[allow(clippy::too_many_arguments)]
fn project(
    rows: Vec<Con>,
    t: &Atom,
    at: &mut Int,
    from: &mut Int,
    work: &mut Work,
    fresh: &mut u32,
    held: &mut Held,
    out: &mut Vec<Strided>,
) -> Result<(), Refusal> {
    if held.done() {
        return Ok(());
    }
    let size: u64 = rows.iter().map(|k| k.lin.terms.len() as u64 + 1).sum();
    work.read(size)?;
    project_read(rows, t, at, from, work, fresh, held, out)
}

/// [`project`] of `rows` already charged to `work` (each row its terms and one more), with
/// `held` not yet done.
#[allow(clippy::too_many_arguments)]
fn project_read(
    rows: Vec<Con>,
    t: &Atom,
    at: &mut Int,
    from: &mut Int,
    work: &mut Work,
    fresh: &mut u32,
    held: &mut Held,
    out: &mut Vec<Strided>,
) -> Result<(), Refusal> {
    let Some(mut rows) = tidied(rows) else {
        return Ok(());
    };
    // An equality with an atom other than `t`.
    if let Some(i) = (0..rows.len())
        .find(|&i| rows[i].rel == Rel::Eq && rows[i].lin.terms.keys().any(|a| a != t))
    {
        let e = rows[i].lin.clone();
        let unit = (e.terms.iter()).find(|(a, c)| *a != t && c.abs() == Int::from(1));
        if let Some((x, c)) = unit {
            // `c·x + r == 0`, `c = ±1`: `x = -c·r`.
            let (x, c) = (x.clone(), c.clone());
            let mut r = e.clone();
            r.terms.remove(&x);
            rows.swap_remove(i);
            let rows = substituted(rows, &x, &r.times(-&c));
            return project(rows, t, at, from, work, fresh, held, out);
        }
        let g = (e.terms.iter())
            .filter(|(a, _)| *a != t)
            .fold(Int::from(0), |g, (_, c)| g.gcd(c));
        if g > Int::from(1) {
            // `a·t + c == 0 mod g`: with `d = gcd(a, g)`, `t == r mod g/d` (the protected
            // variable's step of Pugh's projection, "Projection", which adds `g·σ == ...`).
            let a = e.terms.get(t).cloned().unwrap_or_else(|| Int::from(0));
            let c = e.constant.clone();
            let d = a.gcd(&g);
            if !c.mod_floor(&d).is_zero() {
                return Ok(());
            }
            let m = g.div_floor(&d);
            let (a1, c1) = (a.div_floor(&d), c.div_floor(&d));
            // `a1·r == -c1 mod m`, `a1` and `m` coprime.
            let r = if m == Int::from(1) {
                Int::from(0)
            } else {
                let (_, inv, _) = a1.mod_floor(&m).bezout(&m);
                (&(-&c1) * &inv).mod_floor(&m)
            };
            // `t := m·t + r`.
            let e_t = Lin {
                terms: [(t.clone(), m.clone())].into_iter().collect(),
                constant: r.clone(),
            };
            let rows = substituted(rows, t, &e_t);
            let (at0, from0) = (at.clone(), from.clone());
            *from = &(&*at * &r) + &*from;
            *at = &*at * &m;
            let done = project(rows, t, at, from, work, fresh, held, out);
            (*at, *from) = (at0, from0);
            return done;
        }
        // Pugh's `mod^` step on the atom with the least coefficient other than `t`.
        let (k, ak) = (e.terms.iter())
            .filter(|(a, _)| *a != t)
            .min_by(|x, y| x.1.abs().cmp(&y.1.abs()).then_with(|| x.0.cmp(y.0)))
            .map(|(a, c)| (a.clone(), c.clone()))
            .expect("an atom other than t");
        let m = &ak.abs() + &Int::from(1);
        *fresh += 1;
        let sigma = Atom::Sym(format!("#pugh{fresh}").into());
        let sign = if ak.is_negative() {
            Int::from(-1)
        } else {
            Int::from(1)
        };
        // `x_k = -sign(a_k)·m·σ + Σ_{i != k} sign(a_k)·(a_i mod^ m)·x_i + sign(a_k)·(c mod^ m)`.
        // `mod^` is `Int::mod_hat`, odd at the tie where Pugh's `a - m·floor(a/m + 1/2)`, in
        // `[-m/2, m/2)`, is not; the step needs only `r == a (mod m)`, `|r| <= m/2`, and
        // `a_k mod^ m == -sign(a_k)`, which holds for `|a_k| == m - 1 >= 2` (a unit `a_k` was
        // substituted above), not a tie.
        let mut ek = Lin {
            terms: [(sigma, &(-&sign) * &m)].into_iter().collect(),
            constant: &sign * &e.constant.mod_hat(&m),
        };
        for (a, c) in &e.terms {
            if *a != k {
                let v = &sign * &c.mod_hat(&m);
                if !v.is_zero() {
                    ek.terms.insert(a.clone(), v);
                }
            }
        }
        let rows = substituted(rows, &k, &ek);
        return project(rows, t, at, from, work, fresh, held, out);
    }
    // An equality over `t` alone: `t` fixed, kept where the rest has a point.
    if let Some(i) = (0..rows.len()).find(|&i| rows[i].rel == Rel::Eq) {
        let e = rows[i].lin.clone();
        let a = e.terms.get(t).cloned().expect("t");
        if !e.constant.mod_floor(&a).is_zero() {
            return Ok(());
        }
        let v = -&e.constant.div_floor(&a);
        rows.swap_remove(i);
        let rows = substituted(rows, t, &Lin::constant(v.clone()));
        let (at0, from0) = (at.clone(), from.clone());
        *from = &(&*at * &v) + &*from;
        *at = Int::from(0);
        let done = project(rows, t, at, from, work, fresh, held, out);
        (*at, *from) = (at0, from0);
        return done;
    }
    // Inequalities only. The atoms other than `t`, each with its lower and upper rows.
    let mut sides: BTreeMap<Atom, (Vec<usize>, Vec<usize>)> = BTreeMap::new();
    for (i, k) in rows.iter().enumerate() {
        for (a, c) in &k.lin.terms {
            if a == t {
                continue;
            }
            let e = sides.entry(a.clone()).or_default();
            if c.is_positive() {
                e.0.push(i)
            } else {
                e.1.push(i)
            }
        }
    }
    if sides.is_empty() {
        let set = bounded(&rows, t);
        let Some((lo, hi)) = set.bounds() else {
            return Ok(());
        };
        if at.is_zero() {
            let p = Strided {
                lo: Some(from.clone()),
                hi: Some(from.clone()),
                step: Int::from(1),
                res: Int::from(0),
            };
            held.push(p, out, work)?;
            return Ok(());
        }
        let map = |e: &End| match e {
            End::Fin(n) => Some(&(&*at * &Int::from(n)) + &*from),
            _ => None,
        };
        let p = Strided {
            lo: map(lo),
            hi: map(hi),
            step: at.clone(),
            res: from.mod_floor(at),
        };
        held.push(p, out, work)?;
        return Ok(());
    }
    // An atom bounded on one side only: its rows dropped, exactly.
    if let Some((x, _)) = sides
        .iter()
        .find(|(_, (l, u))| l.is_empty() || u.is_empty())
    {
        let x = x.clone();
        let rows = rows
            .into_iter()
            .filter(|k| !k.lin.terms.contains_key(&x))
            .collect();
        return project(rows, t, at, from, work, fresh, held, out);
    }
    // The atom to remove: one whose elimination is exact, with the fewest new rows; else the
    // one with the fewest splinters, then the fewest new rows.
    let coef = |i: usize, x: &Atom| rows[i].lin.terms[x].abs();
    let splinters = |x: &Atom, l: &[usize], u: &[usize]| -> Int {
        let amax = u.iter().map(|&i| coef(i, x)).max().expect("upper");
        let mut n = Int::from(0);
        for &i in l {
            let b = coef(i, x);
            let top = (&(&(&amax * &b) - &amax) - &b).div_floor(&amax);
            if !top.is_negative() {
                n = &n + &(&top + &Int::from(1));
            }
        }
        n
    };
    let exact = |x: &Atom, l: &[usize], u: &[usize]| {
        l.iter().all(|&i| coef(i, x) == Int::from(1))
            || u.iter().all(|&i| coef(i, x) == Int::from(1))
    };
    let (x, (lower, upper)) = sides
        .iter()
        .min_by(|(x, (l, u)), (y, (m, v))| {
            let (ex, ey) = (exact(x, l, u), exact(y, m, v));
            ey.cmp(&ex)
                .then_with(|| {
                    if ex {
                        Int::from(0).cmp(&Int::from(0))
                    } else {
                        splinters(x, l, u).cmp(&splinters(y, m, v))
                    }
                })
                .then_with(|| (l.len() * u.len()).cmp(&(m.len() * v.len())))
                .then_with(|| x.cmp(y))
        })
        .map(|(x, lu)| (x.clone(), lu.clone()))
        .expect("an atom");
    let is_exact = exact(&x, &lower, &upper);
    let others: Vec<Con> = (rows.iter())
        .filter(|k| !k.lin.terms.contains_key(&x))
        .cloned()
        .collect();
    // For each lower `b·x + l >= 0` and upper `-a·x + u >= 0`: `a·(b·x + l) + b·(-a·x + u) =
    // a·l + b·u >= 0`, the real shadow, and `>= (a-1)(b-1)`, the dark one.
    // Each row of the shadow is charged as it is made, its terms and one more, which is what the
    // call below would read of it, and that call does not read it again (`project_read`): `held`
    // is not done there, as nothing above changed it since this call found it not done.
    // Proof that a shadow not refused is charged exactly what `project(shadow, ..)` charged
    // before ac390b499 (TEST-shadow-charge-totals):
    // 1. `held` is not done here. `project_read` is entered only from `project`, after
    //    `held.done()` was false, or from the call below, with `held` as at this point. Within
    //    one call nothing before this point changes `held`: only `Held::push` does, and it is
    //    called only where no atom other than `t` is left, a branch that returns. By induction
    //    on the depth of the calls, `held` is not done at every entry and here. So the old
    //    `project(shadow, ..)` passed its `held.done()` test and charged `work.read(s)` for
    //    `s` the size of `shadow`, its rows' terms and one more each, before the same
    //    `project_read`.
    // 2. That `s` is `others_size` plus each made row's `terms + 1`, the reads below, as
    //    `shadow` is `others` and then those rows.
    // 3. `work.read(r)` is `charge(r * 100)` and `charge` adds with saturation, so reads of
    //    `r1, .., rk` leave `used` and `EXACT_WORK` at `min(old + 100·Σ ri, u64::MAX)`, as one
    //    read of `Σ ri` does (each partial product or sum that saturates makes both the
    //    maximum). They refuse iff some partial total passes the limit, which, the totals
    //    rising, holds iff the last does: the same refusal, which the row-by-row reads give
    //    within one row of the limit.
    debug_assert!(
        !held.done(),
        "a shadow is made only for a goal not yet held"
    );
    // Complexity tradeoff: before, the shadow was made whole and then read by the call below,
    // so its |lower|·|upper| rows were built uncharged before the limit was checked: on the
    // windows of `l01_38_presburger::exp_families` at seed 1096302828291 one shadow held
    // 6,425,279 terms, 207 times the limit of 3,100,000 units, and took about 8 s to build
    // before its read refused it, twice in one cover, 16 to 21 s against the 250 ms the limit
    // stands for (FAIL-window-seed-13014466797380974686). Used: the same charges, made row by
    // row, so the same projections are answered with the same work, and a refused one stops
    // within one row of the limit; O(1) more a row.
    let others_size: u64 = others.iter().map(|k| k.lin.terms.len() as u64 + 1).sum();
    work.read(others_size)?;
    let mut shadow = others.clone();
    for &i in &lower {
        for &j in &upper {
            let (b, a) = (coef(i, &x), coef(j, &x));
            let mut lin = rows[i].lin.times(a.clone());
            lin.plus_assign(&rows[j].lin.times(b.clone()));
            debug_assert!(!lin.terms.contains_key(&x));
            if !is_exact {
                lin.constant = &lin.constant - &(&(&a - &Int::from(1)) * &(&b - &Int::from(1)));
            }
            work.read(lin.terms.len() as u64 + 1)?;
            shadow.push(Con { lin, rel: Rel::Ge });
        }
    }
    project_read(shadow, t, at, from, work, fresh, held, out)?;
    if is_exact {
        return Ok(());
    }
    // The splinters: for each lower `b·x >= β` and `a` the largest upper coefficient, the
    // rows with `b·x == β + i` for `0 <= i <= (a·b - a - b)/a`. The loop stops once `held` is
    // done: a splinter made after that returns at once without charging `work`, so with a
    // coefficient near `2^62` the loop ran about `b` uncharged clones of `rows` and neither
    // ended nor refused (s22 `remainder_reads_outside_a_split_at_their_corners_on_a_longer_chain`,
    // 2026-11-18).
    let amax = upper.iter().map(|&i| coef(i, &x)).max().expect("upper");
    for &i in &lower {
        let b = coef(i, &x);
        let top = (&(&(&amax * &b) - &amax) - &b).div_floor(&amax);
        let mut k = Int::from(0);
        while k <= top && !held.done() {
            let mut one = rows.clone();
            let mut lin = rows[i].lin.clone();
            lin.constant = &lin.constant - &k;
            one.push(Con { lin, rel: Rel::Eq });
            project(one, t, at, from, work, fresh, held, out)?;
            k = &k + &Int::from(1);
        }
    }
    Ok(())
}

/// A piece of values with no end, with holes: the values of `piece` whose residue modulo
/// `step` is marked in `have`.
pub(super) struct Tail {
    pub(super) piece: IntervalSet,
    pub(super) step: Int,
    pub(super) have: Vec<bool>,
}

/// The union of `parts` as a set of ranges, the values of each finite piece with holes
/// listed one by one, each charged to `work`, and each residue table of the lcm of the
/// steps charged its size; with it, each piece with holes and no end that the parts with
/// no holes do not fill, which ranges cannot hold ([`Tail`]).
pub(super) fn ranges(
    parts: &[Strided],
    work: &mut Work,
) -> Result<(IntervalSet, Vec<Tail>), Refusal> {
    let (set, _, tails) = ranges_in(parts, false, work)?;
    Ok((set, tails))
}

/// [`ranges`] with the values of a finite piece with holes kept as classes where that makes
/// no more sets than listing them ([`classes_in`]), so that no value is listed there.
pub(super) fn ranges_classed(
    parts: &[Strided],
    work: &mut Work,
) -> Result<(ClassUnion, Vec<Tail>), Refusal> {
    let (set, classes, tails) = ranges_in(parts, true, work)?;
    Ok((ClassUnion::plain(set).join(&classes), tails))
}

/// [`ranges`], with the classes of [`classes_in`] apart where `keep`, else none.
fn ranges_in(
    parts: &[Strided],
    keep: bool,
    work: &mut Work,
) -> Result<(IntervalSet, ClassUnion, Vec<Tail>), Refusal> {
    let end_lo = |p: &Strided| p.lo.as_ref().map_or(End::NegInf, fin);
    let end_hi = |p: &Strided| p.hi.as_ref().map_or(End::PosInf, fin);
    let plain = IntervalSet::from_pieces(
        (parts.iter())
            .filter(|p| p.step == Int::from(1))
            .map(|p| (end_lo(p), end_hi(p)))
            .collect(),
    );
    let holed: Vec<&Strided> = parts.iter().filter(|p| p.step > Int::from(1)).collect();
    if holed.is_empty() {
        return Ok((plain, ClassUnion::empty(), Vec::new()));
    }
    let mut classes = ClassUnion::empty();
    // The line cut at every finite end of a holed part: in each segment the same parts hold.
    let mut cuts: BTreeSet<Int> = BTreeSet::new();
    for p in &holed {
        if let Some(l) = &p.lo {
            cuts.insert(l.clone());
        }
        if let Some(h) = &p.hi {
            cuts.insert(h + &Int::from(1));
        }
    }
    let cuts: Vec<Int> = cuts.into_iter().collect();
    let mut segments: Vec<(Option<Int>, Option<Int>)> = Vec::with_capacity(cuts.len() + 1);
    if let (Some(first), Some(last)) = (cuts.first(), cuts.last()) {
        segments.push((None, Some(first - &Int::from(1))));
        for w in cuts.windows(2) {
            segments.push((Some(w[0].clone()), Some(&w[1] - &Int::from(1))));
        }
        segments.push((Some(last.clone()), None));
    } else {
        segments.push((None, None));
    }
    let mut pieces: Vec<(End, End)> = plain.pieces().cloned().collect();
    let mut tails = Vec::new();
    for (lo, hi) in segments {
        work.charge(holed.len() as u64)?;
        let seg = IntervalSet::range(
            lo.as_ref().map_or(End::NegInf, fin),
            hi.as_ref().map_or(End::PosInf, fin),
        );
        let inside = |p: &&&Strided| {
            p.lo.as_ref()
                .is_none_or(|l| lo.as_ref().is_some_and(|v| v >= l))
                && p.hi
                    .as_ref()
                    .is_none_or(|h| hi.as_ref().is_some_and(|v| v <= h))
        };
        let active: Vec<&&Strided> = holed.iter().filter(inside).collect();
        if active.is_empty() {
            continue;
        }
        let rest = seg.minus(&plain);
        if rest.is_empty() {
            continue;
        }
        let lcm = active.iter().fold(Int::from(1), |l, p| {
            let g = l.gcd(&p.step);
            &l.div_floor(&g) * &p.step
        });
        let n = lcm
            .to_i128()
            .and_then(|n| u64::try_from(n).ok())
            .unwrap_or(u64::MAX);
        // The table is filled and read a byte at a time, about a hundredth of a unit each
        // (a unit is about 100 ns, `EXACT_LIMIT`): one unit for each 64 residues.
        work.charge(n / 64 + 1)?;
        let mut have = vec![false; n as usize];
        for p in &active {
            let step = p.step.to_i128().expect("charged") as usize;
            let mut r = p.res.to_i128().expect("charged") as usize;
            while r < n as usize {
                have[r] = true;
                r += step;
            }
        }
        if have.iter().all(|&b| b) {
            pieces.extend(rest.pieces().cloned());
            continue;
        }
        for (l, u) in rest.pieces() {
            let (End::Fin(l), End::Fin(u)) = (l, u) else {
                tails.push(Tail {
                    piece: IntervalSet::range(l.clone(), u.clone()),
                    step: lcm.clone(),
                    have: have.clone(),
                });
                continue;
            };
            let (l, u) = (Int::from(l), Int::from(u));
            if keep {
                classes_in(&l, &u, &lcm, &have, work, &mut classes, &mut pieces)?;
            } else {
                listed(&l, &u, &lcm, &have, work, &mut pieces)?;
            }
        }
    }
    Ok((IntervalSet::from_pieces(pieces), classes, tails))
}

/// The values from `l` to `u` whose residue modulo `step` is marked in `have`: one class
/// `r mod step` for each residue `r` marked, met with `[l, u]`, added to `classes`, each
/// charged [`PIECE`], where that makes no more sets than listing; else listed ([`listed`]).
///
/// The choice: with `k` residues marked in `c` cyclic runs (`c >= 1`, as `have` is neither
/// all marked nor none here: `ranges_in` lists every value where all are), the span of
/// `n = u - l + 1` values holds `floor(n/step)` whole periods, each of which lists as at least
/// `c` ranges (a run of marked residues inside a period is one range at most, and two runs
/// are apart by an unmarked residue, so never one range), so listing makes at least
/// `c·floor(n/step)` ranges. Classes are taken where `k` is at most that bound, so they never
/// make more sets than listing. Both are exact, so only the cost changes; the choice compares
/// the two counts, with no constant chosen.
// Complexity tradeoff: naive version (before PERF-exact-strided-unlisted), every value
// listed, O(n·k/step) for k residues marked; used: O(step) to read the table and O(k) classes,
// O(k log k) to join them, whatever n.
#[allow(clippy::too_many_arguments)]
fn classes_in(
    l: &Int,
    u: &Int,
    step: &Int,
    have: &[bool],
    work: &mut Work,
    classes: &mut ClassUnion,
    pieces: &mut Vec<(End, End)>,
) -> Result<(), Refusal> {
    // The table read once, one unit for each 64 residues, as `listed` reads it.
    work.charge(have.len() as u64 / 64 + 1)?;
    let k = have.iter().filter(|&&b| b).count();
    let runs = (0..have.len())
        .filter(|&r| have[r] && !have[(r + have.len() - 1) % have.len()])
        .count();
    let periods = (&(u - l) + &Int::from(1)).div_floor(step);
    if Int::from(k) > &Int::from(runs) * &periods {
        return listed(l, u, step, have, work, pieces);
    }
    let span = IntervalSet::range(fin(l), fin(u));
    for (r, _) in have.iter().enumerate().filter(|(_, b)| **b) {
        work.charge(PIECE)?;
        let class = Congruence::new(Num::from(step), Num::from(&Int::from(r as i64)));
        classes.add(Classed::new(span.clone(), class));
    }
    Ok(())
}

/// The values from `l` to `u` whose residue modulo `step` is marked in `have`, added to
/// `pieces`, each charged [`LISTED`] units of `work`, and the table one unit for each 64 residues.
pub(super) fn listed(
    l: &Int,
    u: &Int,
    step: &Int,
    have: &[bool],
    work: &mut Work,
    pieces: &mut Vec<(End, End)>,
) -> Result<(), Refusal> {
    // The table read once, one unit for each 64 residues, as where it is made.
    work.charge(have.len() as u64 / 64 + 1)?;
    for (r, _) in have.iter().enumerate().filter(|(_, b)| **b) {
        let r = Int::from(r as i64);
        // The first value at or above `l` with residue `r`.
        let mut v = l + &(&r - l).mod_floor(step);
        while &v <= u {
            work.charge(LISTED)?;
            pieces.push((fin(&v), fin(&v)));
            v = &v + step;
        }
    }
    Ok(())
}

/// The recession rays of the implicant `rows` at `s`, for each sign: a direction `d` of the
/// rows (`A·d >= 0`, `E·d == 0`) with `d_s <= -1` (or `>= 1`), asked of the solver; with
/// `g = |d_s|`, for each residue of `s` modulo `g` a point of the rows, from which `d` runs
/// without end. Each question is charged `size` and the rows' own terms, and the solver's
/// work on it ([`asked`]). A refusal of a question gives no ray for that sign (or residue);
/// past the work limit, `rays` is refused.
pub(super) fn rays(
    rows: &[Con],
    s: &Atom,
    size: u64,
    work: &mut Work,
) -> Result<Vec<Strided>, Refusal> {
    let mut out = Vec::new();
    let homogeneous: Vec<Formula> = (rows.iter())
        .map(|k| {
            Formula::Con(Con {
                lin: Lin {
                    terms: k.lin.terms.clone(),
                    constant: Int::from(0),
                },
                rel: k.rel,
            })
        })
        .collect();
    let rows_f: Vec<Formula> = rows.iter().map(|k| Formula::Con(k.clone())).collect();
    let row_terms: u64 = rows.iter().map(|k| k.lin.terms.len() as u64 + 1).sum();
    for down in [true, false] {
        // `d_s <= -1` or `-d_s <= -1`.
        let sign = if down { Int::from(1) } else { Int::from(-1) };
        let mut ask = homogeneous.clone();
        ask.push(Formula::Con(Con {
            lin: Lin {
                terms: [(s.clone(), -&sign)].into_iter().collect(),
                constant: Int::from(-1),
            },
            rel: Rel::Ge,
        }));
        work.read(size + row_terms)?;
        EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
        let Some(d) = asked(work, &Formula::and(ask))? else {
            continue;
        };
        let g = d.get(s).cloned().unwrap_or_else(|| Int::from(0)).abs();
        if g.is_zero() {
            continue;
        }
        // One point of the rows in each residue of `s` modulo `g`.
        let mut r = Int::from(0);
        while r < g {
            work.read(size + row_terms + 2)?;
            EXACT_QUESTIONS.set(EXACT_QUESTIONS.get() + 1);
            let k = Atom::Sym("#ray".into());
            let mut ask = rows_f.clone();
            ask.push(Formula::Con(Con {
                lin: Lin {
                    terms: [(s.clone(), Int::from(1)), (k, -&g)].into_iter().collect(),
                    constant: -&r,
                },
                rel: Rel::Eq,
            }));
            if let Some(p) = asked(work, &Formula::and(ask))? {
                let v = p.get(s).cloned().unwrap_or_else(|| Int::from(0));
                let (lo, hi) = if down {
                    (None, Some(v))
                } else {
                    (Some(v), None)
                };
                out.push(Strided {
                    lo,
                    hi,
                    step: g.clone(),
                    res: r.clone(),
                });
            }
            r = &r + &Int::from(1);
        }
    }
    Ok(out)
}

/// A question of [`rays`], asked as the cover asks its own (`Work::ask`): the solver's work
/// on it charged to `work`. `None` where it has no point or the solver refuses it for another
/// cause, as the residue questions of the cover read such a refusal; past the work limit,
/// refused with [`Refusal::Questions`] (PRES-rays-unmetered: the solver's work here was not
/// charged, only the fixed reads above).
fn asked(work: &mut Work, q: &Formula) -> Result<Option<Model>, Refusal> {
    match work.ask(q) {
        Ok(m) => Ok(m),
        Err(e) if work.used > work.limit => Err(e),
        Err(_) => Ok(None),
    }
}

// The four helpers below are used by the cover (`exact.rs`) as well as here. They are written
// in this module, which `exact.rs` imports, so that this module imports nothing of `exact.rs`
// (row MAIN-red-pugh-land: the two files were an import cycle).

/// The value of `l` at `m`, each atom absent from `m` zero and each product read as an atom of
/// its own, as the solver reads its points.
pub(super) fn value(l: &Lin, m: &Model) -> Int {
    let mut v = l.constant.clone();
    for (a, k) in &l.terms {
        if let Some(x) = m.get(a) {
            v = &v + &(k * x);
        }
    }
    v
}

pub(super) fn fin(v: &Int) -> End {
    End::Fin(Num::from(v))
}

/// The values of `s` that rows over `s` alone allow (each row with no atom holding or not).
pub(super) fn bounded(rows: &[Con], s: &Atom) -> IntervalSet {
    let mut range: IntRange = (None, None);
    for k in rows {
        let Some(a) = k.lin.terms.get(s) else {
            if !holds_at(k, &k.lin.constant) {
                return IntervalSet::empty();
            }
            continue;
        };
        let (add, bad) = row_range(a, &k.lin.constant, k.rel == Rel::Eq);
        if bad || meet_range(&mut range, add) {
            return IntervalSet::empty();
        }
    }
    let (lo, hi) = range;
    IntervalSet::range(
        lo.as_ref().map_or(End::NegInf, fin),
        hi.as_ref().map_or(End::PosInf, fin),
    )
}

/// Whether the constraint `c` holds where its form is `v`.
pub(super) fn holds_at(c: &Con, v: &Int) -> bool {
    match c.rel {
        Rel::Ge => !v.is_negative(),
        Rel::Eq => v.is_zero(),
    }
}

/// Calls `at` on each constraint of `f`, a shared part read once (by [`Id`]), the parts
/// waiting on an explicit stack (as `fold` in `exact.rs`). It is here, not in `exact.rs`, so
/// that `guarded.rs`, which `exact.rs` calls, reads it without importing `exact.rs`
/// (`s_01f_import_graph`).
pub(super) fn each_constraint<'a>(f: &'a Formula, mut at: impl FnMut(&'a Con)) {
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
            Formula::Holes(b) => stack.push(b.lowered()),
        }
    }
}

// The tests are files of their own: they name the solver (`presburger.rs`, the steps of
// [`Work`]), which calls this module through `exact.rs`, and test modules kept here would
// make the two import each other (`s_01f_import_graph`, row PRES-cover-wire).
#[cfg(test)]
mod pendants_rows;
#[cfg(test)]
mod tests;
