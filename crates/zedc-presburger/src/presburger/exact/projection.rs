//! Two ways to give a cell of the cover (`super::cover`) the values of an implicant that run
//! without end, which the elimination of `super::cell` leaves out (PRES-pugh-exact-projection-
//! research; the stuck case is `an_unbounded_conjunction_needs_one_cell`, whose cells each held
//! eight values of a ray, so the cover never ended):
//! - [`pugh`]: the exact projection of the implicant onto the symbol, by the Omega test's
//!   projection (Pugh, "A practical algorithm for exact array dependence analysis", CACM 35(8),
//!   1992, sections "Eliminating equality constraints", "Dark shadow" and "Projection"):
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

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};

use super::super::meter::{EXACT_QUESTIONS, LISTED, PIECE, Work};
use super::super::{Atom, Con, Formula, Lin, Model, Refusal, Rel};

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
    let mut held = Held { left: goal.clone() };
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

/// The values of the goal of [`pugh`] that no part found so far holds.
struct Held {
    left: IntervalSet,
}

impl Held {
    /// Whether every value of the goal is held.
    fn done(&self) -> bool {
        self.left.is_empty()
    }

    /// `p` added to `out`, and its values taken from those left: a part with no holes as one
    /// range; a part with holes value by value, but only in the finite pieces of what is left
    /// within its ends, each value taken charged [`LISTED`] and each piece read [`PIECE`].
    ///
    /// Complexity tradeoff: naive version, a part with holes taken from what is left by a set
    /// of its values, which has no end for a part with no end. Used: each finite piece of
    /// `left` within the part's ends read once, and each of the part's values in it taken once
    /// (it is then gone from `left`), so the values listed over all parts are at most the
    /// finite values of the goal, and each is a value outside the parts with no holes, which
    /// [`ranges`] lists one by one from the same parts when it is not cut short. A piece of
    /// `left` with no end inside a part with no end is skipped: the goal is then not held by
    /// that part alone, and the projection goes on, as without the goal.
    fn push(&mut self, p: Strided, out: &mut Vec<Strided>, work: &mut Work) -> Result<(), Refusal> {
        let lo = p.lo.as_ref().map_or(End::NegInf, fin);
        let hi = p.hi.as_ref().map_or(End::PosInf, fin);
        let within = self.left.meet(&IntervalSet::range(lo, hi));
        if p.step == Int::from(1) {
            work.charge(PIECE.saturating_mul(within.len() as u64 + 1))?;
            self.left = self.left.minus(&within);
        } else if !within.is_empty() {
            work.charge(PIECE.saturating_mul(within.len() as u64 + 1))?;
            let mut taken = Vec::new();
            for (l, u) in within.pieces() {
                let (End::Fin(l), End::Fin(u)) = (l, u) else {
                    continue;
                };
                let (l, u) = (Int::from(l), Int::from(u));
                let mut v = &l + &(&p.res - &l).mod_floor(&p.step);
                while v <= u {
                    work.charge(LISTED)?;
                    taken.push((fin(&v), fin(&v)));
                    v = &v + &p.step;
                }
            }
            self.left = self.left.minus(&IntervalSet::from_pieces(taken));
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

fn lcm(a: &Int, b: &Int) -> Int {
    &a.div_floor(&a.gcd(b)) * b
}

/// The values of `s` of the one disjunct, chosen by the point `m` of the conjunction `rows`,
/// of the projection of `rows` onto `s`: the model-based projection for linear integer
/// arithmetic, `LIAProj`, of Komuravelli, Gurfinkel and Chaki ("SMT-based model checking for
/// recursive programs", CAV 2014, section "Model Based Projection for Linear Integer
/// Arithmetic"; arXiv 1405.4028), which keeps of Cooper's quantifier elimination for each atom
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
            .fold(Int::ONE, |l, c| lcm(&l, &c.abs()));
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
                big_d = lcm(&big_d, &d);
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
        lcm(&step, &k.d.div_floor(&k.d.gcd(c)))
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

/// `a mod^ b` of Pugh's equality step: `a - b·floor(a/b + 1/2)`, in `(-b/2, b/2]`.
fn mod_hat(a: &Int, b: &Int) -> Int {
    let two = Int::from(2);
    let q = (&(&two * a) + b).div_floor(&(&two * b));
    a - &(b * &q)
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
                let (_, inv, _) = a1.mod_floor(&m).extended_gcd(&m).expect("gcd");
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
        let mut ek = Lin {
            terms: [(sigma, &(-&sign) * &m)].into_iter().collect(),
            constant: &sign * &mod_hat(&e.constant, &m),
        };
        for (a, c) in &e.terms {
            if *a != k {
                let v = &sign * &mod_hat(c, &m);
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
            shadow.push(Con { lin, rel: Rel::Ge });
        }
    }
    project(shadow, t, at, from, work, fresh, held, out)?;
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
        return Ok((plain, Vec::new()));
    }
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
            listed(&Int::from(l), &Int::from(u), &lcm, &have, work, &mut pieces)?;
        }
    }
    Ok((IntervalSet::from_pieces(pieces), tails))
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

/// Whether the constraint `c` holds where its form is `v`.
pub(super) fn holds_at(c: &Con, v: &Int) -> bool {
    match c.rel {
        Rel::Ge => !v.is_negative(),
        Rel::Eq => v.is_zero(),
    }
}

// The tests are files of their own: they name the solver (`presburger.rs`, the steps of
// [`Work`]), which calls this module through `exact.rs`, and test modules kept here would
// make the two import each other (`s_01f_import_graph`, row PRES-cover-wire).
#[cfg(test)]
mod pendants_rows;
#[cfg(test)]
mod tests;
