//! COMPLEXITY.md S22: the backward transfer through `if` chains whose arms read one shared
//! term. The transfer reads such a chain through a piecewise-affine summary of each term in
//! one input, and meets each integer demand with the hull of the term's values first. Neither
//! may change an exact preimage, so each one here is compared, whole (domains, exactness,
//! enumeration, stops, relation and refusal), with the transfer as it was before
//! (`zedc::store::preimage_ref`, main at fdf7918: the 397f1c9 transfer with later changes);
//! the differences allowed, each counted, are an inexact box made narrower and still sound
//! (`meeting_a_demand_with_the_hull_may_narrow_a_box_the_map2_cap_widened`); since plan item
//! S22b, a box of `c - x` that the transfer before merged across zero (`constant_minus.rs`),
//! whose pieces are now kept: the new result is checked by the interpreter, lies inside the one
//! before, and is exact wherever the one before was; and a preimage now exact, with no relation,
//! refusal or listing, that was inexact, refused or listed before, checked against the
//! interpreter: found by classes of remainders (COMPLEXITY.md S22e), or by S22b's reflection
//! when that makes an inexact box exact. The kinds are told apart by the result, not by the
//! item that made it, so a box S22b made exact counts as exact, not reflected. Each test states
//! how many cases of each kind it finds. The scaling tests
//! then check that the chains cost `O(n log n)`.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::Congruence;
use zedc::store::preimage::{Classes, Demand, Domains, exact_preimage, preimage};
use zedc::store::preimage_ref as before;

use super::check;
use super::random::{bool_term, domains, int_demand, int_term, with_functions};

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn ints(lo: i64, hi: i64) -> Demand {
    Demand::Ints(IntervalSet::of(lo, hi))
}

fn pieces(ps: &[(i64, i64)]) -> IntervalSet {
    IntervalSet::from_pieces(
        ps.iter()
            .map(|&(a, b)| (End::Fin(a), End::Fin(b)))
            .collect(),
    )
}

/// The domains `name: set`.
fn over(ds: &[(&str, IntervalSet)]) -> Domains {
    ds.iter().map(|(n, s)| (Arc::from(*n), s.clone())).collect()
}

/// `i` in `[lo, hi]`.
fn i_in(lo: i64, hi: i64) -> Domains {
    over(&[("i", IntervalSet::of(lo, hi))])
}

/// `t0 = base; tj = if guard(j) { t(j-1) } else { arm(j, t(j-1)) }`, both arms reading the one
/// term `t(j-1)`.
fn chain(
    k: usize,
    base: Term,
    guard: impl Fn(i64) -> Term,
    arm: impl Fn(i64, Term) -> Term,
) -> Term {
    (1..=k as i64).fold(base, |t, j| {
        let t = Arc::new(t);
        let other = arm(j, (*t).clone());
        Term::If(Arc::new(guard(j)), t, Arc::new(other))
    })
}

fn ge_i(j: i64) -> Term {
    prim(Prim::Ge, var("i"), int(j))
}

/// The else arm `t + c(j)`.
fn plus(c: impl Fn(i64) -> i64) -> impl Fn(i64, Term) -> Term {
    move |j, t| prim(Prim::Add, t, int(c(j)))
}

/// The chain over `i` with guard `i >= j` and else arm `t + c(j)`.
fn adds(k: usize, c: impl Fn(i64) -> i64) -> Term {
    chain(k, var("i"), ge_i, plus(c))
}

/// `t0 = z; tj = if bj >= 1 { t(j-1) } else { t(j-1) + c(j) }`, over `z` and the bits `bj`.
fn independent(k: usize, c: impl Fn(i64) -> i64) -> Term {
    chain(
        k,
        var("z"),
        |j| prim(Prim::Ge, var(&format!("b{j}")), int(1)),
        plus(c),
    )
}

fn bits(k: usize, lo: i64, hi: i64) -> Domains {
    let mut d = over(&[("z", IntervalSet::of(lo, hi))]);
    for j in 1..=k {
        d.insert(format!("b{j}").into(), IntervalSet::of(0, 1));
    }
    d
}

/// The families of chains, by name, at size `k`: the term, its domains and the demand.
///
/// - `probe`: else `t + 1`, `i` in `[-50, 50]`, `tk >= 0`; `live` the same with `i` in
///   `[-k, k]`, so that no demand merges with another;
/// - `probe_all` and `probe_half`: the probe with `i` over all integers and over
///   `[-100, inf)`, where `t + 1` leaves `i64` at `i = i64::MAX`;
/// - `probe_wide`: the probe with `i` in `[-100, 2^62]`;
/// - else arms `t + c_j` for `c_j` = `±1`, `j`, `±j`, `2^((j-1) mod 40)`;
/// - roots `tk == 0`, `tk != 0`, `tk` in `[-3, 7]` (an integer demand) and the same as a
///   conjunction;
/// - the probe spelled otherwise: guard `i > j-1`, `j <= i`, `i < j` with the arms swapped,
///   `1 + t`, `t - (-1)`, an input the chain does not read;
/// - `conj`: `t1 >= 0 && ... && tk >= 0`, every term of the chain asked;
/// - `cross`: `t0 = m` with the guards on `i`, two inputs in `[-50, 50]`; `cross_live` with
///   both in `[-k, k]`, and `cross_dead` in `[2-k, k-2]`, so its last two guards always hold;
/// - guards `i != j`, `abs(i) >= j` and `i mod 7 == j mod 7`;
/// - else arms that are not translations: `j - t`, `3t - 1`, `min(t + 1, 100)`, `-2t`,
///   `0 - (t + 1)`;
/// - `jt_range` and `five_range`: else arms `j - t` and `5 - t` with the integer demand
///   `tk` in `[-3, 7]`, `_live` over `[-k, k]` (plan item S22b-rest: the summary reads `c - t`);
/// - chains of independent guards on bits, `indep` and `subset`, and the `abs` chain
///   `s_j = abs(s_(j-1)) - 2^(k+1-j)`.
fn family(name: &str, k: usize) -> (Term, Domains, Demand) {
    let ki = k as i64;
    let narrow = || i_in(-50, 50);
    let live = || i_in(-ki, ki);
    let ge0 = |t| prim(Prim::Ge, t, int(0));
    let yes = Demand::Bool(true);
    let alt = |j: i64| if j % 2 == 0 { 1 } else { -1 };
    let altj = |j: i64| if j % 2 == 0 { j } else { -j };
    match name {
        "probe" => (ge0(adds(k, |_| 1)), narrow(), yes),
        "live" => (ge0(adds(k, |_| 1)), live(), yes),
        "probe_all" => (ge0(adds(k, |_| 1)), over(&[("i", IntervalSet::top())]), yes),
        "probe_wide" => (ge0(adds(k, |_| 1)), i_in(-100, 1 << 62), yes),
        "probe_half" => {
            let half = IntervalSet::range(End::Fin(-100), End::PosInf);
            (ge0(adds(k, |_| 1)), over(&[("i", half)]), yes)
        }
        "alt" => (ge0(adds(k, alt)), narrow(), yes),
        "alt_live" => (ge0(adds(k, alt)), live(), yes),
        "cj" => (ge0(adds(k, |j| j)), narrow(), yes),
        "cj_live" => (ge0(adds(k, |j| j)), live(), yes),
        "altj" => (ge0(adds(k, altj)), narrow(), yes),
        "altj_live" => (ge0(adds(k, altj)), live(), yes),
        "pow2" => (ge0(adds(k, |j| 1 << ((j - 1) % 40))), narrow(), yes),
        "eq0" => (prim(Prim::Eq, adds(k, |_| 1), int(0)), narrow(), yes),
        "eq0_live" => (prim(Prim::Eq, adds(k, |_| 1), int(0)), live(), yes),
        "ne0" => (prim(Prim::Ne, adds(k, |_| 1), int(0)), narrow(), yes),
        "range" => (adds(k, |_| 1), narrow(), ints(-3, 7)),
        "range_live" => (adds(k, |_| 1), live(), ints(-3, 7)),
        "rangeand" => {
            let t = adds(k, |_| 1);
            let lo = prim(Prim::Ge, t.clone(), int(-3));
            (
                prim(Prim::And, lo, prim(Prim::Le, t, int(7))),
                narrow(),
                yes,
            )
        }
        "gt" => {
            let t = chain(
                k,
                var("i"),
                |j| prim(Prim::Gt, var("i"), int(j - 1)),
                plus(|_| 1),
            );
            (ge0(t), narrow(), yes)
        }
        "le" => {
            let t = chain(
                k,
                var("i"),
                |j| prim(Prim::Le, int(j), var("i")),
                plus(|_| 1),
            );
            (ge0(t), narrow(), yes)
        }
        "swapped" => {
            let t = (1..=ki).fold(var("i"), |t, j| {
                let t = Arc::new(t);
                let more = prim(Prim::Add, (*t).clone(), int(1));
                Term::If(
                    Arc::new(prim(Prim::Lt, var("i"), int(j))),
                    Arc::new(more),
                    t,
                )
            });
            (ge0(t), narrow(), yes)
        }
        "constfirst" => {
            let t = chain(k, var("i"), ge_i, |_, t| prim(Prim::Add, int(1), t));
            (ge0(t), narrow(), yes)
        }
        "sub" => {
            let t = chain(k, var("i"), ge_i, |_, t| prim(Prim::Sub, t, int(-1)));
            (ge0(t), narrow(), yes)
        }
        "twoin" => {
            let ds = over(&[
                ("i", IntervalSet::of(-50, 50)),
                ("u", IntervalSet::of(0, 5)),
            ]);
            (ge0(adds(k, |_| 1)), ds, yes)
        }
        "conj" | "conj_live" => {
            let mut t = var("i");
            let mut all: Option<Term> = None;
            for j in 1..=ki {
                let prev = Arc::new(t);
                let more = prim(Prim::Add, (*prev).clone(), int(1));
                t = Term::If(Arc::new(ge_i(j)), prev, Arc::new(more));
                let tj = ge0(t.clone());
                all = Some(all.map_or(tj.clone(), |a| prim(Prim::And, a, tj)));
            }
            let all = all.unwrap_or(Term::Lit(Value::Bool(true)));
            let ds = if name == "conj" { narrow() } else { live() };
            (all, ds, yes)
        }
        "cross" | "cross_live" | "cross_dead" => {
            let w = match name {
                "cross" => 50,
                "cross_live" => ki,
                _ => ki - 2,
            };
            let ds = over(&[("i", IntervalSet::of(-w, w)), ("m", IntervalSet::of(-w, w))]);
            (ge0(chain(k, var("m"), ge_i, plus(|_| 1))), ds, yes)
        }
        "ne_guard" => {
            let t = chain(
                k,
                var("i"),
                |j| prim(Prim::Ne, var("i"), int(j)),
                plus(|_| 1),
            );
            (ge0(t), narrow(), yes)
        }
        "abs_guard" => {
            let abs = || Term::Prim(Prim::Abs, vec![var("i")]);
            let t = chain(k, var("i"), |j| prim(Prim::Ge, abs(), int(j)), plus(|_| 1));
            (ge0(t), narrow(), yes)
        }
        "mod7" => {
            let g = |j: i64| prim(Prim::Eq, prim(Prim::Mod, var("i"), int(7)), int(j % 7));
            (ge0(chain(k, var("i"), g, plus(|_| 1))), narrow(), yes)
        }
        "jt" => {
            let t = chain(k, var("i"), ge_i, |j, t| prim(Prim::Sub, int(j), t));
            (ge0(t), narrow(), yes)
        }
        "jt_range" | "jt_range_live" => {
            let t = chain(k, var("i"), ge_i, |j, t| prim(Prim::Sub, int(j), t));
            let ds = if name == "jt_range" { narrow() } else { live() };
            (t, ds, ints(-3, 7))
        }
        "five_range" | "five_range_live" => {
            let t = chain(k, var("i"), ge_i, |_, t| prim(Prim::Sub, int(5), t));
            let ds = if name == "five_range" {
                narrow()
            } else {
                live()
            };
            (t, ds, ints(-3, 7))
        }
        "t3" => {
            let arm = |_, t| prim(Prim::Sub, prim(Prim::Mul, t, int(3)), int(1));
            (ge0(chain(k, var("i"), ge_i, arm)), narrow(), yes)
        }
        "t3_gaps" | "t3_gaps_no" | "t3_gaps_five" | "t3_gaps_five_no" => {
            let arm = |_, t| prim(Prim::Sub, prim(Prim::Mul, t, int(3)), int(1));
            let mut ps = vec![(-24, -21), (-15, -4)];
            if name.contains("five") {
                ps.push((5, 5));
            }
            let ds = over(&[("i", pieces(&ps))]);
            let d = Demand::Bool(!name.ends_with("_no"));
            (ge0(chain(k, var("i"), ge_i, arm)), ds, d)
        }
        "min" => {
            let arm = |_, t| prim(Prim::Min, prim(Prim::Add, t, int(1)), int(100));
            (ge0(chain(k, var("i"), ge_i, arm)), narrow(), yes)
        }
        "mul" => {
            let t = chain(k, var("i"), ge_i, |_, t| prim(Prim::Mul, int(-2), t));
            (t, narrow(), Demand::Ints(pieces(&[(-40, -5), (3, 30)])))
        }
        "neg" => {
            let arm = |_, t| prim(Prim::Sub, int(0), prim(Prim::Add, t, int(1)));
            let t = chain(k, var("i"), ge_i, arm);
            (t, narrow(), Demand::Ints(pieces(&[(-10, -2), (4, 9)])))
        }
        "indep_2j" => (
            independent(k, |j| 2 * j),
            bits(k, -ki * (ki + 1), 0),
            ints(0, 0),
        ),
        "indep_1" => (independent(k, |_| 1), bits(k, -ki, ki), ints(0, 0)),
        "subset" => {
            let cs: Vec<i64> = (1..=ki)
                .map(|j| (1 << 40) + 2 * ((j * 0x9e37_79b9) % (1 << 30)))
                .collect();
            let target: i64 = cs.iter().step_by(2).sum();
            (
                independent(k, |j| cs[j as usize - 1]),
                bits(k, 0, 0),
                ints(target, target),
            )
        }
        "abs_chain" => {
            let t = (1..=ki).fold(var("i"), |t, j| {
                let abs = Term::Prim(Prim::Abs, vec![t]);
                prim(Prim::Sub, abs, int(1 << (ki + 1 - j)))
            });
            let r = 1 << (ki + 2);
            (t, i_in(-r, r), ints(0, 0))
        }
        _ => panic!("no family {name}"),
    }
}

fn old(d: &Demand) -> before::Demand {
    match d {
        Demand::Ints(z) => before::Demand::Ints(z.clone()),
        Demand::Bool(b) => before::Demand::Bool(*b),
    }
}

/// Runs `f` on a thread with a stack deep enough for chains of thousands of terms.
fn on_big_stack<R: Send>(f: impl FnOnce() -> R + Send) -> R {
    std::thread::scope(|s| {
        let thread = std::thread::Builder::new().stack_size(1 << 28);
        thread.spawn_scoped(s, f).unwrap().join().unwrap()
    })
}

/// The cases compared, the differences found, each shown, the cases whose inexact box is
/// narrower than the one before and still sound, the other boxes of `c - x` that S22b changed,
/// and the cases now exact that the transfer before left inexact, refused or listed (by
/// classes of remainders, COMPLEXITY.md S22e, or by S22b's reflection).
#[derive(Default)]
struct Diffs {
    cases: usize,
    found: Vec<String>,
    narrower: usize,
    reflected: usize,
    exact: usize,
}

/// Whether the interpreter refutes `domains` as the preimage of `d` under `t` over `ds` on
/// the points within (-60, 60): a point that meets `d` lies outside, or, when `exact`, a point
/// inside fails `d`.
fn refuted(t: &Term, ds: &Domains, d: &Demand, domains: &Domains, exact: bool) -> bool {
    let names: Vec<Arc<str>> = ds.keys().cloned().collect();
    super::points(ds, &names, (-60, 60)).iter().any(|pt| {
        let inside = names
            .iter()
            .zip(pt)
            .all(|(n, &v)| domains.get(n).is_none_or(|s| s.contains(v)));
        let meets = super::meets(t, &names, pt, d);
        (meets && !inside) || (!meets && exact && inside)
    })
}

impl Diffs {
    /// Compares the preimage of `d` under `t` over `ds` with the one before. A difference
    /// counts as narrower when only the box differs, both are inexact, and the new box is a
    /// sound subset of the one before; every other difference is found.
    fn preimage(&mut self, what: &str, t: &Term, ds: &Domains, d: &Demand) {
        let (now, then) = (preimage(t, ds, d), before::preimage(t, ds, &old(d)));
        let (new, old) = (format!("{now:?}"), format!("{then:?}"));
        // Both inexact and alike but for the box, and the new box lies inside the one before
        // and holds every point the interpreter finds: the clip narrows a result the map2 cap
        // widened, so Lemma 4's equality does not hold there.
        macro_rules! rest {
            ($p:expr) => {
                format!(
                    "{:?} {:?} {:?} {:?} {:?}",
                    $p.exact, $p.enumerated, $p.stops, $p.relation, $p.refusal
                )
            };
        }
        let inside = |s: &IntervalSet, o: &IntervalSet| {
            s.pieces()
                .iter()
                .all(|&(lo, hi)| o.pieces().iter().any(|&(l, h)| l <= lo && hi <= h))
        };
        if new != old
            && !now.exact
            && rest!(now) == rest!(then)
            && now.domains.keys().eq(then.domains.keys())
            && now.domains.iter().all(|(n, s)| inside(s, &then.domains[n]))
            && !refuted(t, ds, d, &now.domains, now.exact)
        {
            self.cases += 1;
            self.narrower += 1;
            return;
        }
        // Now exact, with no relation, refusal or listing: the box equals the one before when
        // that was exact, lies inside it otherwise, and the interpreter finds no point that
        // meets the demand outside it or fails it inside. Classes of remainders (S22e) find
        // these, and so does S22b's reflection of `c - x` when it makes an inexact box exact;
        // such a box is counted here, before the reflected branch below is tried.
        if new != old
            && now.exact
            && !now.enumerated
            && now.relation.is_none()
            && now.refusal.is_none()
            && format!("{:?}", now.stops) == format!("{:?}", then.stops)
            && now.domains.keys().eq(then.domains.keys())
            && if then.exact {
                now.domains == then.domains
            } else {
                now.domains.iter().all(|(n, s)| inside(s, &then.domains[n]))
            }
            && !refuted(t, ds, d, &now.domains, true)
        {
            self.cases += 1;
            self.exact += 1;
            return;
        }
        // Plan item S22b: the transfer before took `c - x` as the forward image of `{c} - z`,
        // whose cap merged pieces moved across zero, so its box may be wider, and may be marked
        // exact while holding points that fail. The new result holds every point that meets
        // the demand, holds no point that fails when it is exact, lies inside the one before,
        // and is exact wherever the one before was.
        if new != old
            && (now.exact || !then.exact)
            && now.domains.keys().eq(then.domains.keys())
            && now.domains.iter().all(|(n, s)| inside(s, &then.domains[n]))
            && !refuted(t, ds, d, &now.domains, now.exact)
        {
            self.cases += 1;
            self.reflected += 1;
            return;
        }
        self.note(what, t, ds, d, new, old);
    }

    /// Compares the exact preimage of `d` under `t` over `ds` and `cs` with the one before.
    fn exact(&mut self, what: &str, t: &Term, ds: &Domains, cs: &Classes, d: &Demand) {
        let new = format!("{:?}", exact_preimage(t, ds, cs, d));
        let old = format!("{:?}", before::exact_preimage(t, ds, cs, &old(d)));
        self.note(what, t, ds, d, new, old);
    }

    fn note(&mut self, what: &str, t: &Term, ds: &Domains, d: &Demand, new: String, old: String) {
        self.cases += 1;
        if new != old {
            // The families' terms are too large to show; their names and sizes say which.
            let t = if what.contains(" k=") {
                String::new()
            } else {
                t.to_string()
            };
            self.found.push(format!(
                "{what}: {t} over {ds:?}, demand {d:?}\n  now    {new}\n  before {old}"
            ));
        }
    }

    /// [`Diffs::none_but`] with no box of `c - x` changed and none made exact.
    fn none(self, least: usize, narrower: usize) {
        self.none_but(least, narrower, 0, 0)
    }

    /// Panics, showing the first differences, when there are any, when fewer than `least`
    /// cases were compared, when the number of narrower boxes is not `narrower`, when the
    /// number of other boxes of `c - x` that S22b changed is not `reflected`, or when the number
    /// of boxes made exact (by classes of remainders or by S22b) is not `exact`.
    fn none_but(self, least: usize, narrower: usize, reflected: usize, exact: usize) {
        assert!(
            self.found.is_empty(),
            "{} of {} preimages differ from the transfer before:\n{}",
            self.found.len(),
            self.cases,
            self.found[..self.found.len().min(5)].join("\n")
        );
        assert!(self.cases >= least, "only {} cases compared", self.cases);
        assert_eq!(
            self.narrower, narrower,
            "the number of narrower inexact boxes changed"
        );
        assert_eq!(
            self.reflected, reflected,
            "the number of other boxes of `c - x` changed by S22b differs"
        );
        assert_eq!(self.exact, exact, "the number of boxes made exact changed");
    }
}

/// A random domain of `i`: all integers, a half-line, or one to three intervals apart.
fn chain_domain(rng: &mut Rng) -> IntervalSet {
    match rng.below(6) {
        0 => IntervalSet::top(),
        1 => IntervalSet::range(End::Fin(rng.int(-20, 5)), End::PosInf),
        2 => IntervalSet::range(End::NegInf, End::Fin(rng.int(-5, 20))),
        _ => {
            let mut lo = rng.int(-25, -5);
            let mut ps = Vec::new();
            for _ in 0..rng.int(1, 3) {
                let hi = lo + rng.int(0, 12);
                ps.push((End::Fin(lo), End::Fin(hi)));
                lo = hi + rng.int(2, 6);
            }
            IntervalSet::from_pieces(ps)
        }
    }
}

/// A random chain of up to four `if`s over `i` whose arms read one shared term, each arm
/// the term, a translation, a reflection, a multiple, a `min` or a sum of the term with itself.
fn random_chain(rng: &mut Rng) -> Term {
    let mut t = if rng.below(4) == 0 {
        prim(Prim::Add, var("i"), int(rng.int(-5, 5)))
    } else {
        var("i")
    };
    for _ in 0..rng.int(1, 4) {
        let c = rng.int(-10, 10);
        let g = match rng.below(7) {
            0 => prim(Prim::Ge, var("i"), int(c)),
            1 => prim(Prim::Le, var("i"), int(c)),
            2 => prim(Prim::Lt, int(c), var("i")),
            3 => prim(Prim::Eq, var("i"), int(c)),
            4 => prim(Prim::Ne, var("i"), int(c)),
            5 => prim(
                Prim::Eq,
                prim(Prim::Mod, var("i"), int(3)),
                int(c.rem_euclid(3)),
            ),
            _ => prim(
                Prim::Ge,
                Term::Prim(Prim::Abs, vec![var("i")]),
                int(c.abs()),
            ),
        };
        let shared = Arc::new(t);
        let mut arm = || {
            let s = (*shared).clone();
            let c = rng.int(-6, 6);
            match rng.below(10) {
                0 => s,
                1 => prim(Prim::Add, s, int(c)),
                2 => prim(Prim::Sub, s, int(c)),
                3 => prim(Prim::Sub, int(c), s),
                4 => prim(Prim::Sub, int(0), s),
                5 => Term::Prim(Prim::Neg, vec![s]),
                6 => prim(Prim::Mul, s, int(c)),
                7 => prim(Prim::Mul, int(c), s),
                8 => prim(Prim::Min, s, int(c)),
                _ => prim(Prim::Add, s.clone(), s),
            }
        };
        let (a, b) = (arm(), arm());
        t = Term::If(Arc::new(g), Arc::new(a), Arc::new(b));
    }
    t
}

/// A random demand on `t`: on its value, one or two intervals or a half-line, or a comparison
/// of it with a constant asked true or false.
fn chain_demand(rng: &mut Rng, t: Term) -> (Term, Demand) {
    let a = rng.int(-30, 30);
    let b = rng.below(2) == 0;
    let cmp = |p| prim(p, t.clone(), int(a));
    match rng.below(10) {
        0 => (t, ints(a, a)),
        1 => (t, ints(a, a + rng.int(0, 15))),
        2 => (
            t,
            Demand::Ints(IntervalSet::range(End::NegInf, End::Fin(a))),
        ),
        3 => (
            t,
            Demand::Ints(IntervalSet::range(End::Fin(a), End::PosInf)),
        ),
        4 => (t, Demand::Ints(pieces(&[(a, a + 1), (a + 5, a + 6)]))),
        5 => (cmp(Prim::Ge), Demand::Bool(b)),
        6 => (cmp(Prim::Lt), Demand::Bool(b)),
        7 => (cmp(Prim::Eq), Demand::Bool(b)),
        8 => (cmp(Prim::Le), Demand::Bool(b)),
        _ => (cmp(Prim::Gt), Demand::Bool(b)),
    }
}

/// The families in `sets` at sizes on both sides of the domain's width (50), where the hull of
/// a term starts to merge demands, and each under three more domains of `i`; the extra sizes
/// of each family follow its name.
fn chain_families(sets: &[(&str, &[usize])], least: usize) {
    on_big_stack(|| {
        let wide = (0..=8).chain([13, 16, 21, 32, 49, 50, 51, 64]);
        let mut diffs = Diffs::default();
        for &(name, more) in sets {
            for k in wide.clone().chain(more.iter().copied()) {
                let (t, ds, d) = family(name, k);
                diffs.preimage(&format!("{name} k={k}"), &t, &ds, &d);
                if !ds.contains_key("i") {
                    continue;
                }
                let mut rng = Rng::new(k as u64 * 31 + name.len() as u64);
                for _ in 0..3 {
                    let mut ds = ds.clone();
                    ds.insert("i".into(), chain_domain(&mut rng));
                    diffs.preimage(&format!("{name} k={k}"), &t, &ds, &d);
                }
            }
        }
        diffs.none(least, 0);
    });
}

/// The families with one guard each, at the sizes above.
#[test]
fn chains_of_shared_terms_keep_their_preimages() {
    chain_families(
        &[
            ("probe", &[256]),
            ("live", &[64, 128]),
            ("probe_all", &[256]),
            ("probe_half", &[256]),
            ("alt", &[256]),
            ("alt_live", &[64, 128]),
            ("eq0", &[256]),
            ("eq0_live", &[64, 128]),
            ("ne0", &[]),
            ("range", &[256]),
            ("range_live", &[64, 128]),
            ("rangeand", &[]),
            ("gt", &[]),
            ("le", &[]),
            ("swapped", &[]),
            ("constfirst", &[]),
            ("sub", &[]),
            ("twoin", &[]),
            ("conj", &[]),
            ("conj_live", &[]),
            ("ne_guard", &[]),
            ("abs_guard", &[]),
            ("jt", &[]),
            ("jt_range", &[256]),
            ("jt_range_live", &[64, 128]),
            ("five_range", &[]),
            ("five_range_live", &[64]),
            ("min", &[]),
            ("neg", &[]),
        ],
        1612,
    );
}

/// The families whose constants grow with the chain (`c_j = j`), at the sizes above.
#[test]
fn chains_of_growing_constants_keep_their_preimages() {
    chain_families(
        &[
            ("cj", &[]),
            ("cj_live", &[24]),
            ("altj", &[]),
            ("altj_live", &[24]),
        ],
        280,
    );
}

/// Families whose transfer is slow or whose values leave `i64` at larger sizes.
#[test]
fn chains_of_slow_families_keep_their_preimages() {
    on_big_stack(|| {
        let small = (0..=8).chain([13, 16, 21, 32]);
        let mut diffs = Diffs::default();
        for (name, ks) in [
            ("cross", small.clone().take(10).collect::<Vec<_>>()),
            ("cross_live", small.clone().take(10).collect()),
            ("mod7", small.clone().take(9).collect()),
            ("pow2", small.clone().take(10).collect()),
            ("t3", small.clone().take(9).collect()),
            ("mul", small.clone().collect()),
            ("indep_2j", vec![1, 2, 3, 5, 8]),
            ("indep_1", vec![1, 2, 3, 5, 8, 12]),
            ("subset", vec![1, 2, 3, 5, 8, 10]),
            ("abs_chain", vec![1, 2, 3, 5, 8]),
        ] {
            for k in ks {
                let (t, ds, d) = family(name, k);
                diffs.preimage(&format!("{name} k={k}"), &t, &ds, &d);
            }
        }
        diffs.none_but(83, 0, 0, 7);
    });
}

/// Random chains of shared terms, under random domains of one to three pieces and random
/// demands on the chain or on a comparison of it.
#[test]
fn random_chains_of_shared_terms_keep_their_preimages() {
    on_big_stack(|| {
        let mut diffs = Diffs::default();
        // Guards `i >= c` and translations, as the summary reads them.
        let mut rng = Rng::new(0x9e37_79b9_7f4a_7c15);
        for _ in 0..4000 {
            let mut t = var("i");
            for _ in 0..rng.int(0, 12) {
                let prev = Arc::new(t);
                let g = ge_i(rng.int(-25, 25));
                let c = rng.int(-6, 6);
                let more = if rng.below(10) == 0 {
                    prim(Prim::Sub, (*prev).clone(), int(-c))
                } else {
                    prim(Prim::Add, (*prev).clone(), int(c))
                };
                t = Term::If(Arc::new(g), prev, Arc::new(more));
            }
            let lo = rng.int(-30, 5);
            let mut ds = i_in(lo, lo + rng.int(0, 40));
            if rng.below(10) == 0 {
                ds.insert("y".into(), IntervalSet::of(0, 3));
            }
            let (t, d) = chain_demand(&mut rng, t);
            diffs.preimage("translations", &t, &ds, &d);
        }
        diffs.none(4000, 0);
    });
}

/// The one kind of difference the comparison allows. Lemma 4 of the synthesis (meeting a
/// demand with a hull of the term's values changes no preimage) holds for the exact
/// preimage, but the map2 cap (`revision::map2`) merges pieces by how many the operands have,
/// demand included, so an inexact box depends on the demand's pieces outside the hull. Here
/// the demand on `x` through `x + x` is met with `x`'s hull `[-17, inf)`, the cap then merges
/// less, and the box shrinks from `[-10] | [-2, 10]` to `[-10] | [-2, 3] | [10]`; the true set
/// is `{-10} | [1, 3] | {10}`. Both boxes are inexact and hold every point that meets the
/// demand. The transfer before cannot be kept on such demands without reading both the met
/// and the whole demand at each term, which doubles the demands per level.
#[test]
fn meeting_a_demand_with_the_hull_may_narrow_a_box_the_map2_cap_widened() {
    let i = || var("i");
    let abs = || Term::Prim(Prim::Abs, vec![i()]);
    let x = Term::If(
        Arc::new(prim(Prim::Ge, abs(), int(10))),
        Arc::new(prim(Prim::Sub, int(-5), i())),
        Arc::new(prim(Prim::Sub, int(6), i())),
    );
    let t = Term::If(
        Arc::new(prim(Prim::Ge, abs(), int(3))),
        Arc::new(prim(Prim::Mul, int(2), x.clone())),
        Arc::new(prim(Prim::Add, x.clone(), x)),
    );
    let ds = over(&[("i", IntervalSet::range(End::NegInf, End::Fin(12)))]);
    let d = Demand::Ints(pieces(&[(-30, -29), (6, 10)]));
    let (now, then) = (preimage(&t, &ds, &d), before::preimage(&t, &ds, &old(&d)));
    assert!(!now.exact && !then.exact);
    assert_eq!(now.domains["i"], pieces(&[(-10, -10), (-2, 3), (10, 10)]));
    assert_eq!(then.domains["i"], pieces(&[(-10, -10), (-2, 10)]));
    assert!(!refuted(&t, &ds, &d, &now.domains, false));
    let mut diffs = Diffs::default();
    diffs.preimage("the narrowed case", &t, &ds, &d);
    assert_eq!((diffs.cases, diffs.narrower, diffs.found.len()), (1, 1, 0));
}

/// Every kind of guard and arm the summary reads, and some it does not: the cases `from..to`
/// of one sequence, split in two tests so they run in parallel.
fn random_guarded_chains(from: usize, to: usize, narrower: usize, reflected: usize, exact: usize) {
    on_big_stack(|| {
        let mut diffs = Diffs::default();
        let mut rng = Rng::new(22);
        for i in 0..to {
            let t = random_chain(&mut rng);
            let ds = over(&[("i", chain_domain(&mut rng))]);
            let (t, d) = if rng.below(3) == 0 {
                let p = rng.pick(&[Prim::Ge, Prim::Le, Prim::Eq, Prim::Ne, Prim::Lt]);
                (
                    prim(p, t, int(rng.int(-10, 10))),
                    Demand::Bool(rng.below(2) == 0),
                )
            } else {
                (t, int_demand(&mut rng))
            };
            if i >= from {
                diffs.preimage("random chain", &t, &ds, &d);
            }
        }
        diffs.none_but(to - from, narrower, reflected, exact);
    });
}

/// Random chains of every kind of guard, the first half.
#[test]
fn random_guarded_chains_keep_their_preimages() {
    random_guarded_chains(0, 2000, 2, 6, 39);
}

/// Random chains of every kind of guard, the second half. S22b changes 7 boxes of `c - x` here;
/// two of them, inexact before and exact now, count as made exact (54 by classes of remainders,
/// S22e, and 2 by S22b): the chains `(if (6 < i) { (if (7 < i) { (0 - …` and
/// `if ((i mod 3) == 1) { min(if (i >= -9) { …`, whose results are the same on main before S22e
/// merged (5adc3c2).
#[test]
fn more_random_guarded_chains_keep_their_preimages() {
    random_guarded_chains(2000, 4000, 0, 5, 56);
}

/// The random terms of `random.rs`, with its seeds and others, and its exact preimages.
#[test]
fn random_terms_keep_their_preimages() {
    on_big_stack(|| {
        let mut diffs = Diffs::default();
        let seeds = [
            (25, 250, false, false),
            (2025, 250, true, false),
            (7, 400, false, true),
        ];
        let more = [
            (77, 400, true, true),
            (777, 1500, false, true),
            (31337, 1500, true, true),
        ];
        for (seed, cases, test, calls) in seeds.into_iter().chain(more) {
            let mut rng = Rng::new(seed);
            for case in 0..cases {
                let test = test && (seed < 777 || case % 2 == 1);
                let (t, d) = if test {
                    (bool_term(&mut rng, 3), Demand::Bool(rng.below(2) == 0))
                } else {
                    (int_term(&mut rng, 3), int_demand(&mut rng))
                };
                let t = if calls && case % 3 == 0 {
                    with_functions(&mut rng, &t)
                } else {
                    t
                };
                let ds = domains(&mut rng);
                diffs.preimage("random term", &t, &ds, &d);
            }
        }
        for seed in 1000..1010 {
            let mut rng = Rng::new(seed);
            for _ in 0..200 {
                let (t, d) = if rng.below(2) == 0 {
                    (bool_term(&mut rng, 4), Demand::Bool(rng.below(2) == 0))
                } else {
                    (int_term(&mut rng, 4), int_demand(&mut rng))
                };
                let ds = domains(&mut rng);
                diffs.preimage("random term, depth 4", &t, &ds, &d);
            }
        }
        for (seed, test) in [(7, false), (77, true)] {
            let mut rng = Rng::new(seed);
            for _ in 0..250 {
                let (t, d) = if test {
                    (bool_term(&mut rng, 3), Demand::Bool(rng.below(2) == 0))
                } else {
                    (int_term(&mut rng, 3), int_demand(&mut rng))
                };
                let mut bounded = || {
                    let lo = rng.int(-15, 10);
                    IntervalSet::of(lo, (lo + rng.int(0, 20)).min(15))
                };
                let ds = over(&[("x", bounded()), ("y", bounded())]);
                let mut cs = Classes::new();
                if rng.below(3) == 0 {
                    let m = rng.int(2, 4);
                    cs.insert("x".into(), Congruence::new(m as u64, rng.int(0, m - 1)));
                }
                diffs.exact("exact", &t, &ds, &cs, &d);
            }
        }
        // The one box S22b changes here, `((5 mod (3 - x)) mod abs(5))` with `x` in `[-4, ∞)`
        // and the demand `[-3, 5]`, is now exact (`x` in `[-4, 2] | [4, ∞)`, where `3 - x` is
        // not zero) and was inexact (`[-4, ∞)`), so it counts as made exact, not reflected.
        diffs.none_but(6800, 0, 0, 1);
    });
}

/// Guards, domains, offsets and demands at the two ends of `i64`, values that leave `i64`
/// inside a chain, reflections under several demands, products, and empty demands.
#[test]
fn ends_of_i64_and_other_corners_keep_their_preimages() {
    use End::{Fin, NegInf, PosInf};
    const MIN: i64 = i64::MIN;
    const MAX: i64 = i64::MAX;
    on_big_stack(|| {
        let mut diffs = Diffs::default();
        let ends = [MIN, MIN + 1, MIN + 2, -1, 0, 1, MAX - 2, MAX - 1, MAX];
        let doms = [(-2, 2), (MIN, MIN + 3), (MAX - 3, MAX), (MIN, MAX)];
        let demands = [
            Demand::Ints(IntervalSet::single(0)),
            Demand::Ints(IntervalSet::range(Fin(MAX - 1), PosInf)),
            Demand::Ints(IntervalSet::range(NegInf, Fin(MIN + 1))),
            Demand::Ints(IntervalSet::from_pieces(vec![
                (NegInf, Fin(MIN + 2)),
                (Fin(MAX - 2), PosInf),
            ])),
        ];
        let guards: [fn(i64) -> Term; 3] = [
            ge_i,
            |b| prim(Prim::Le, var("i"), int(b)),
            |b| prim(Prim::Gt, var("i"), int(b)),
        ];
        for b in ends {
            for c in [-2, -1, 1, 2, MAX, MIN] {
                for (lo, hi) in doms {
                    for d in &demands {
                        for g in guards {
                            let t = chain(1, var("i"), |_| g(b), plus(|_| c));
                            diffs.preimage("ends", &t, &i_in(lo, hi), d);
                            // Two levels, the second guard at the other end.
                            let t = chain(
                                2,
                                var("i"),
                                |j| g(if j == 1 { b } else { -b.saturating_add(1) }),
                                plus(|_| c),
                            );
                            diffs.preimage("ends, two levels", &t, &i_in(lo, hi), d);
                        }
                    }
                }
            }
        }
        // Sums that leave `i64` on some inputs and not others, deep in a chain.
        for c in [MAX / 2, MAX / 3, MIN / 2, MAX - 5] {
            for k in [2, 3, 5, 8] {
                for (lo, hi) in [(0, 10), (-10, 10), (MAX - 20, MAX), (MIN, MIN + 20)] {
                    let t = adds(k, |_| c);
                    for d in &demands {
                        diffs.preimage("overflow", &t, &i_in(lo, hi), d);
                    }
                    diffs.preimage(
                        "overflow",
                        &prim(Prim::Ge, t.clone(), int(0)),
                        &i_in(lo, hi),
                        &Demand::Bool(true),
                    );
                    let t = chain(k, var("i"), ge_i, |_, t| prim(Prim::Mul, t, int(c)));
                    diffs.preimage("overflow, product", &t, &i_in(lo, hi), &ints(-5, 5));
                }
            }
        }
        // Reflections and products under demands of several pieces on both signs.
        let neg = |t: Term| Term::Prim(Prim::Neg, vec![t]);
        let arms: [(Term, Term); 7] = [
            (prim(Prim::Sub, int(0), var("i")), var("i")),
            (neg(var("i")), var("i")),
            (
                prim(Prim::Sub, int(0), prim(Prim::Add, var("i"), int(12))),
                var("i"),
            ),
            (var("i"), prim(Prim::Sub, int(0), var("i"))),
            (prim(Prim::Sub, int(7), var("i")), var("i")),
            (
                prim(Prim::Mul, var("i"), int(3)),
                prim(Prim::Mul, int(-2), var("i")),
            ),
            (
                prim(Prim::Mul, int(-1), var("i")),
                prim(Prim::Add, var("i"), int(4)),
            ),
        ];
        let zs = [
            pieces(&[(-10, 0), (10, 25)]),
            pieces(&[(-25, -20), (-10, -5), (3, 4), (10, 12)]),
            pieces(&[(-30, -28), (-20, -18), (-9, -7), (-3, -2)]),
            pieces(&[(2, 3), (6, 7), (11, 12), (20, 21)]),
            pieces(&[(-60, 60)]),
            IntervalSet::empty(),
        ];
        for (b, (yes, no)) in [0, 5, -3]
            .into_iter()
            .zip(arms.iter().cycle())
            .chain(arms.iter().enumerate().map(|(n, a)| (n as i64 - 3, a)))
        {
            let t = Term::If(
                Arc::new(ge_i(b)),
                Arc::new(yes.clone()),
                Arc::new(no.clone()),
            );
            for z in &zs {
                for ds in [
                    i_in(-30, 30),
                    over(&[("i", pieces(&[(-30, -20), (-5, 5), (12, 40)]))]),
                ] {
                    diffs.preimage("reflection", &t, &ds, &Demand::Ints(z.clone()));
                }
            }
        }
        // An empty demand on each family.
        for name in ["probe", "alt", "range", "cross", "twoin", "neg", "mul"] {
            for k in [1, 4, 60] {
                let (t, ds, _) = family(name, k);
                diffs.preimage(
                    &format!("empty demand {name} k={k}"),
                    &t,
                    &ds,
                    &Demand::Ints(IntervalSet::empty()),
                );
            }
        }
        diffs.none_but(4000, 0, 2, 0);
    });
}

/// Chains of guarded translations, checked with the interpreter: their preimages are exact,
/// not enumerated, and stop nowhere.
#[test]
fn guarded_translation_chains_match_the_interpreter() {
    let mut rng = Rng::new(2201);
    for _ in 0..120 {
        let mut t = var("x");
        for _ in 0..rng.int(1, 16) {
            let prev = Arc::new(t);
            let g = prim(Prim::Ge, var("x"), int(rng.int(-10, 10)));
            let more = prim(Prim::Add, (*prev).clone(), int(rng.int(-4, 4)));
            t = Term::If(Arc::new(g), prev, Arc::new(more));
        }
        let lo = rng.int(-20, 20);
        let d = ints(lo, lo + rng.int(0, 10));
        let ds = over(&[("x", IntervalSet::of(-15, 15))]);
        let p = preimage(&t, &ds, &d);
        assert!(p.exact && !p.enumerated, "{t}: {p:?}");
        assert!(
            p.stops.is_empty() && p.relation.is_none() && p.refusal.is_none(),
            "{t}: {p:?}"
        );
        check(&t, &ds, &d, &p, (-15, 15));
    }
}

/// [`scaling::check`] on the preimage of a family, its sizes built before they are timed.
fn scales(name: &'static str, n: usize) {
    on_big_stack(|| {
        let (a, b) = (family(name, n), family(name, n * scaling::FACTOR));
        scaling::check(
            &format!("the preimage of the chain family {name}"),
            n,
            |k| {
                let (t, ds, d) = if k == n { &a } else { &b };
                preimage(t, ds, d);
            },
        );
    });
}

#[test]
fn chain_probe_scales() {
    scales("probe", 256);
}

#[test]
fn chain_live_scales() {
    scales("live", 256);
}

/// The probe with `i` over all integers: the arm `t + 1` leaves `i64` at `i = i64::MAX`,
/// where the guard keeps `t`, so the summary checks only the values each arm keeps.
#[test]
fn chain_probe_all_scales() {
    scales("probe_all", 256);
}

/// The probe with `i` over the half-line `[-100, inf)`.
#[test]
fn chain_probe_half_scales() {
    scales("probe_half", 256);
}

/// The probe with `i` in `[-100, 2^62]`: an end of the domain plus an end of the demand met
/// with the hull passes `i64::MAX`, so `Tx::fits` keeps the summary and the clip off and the
/// transfer before runs, at about `k^2.8` (ledger S22-WIDE).
#[test]
#[ignore = "ledger S22-WIDE: the transfer before on a domain end beyond 2^62"]
fn chain_probe_wide_scales() {
    scales("probe_wide", 256);
}

#[test]
fn chain_alt_scales() {
    scales("alt", 256);
}

#[test]
fn chain_cj_scales() {
    scales("cj", 256);
}

#[test]
fn chain_eq0_scales() {
    scales("eq0", 256);
}

#[test]
fn chain_range_scales() {
    scales("range", 256);
}

#[test]
fn chain_gt_scales() {
    scales("gt", 256);
}

#[test]
fn chain_swapped_scales() {
    scales("swapped", 256);
}

#[test]
fn chain_constfirst_scales() {
    scales("constfirst", 256);
}

#[test]
fn chain_sub_scales() {
    scales("sub", 256);
}

#[test]
fn chain_twoin_scales() {
    scales("twoin", 256);
}

#[test]
fn chain_conj_scales() {
    scales("conj", 256);
}

#[test]
fn chain_conj_live_scales() {
    scales("conj_live", 256);
}

#[test]
fn chain_cross_scales() {
    scales("cross", 256);
}

#[test]
fn chain_abs_guard_scales() {
    scales("abs_guard", 256);
}

#[test]
fn chain_ne_guard_scales() {
    scales("ne_guard", 256);
}

#[test]
fn chain_pow2_scales() {
    scales("pow2", 256);
}

#[test]
fn chain_jt_scales() {
    scales("jt", 256);
}

#[test]
fn chain_jt_range_scales() {
    scales("jt_range", 256);
}

/// The chain whose else arms reflect, `j - t`, over `[-k, k]` with `tk` in `[-3, 7]`: each
/// level reflects the demands of the one above about a new constant. The summary reads `c - t`
/// since plan item S22b-rest and inverts the demand once: 10.6 times the instructions at
/// `k` = 256 and 2,048, and 8.8 and 21 ms at 256 and 512. Before, the transfer read the chain
/// level by level: 63.4 times, and 3.36 and 8.64 s at 256 and 512 (load about 85 to 110).
#[test]
fn chain_jt_range_live_scales() {
    scales("jt_range_live", 256);
}

#[test]
fn chain_five_range_live_scales() {
    scales("five_range_live", 256);
}

#[test]
fn chain_min_scales() {
    scales("min", 256);
}

/// `cross` below its domain's width: `m` plus the number of guards `i >= j` that fail, for
/// `j` up to 40 and both inputs in `[-50, 50]`. The transfer's box is inexact, so the
/// preimage asks whether the box can be listed; it cannot (two inputs are ranges), and that is
/// read before `stage::ends`, which walks the term as a tree and so costs `2^40` steps on this
/// chain, whose arms share their term (ledger ENDS-dag).
#[test]
fn a_chain_on_two_inputs_below_its_domains_width_ends() {
    on_big_stack(|| {
        let (t, ds, d) = family("cross", 40);
        let p = preimage(&t, &ds, &d);
        assert!(!p.exact);
        assert_eq!(p.domains["i"], IntervalSet::of(-50, 50));
        assert_eq!(p.domains["m"], IntervalSet::of(-40, 50));
    });
}

/// `3 * t - 1` in every else arm, over `i` in `[-24, -21]` and `[-15, -4]` (and `5` in the
/// `five` cases), where every guard `i >= j` with `j >= 1` fails on the negative inputs, so
/// `t_k = 3^k i - (3^k - 1) / 2`. At `i = -24` that leaves `i64` from `k = 37`, and the
/// transfer rounds there. Its empty preimage of `t_k >= 0` was called inexact for the rounding,
/// so the preimage went on to list the box, and asked `stage::ends`, which walks the shared
/// term as a tree, before it saw that the box is empty: over 60 s at `k = 37`. An empty box is
/// now read as exact before `ends` is asked; it is the one box here that is listed.
#[test]
fn a_chain_that_leaves_i64_keeps_its_exact_preimage() {
    on_big_stack(|| {
        let negative = pieces(&[(-24, -21), (-15, -4)]);
        for k in [36, 37, 38, 40, 64, 256] {
            for (name, want) in [
                ("t3_gaps", IntervalSet::empty()),
                ("t3_gaps_no", negative.clone()),
                ("t3_gaps_five", IntervalSet::of(5, 5)),
                ("t3_gaps_five_no", negative.clone()),
            ] {
                let (t, ds, d) = family(name, k);
                let p = preimage(&t, &ds, &d);
                assert_eq!(p.domains["i"], want, "{name} k={k}: {p:?}");
                assert!(p.exact, "{name} k={k}: {p:?}");
                assert_eq!(p.enumerated, k >= 37 && name == "t3_gaps", "{name} k={k}");
                assert!(
                    p.stops.is_empty() && p.relation.is_none() && p.refusal.is_none(),
                    "{name} k={k}: {p:?}"
                );
                check(&t, &ds, &d, &p, (-30, 30));
            }
        }
    });
}

/// The same chains where they stay in `i64`, compared with the transfer before, which from
/// `k = 37` takes `2^k` steps on `t3_gaps`.
#[test]
fn chains_that_stay_in_i64_keep_their_preimages() {
    on_big_stack(|| {
        let mut diffs = Diffs::default();
        for name in ["t3_gaps", "t3_gaps_no", "t3_gaps_five", "t3_gaps_five_no"] {
            for k in (0..=36).step_by(4).chain([35, 36]) {
                let (t, ds, d) = family(name, k);
                diffs.preimage(&format!("{name} k={k}"), &t, &ds, &d);
            }
        }
        diffs.none(44, 0);
    });
}

/// The chain that leaves `i64`, with no point meeting `t_k >= 0`.
#[test]
fn chain_t3_gaps_scales() {
    scales("t3_gaps", 256);
}

/// The chain that leaves `i64`, with the negative inputs meeting `t_k < 0`.
#[test]
fn chain_t3_gaps_five_no_scales() {
    scales("t3_gaps_five_no", 256);
}

/// COMPLEXITY.md S22e. The chain `mod7`, of eleven guards `i mod 7 == j mod 7` with else arm
/// `t + 1`: each remainder of `i` keeps `t` at one guard in seven, so `t11 = i + 9` for
/// `i mod 7` in 1..4 and `i + 10` otherwise, and `t11 >= 0` holds exactly on `[-9, 50]`. The
/// guard's preimage over `[-50, 50]` spans more than two periods of 7, so the remainder alone
/// is not read exactly (row C17); the transfer reads it class by class of remainders, and
/// finds the preimage exact, with no relation and no refusal.
#[test]
fn a_chain_of_guards_on_remainders_is_read_class_by_class() {
    on_big_stack(|| {
        let (t, ds, d) = family("mod7", 11);
        let p = preimage(&t, &ds, &d);
        assert!(p.exact && !p.enumerated, "{p:?}");
        assert!(p.relation.is_none() && p.refusal.is_none() && p.stops.is_empty());
        assert_eq!(p.domains["i"], IntervalSet::of(-9, 50));
        check(&t, &ds, &d, &p, (-60, 60));
    });
}

/// `t = i + 1` where `keep` holds and `i` elsewhere, asked `t` in `[3, 30]`.
fn by_remainder(keep: Term) -> (Term, Demand) {
    let i = || var("i");
    let t = Term::If(
        Arc::new(keep),
        Arc::new(prim(Prim::Add, i(), int(1))),
        Arc::new(i()),
    );
    (t, ints(3, 30))
}

/// The classes cut by ordered comparisons, by `!=`, by a negative modulus and by constants
/// outside `[0, m)`, and over a domain unbounded on both sides: each preimage is exact and
/// agrees with the interpreter. Over all integers the preimage is `[3, 30]` with `2` added
/// where `i mod m` keeps and `30` dropped there.
#[test]
fn remainders_compared_every_way_are_read_exactly() {
    let r = |m: i64| prim(Prim::Mod, var("i"), int(m));
    let cases = [
        prim(Prim::Lt, r(5), int(2)),
        prim(Prim::Ge, r(5), int(3)),
        prim(Prim::Ne, r(5), int(4)),
        prim(Prim::Gt, int(3), r(5)),
        prim(Prim::Le, int(2), r(-5)),
        Term::Prim(
            Prim::And,
            vec![prim(Prim::Ge, r(6), int(-3)), prim(Prim::Le, r(6), int(9))],
        ),
        Term::Prim(
            Prim::Or,
            vec![prim(Prim::Eq, r(4), int(1)), prim(Prim::Eq, r(4), int(3))],
        ),
    ];
    for keep in cases {
        for ds in [
            i_in(-40, 40),
            over(&[("i", IntervalSet::top())]),
            over(&[("i", pieces(&[(-40, -20), (5, 33)]))]),
        ] {
            let (t, d) = by_remainder(keep.clone());
            let p = preimage(&t, &ds, &d);
            assert!(p.exact, "{t} over {ds:?}: {p:?}");
            check(&t, &ds, &d, &p, (-60, 60));
        }
    }
}

/// Where the split cannot be exact it is given up, and the preimage is the one before: two
/// inputs' remainders compared; another input narrowed differently by class (the union of
/// boxes is not a box); and a stretch where one class keeps its points and another does not
/// that spans many periods.
#[test]
fn a_split_by_remainders_is_given_up_where_it_cannot_be_exact() {
    let i = || var("i");
    let j = || var("j");
    let two = over(&[
        ("i", IntervalSet::of(-30, 30)),
        ("j", IntervalSet::of(-30, 30)),
    ]);
    let both = Term::If(
        Arc::new(prim(
            Prim::Eq,
            prim(Prim::Mod, i(), int(3)),
            prim(Prim::Mod, j(), int(3)),
        )),
        Arc::new(i()),
        Arc::new(j()),
    );
    let other = Term::If(
        Arc::new(prim(Prim::Eq, prim(Prim::Mod, i(), int(3)), int(0))),
        Arc::new(j()),
        Arc::new(prim(Prim::Add, j(), int(1))),
    );
    let wide = Term::If(
        Arc::new(prim(Prim::Eq, prim(Prim::Mod, i(), int(2)), int(0))),
        Arc::new(i()),
        Arc::new(int(0)),
    );
    for (t, ds, d) in [
        (both, two.clone(), ints(0, 10)),
        (other, two, ints(0, 10)),
        (wide, i_in(-1000, 1000), ints(10, 2000)),
    ] {
        let (now, then) = (preimage(&t, &ds, &d), before::preimage(&t, &ds, &old(&d)));
        assert_eq!(format!("{now:?}"), format!("{then:?}"), "{t}");
        check(&t, &ds, &d, &now, (-60, 60));
    }
}

#[test]
fn chain_mod7_scales() {
    scales("mod7", 256);
}

/// The chain of `k` guards `i mod 1024 == j`, else `t + 1`, over `i` in `[-5000, 5000]`, asked
/// `tk >= 0`.
fn many_remainders(k: usize) -> (Term, Domains, Demand) {
    let g = |j: i64| prim(Prim::Eq, prim(Prim::Mod, var("i"), int(1024)), int(j));
    let t = chain(k, var("i"), g, plus(|_| 1));
    (
        prim(Prim::Ge, t, int(0)),
        i_in(-5000, 5000),
        Demand::Bool(true),
    )
}

/// COMPLEXITY.md S22e, the cost of the split: `k` distinct remainders compared cut `2k + 1`
/// classes, and the transfer runs once in each. `tk` is `i + k - 1` where `i mod 1024` is in
/// `1..=k` and `i + k` elsewhere, so the preimage is `[-k, 5000]`.
#[test]
fn remainders_many_classes_cost_one_transfer_each() {
    on_big_stack(|| {
        for k in [1, 2, 7, 40] {
            let (t, ds, d) = many_remainders(k);
            let p = preimage(&t, &ds, &d);
            assert!(p.exact && p.refusal.is_none(), "{p:?}");
            assert_eq!(p.domains["i"], IntervalSet::of(-(k as i64), 5000));
            check(&t, &ds, &d, &p, (-60, 60));
        }
    });
}

/// The chains on two inputs keep the boxes they had before LIN-cross, whose repair of the
/// search over disjunctions changed only its cost: `m` in `[-min(k, 50), 50]` on `cross`, both
/// inputs in `[-k, k]` on `cross_live` and in `[2-k, k-2]` on `cross_dead` (from `k = 5`,
/// where its box stops being exact, to 13, as it costs `k^2.4`: ledger LIN-probe). Each box is
/// inexact with its relation kept, and no point within the interpreter's window meets the
/// demand outside it. Before the change and after, the whole preimage, relation included, was
/// equal on every family of this file (running log, LIN-cross).
#[test]
fn chains_on_two_inputs_keep_their_boxes() {
    on_big_stack(|| {
        for k in [1, 2, 3, 5, 8, 13, 21, 34, 48, 50, 51] {
            for name in ["cross", "cross_live", "cross_dead"] {
                if name == "cross_dead" && !(5..=13).contains(&k) {
                    continue;
                }
                let (t, ds, d) = family(name, k);
                let p = preimage(&t, &ds, &d);
                let what = format!("{name} k={k}");
                let ki = k as i64;
                let (i, m) = match name {
                    "cross" => (IntervalSet::of(-50, 50), IntervalSet::of(-ki.min(50), 50)),
                    "cross_live" => (IntervalSet::of(-ki, ki), IntervalSet::of(-ki, ki)),
                    _ => (
                        IntervalSet::of(2 - ki, ki - 2),
                        IntervalSet::of(2 - ki, ki - 2),
                    ),
                };
                assert_eq!((&p.domains["i"], &p.domains["m"]), (&i, &m), "{what}");
                assert!(!p.exact && p.relation.is_some(), "{what}: {p:?}");
                if k <= 13 {
                    assert!(!refuted(&t, &ds, &d, &p.domains, p.exact), "{what}");
                }
            }
        }
    });
}

#[test]
fn chain_cross_live_scales() {
    scales("cross_live", 32);
}

/// `cross` with every guard inside the inputs' width, so that the relation is asked at both
/// sizes (from `k = 100` on, the transfer's box is exact and the relation is not needed).
#[test]
fn chain_cross_within_its_width_scales() {
    scales("cross", 6);
}

/// `cross_dead` (`cross` with its inputs two narrower than the chain is long) has its only
/// point outside the demand at an end, `i = k - 2` and `m = 2 - k`. The greedy search over
/// disjunctions keeps `i` where the first solution put it and fails, and the search then tests
/// each of the `2k` disjuncts in turn with a full propagation, about `k^2.4` in all (0.26,
/// 1.40, 7.2 and 39.4 G instructions at `k` = 10, 18, 34, 66). The same holds of `cross` from
/// `k = 51` to `99` (22.9 G at 52 against 1.09 G at 48): the jump the ledger reports is the
/// guards `j > 50` that no input meets, not a size where the method changes.
#[test]
#[ignore = "ledger LIN-probe: the failed-literal search on a chain of guards that no input meets"]
fn chain_cross_dead_scales() {
    scales("cross_dead", 8);
}
