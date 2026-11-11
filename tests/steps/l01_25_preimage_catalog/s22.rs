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
use zed_kernel::Shared;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::Congruence;
use zedc::store::preimage::{
    Classes, Demand, Domains, Listed, Preimage, TouchedPaths, class_domain_reads, exact_preimage,
    forward_pieces, preimage, preimage_listed, touched_paths,
};
use zedc::store::preimage_ref as before;
use zedc::store::presburger::{Atom, Formula, Model, Refusal, Relation, member, satisfiable};

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
    IntervalSet::from_pieces(ps.iter().map(|&(a, b)| (End::of(a), End::of(b))).collect())
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
        let t = Shared::new(t);
        let other = arm(j, (*t).clone());
        Term::If(Shared::new(guard(j)), t, Shared::new(other))
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
/// - `probe_wide` and `probe_max`: the probe with `i` in `[-100, 2^62]` and in
///   `[-100, i64::MAX]`;
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
        "probe_max" => (ge0(adds(k, |_| 1)), i_in(-100, i64::MAX), yes),
        "probe_half" => {
            let half = IntervalSet::range(End::of(-100), End::PosInf);
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
                let t = Shared::new(t);
                let more = prim(Prim::Add, (*t).clone(), int(1));
                Term::If(
                    Shared::new(prim(Prim::Lt, var("i"), int(j))),
                    Shared::new(more),
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
                let prev = Shared::new(t);
                let more = prim(Prim::Add, (*prev).clone(), int(1));
                t = Term::If(Shared::new(ge_i(j)), prev, Shared::new(more));
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
/// the cases now exact that the transfer before left inexact, refused or listed (by
/// classes of remainders, COMPLEXITY.md S22e, or by S22b's reflection), and the cases a split
/// over many periods answers with the classes' relation in place of the linear stage's
/// (COMPLEXITY.md S22e-wide), each shown with its box now and before when wider, and the cases
/// that differ only in the names of the variables of their relation or refusal
/// (COMPLEXITY.md S22-transfer-rem), and the exact preimages the transfer before found by
/// listing their points that are now the same set, exact, read without a listing
/// (COMPLEXITY.md F70, PA-plus-if).
#[derive(Default)]
struct Diffs {
    cases: usize,
    found: Vec<String>,
    narrower: usize,
    reflected: usize,
    exact: usize,
    wide: usize,
    wider: Vec<String>,
    renamed: usize,
    unlisted: usize,
}

/// Whether `p`, not exact, holds the relation of a split by remainders over many periods
/// (`x div c` and `x mod c` its only auxiliary variables), and the interpreter finds that the
/// points of the box meeting that relation are those within (-60, 60) that meet `d` under `t`
/// over `ds`: the relation is exact on the box.
fn split_relation_exact(t: &Term, ds: &Domains, d: &Demand, p: &Preimage) -> bool {
    let Some(rel) = &p.relation else {
        return false;
    };
    let [(0, div, _), (1, rem, _)] = &rel.defs[..] else {
        return false;
    };
    let Some((x, c)) = div.split_once(" div ") else {
        return false;
    };
    let c: i64 = c.parse().expect("a modulus is an integer");
    if p.exact || *rem != format!("{x} mod {c}") {
        return false;
    }
    let names: Vec<Arc<str>> = ds.keys().cloned().collect();
    let at = names
        .iter()
        .position(|n| &**n == x)
        .expect("the split input is an input");
    let (defs, body) = (rel.defined(), &rel.body);
    super::points(ds, &names, (-60, 60)).iter().all(|pt| {
        let inside = names.iter().zip(pt).all(|(n, &v)| p.domains[n].contains(v));
        let r = pt[at].rem_euclid(c.abs());
        let mut model: Model = names
            .iter()
            .zip(pt)
            .map(|(n, &v)| (Atom::Sym(n.clone()), Int::from(v)))
            .collect();
        model.insert(Atom::Aux(0), Int::from((pt[at] - r) / c));
        model.insert(Atom::Aux(1), Int::from(r));
        let held = inside && defs.holds(&model) && body.holds(&model);
        held == super::meets(t, &names, pt, d)
    })
}

/// Whether the interpreter refutes `domains` as the preimage of `d` under `t` over `ds` on
/// the points within (-60, 60): a point that meets `d` lies outside, or, when `exact`, a point
/// inside fails `d`.
fn refuted(t: &Term, ds: &Domains, d: &Demand, domains: &Domains, exact: bool) -> bool {
    first_refuted(t, ds, d, &[(domains, exact)]).is_some()
}

/// The index of a box of `boxes` (each a box and whether it is marked exact) that the
/// interpreter refutes as [`refuted`] does, if any. The term runs once at each point, whatever
/// the number of boxes.
fn first_refuted(t: &Term, ds: &Domains, d: &Demand, boxes: &[(&Domains, bool)]) -> Option<usize> {
    let names: Vec<Arc<str>> = ds.keys().cloned().collect();
    super::points(ds, &names, (-60, 60)).iter().find_map(|pt| {
        let meets = super::meets(t, &names, pt, d);
        boxes.iter().position(|&(domains, exact)| {
            let inside = names
                .iter()
                .zip(pt)
                .all(|(n, &v)| domains.get(n).is_none_or(|s| s.contains(v)));
            (meets && !inside) || (!meets && exact && inside)
        })
    })
}

impl Diffs {
    /// Compares the preimage of `d` under `t` over `ds` with the one before. A difference
    /// counts as narrower when only the box differs, both are inexact, and the new box is a
    /// sound subset of the one before; every other difference is found.
    fn preimage(&mut self, what: &str, t: &Term, ds: &Domains, d: &Demand) {
        self.preimage_listed(what, t, ds, &Listed::new(), d);
    }

    /// [`Diffs::preimage`], the names of `listed` having domains the source lists.
    fn preimage_listed(&mut self, what: &str, t: &Term, ds: &Domains, listed: &Listed, d: &Demand) {
        let (now, then) = (
            preimage_listed(t, ds, listed, d),
            before::preimage_listed(t, ds, listed, &old(d)),
        );
        let (new, old) = (format!("{now:?}"), format!("{then:?}"));
        // Every box of both transfers, whether or not the two differ, holds each point that
        // meets the demand, and holds no point that fails it when it is marked exact (item
        // S22-exact-mislabel: ten boxes of the transfer before were marked exact while holding
        // points that fail, and were counted as boxes of `c - x` narrowed, since this was
        // checked only for the new box).
        let boxes = [(&now.domains, now.exact), (&then.domains, then.exact)];
        if let Some(i) = first_refuted(t, ds, d, &boxes) {
            let (which, shown) = [("now", &new), ("before", &old)][i];
            self.cases += 1;
            self.found.push(format!(
                "{what}: {t} over {ds:?}, demand {d:?}\n  the interpreter refutes the box \
                 {which}: {shown}"
            ));
            return;
        }
        // Plan item S22e-wide: a split by remainders over many periods answers with its box and
        // the classes' relation, exact on the box, where the linear stage stated its own
        // relation and projected a box from it. The box is narrower than the projection's in
        // most such cases, and in a few wider (the hull of a class's members joins pieces the
        // projection kept apart, where the relation holds no point); those are listed. Where
        // the split's box is small enough to list ([`enumerate`]), the listing is exact, inside
        // the box before, and equal to it when that was exact.
        let inside = now.domains.iter().all(|(n, s)| {
            let o = &then.domains[n];
            s.pieces()
                .all(|(lo, hi)| o.pieces().any(|(l, h)| l <= lo && hi <= h))
        });
        let listed = now.exact
            && now.enumerated
            && !then.enumerated
            && inside
            && (!then.exact || now.domains == then.domains);
        if new != old && (listed || !then.exact && split_relation_exact(t, ds, d, &now)) {
            self.cases += 1;
            self.wide += 1;
            if !inside {
                let show = |ds: &Domains| {
                    let each = ds.iter().map(|(n, s)| format!("{n} {s}"));
                    each.collect::<Vec<_>>().join(", ")
                };
                self.wider.push(format!(
                    "{} before {}",
                    show(&now.domains),
                    show(&then.domains)
                ));
            }
            return;
        }
        // Item S22-transfer-rem: the linear stage gives one quotient and remainder to every
        // `x mod c` of one input, so the auxiliary variables of a relation and the variables a
        // refusal names are numbered anew. Such a result differs from the one before only in
        // those names: the same box, exactness, listing and stops, a relation where there was
        // one, and a refusal of the same kind.
        let kind = |r: &Option<Refusal>| r.as_ref().map(std::mem::discriminant);
        if new != old
            && now.domains == then.domains
            && now.exact == then.exact
            && now.enumerated == then.enumerated
            && format!("{:?}", now.stops) == format!("{:?}", then.stops)
            && now.relation.is_some() == then.relation.is_some()
            && kind(&now.refusal) == kind(&then.refusal)
        {
            self.cases += 1;
            self.renamed += 1;
            return;
        }
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
                .all(|(lo, hi)| o.pieces().any(|(l, h)| l <= lo && hi <= h))
        };
        if new != old
            && !now.exact
            && rest!(now) == rest!(then)
            && now.domains.keys().eq(then.domains.keys())
            && now.domains.iter().all(|(n, s)| inside(s, &then.domains[n]))
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
        {
            self.cases += 1;
            self.exact += 1;
            return;
        }
        // Plan item S22b: the transfer before takes `c - x` as the forward image of `{c} - z`,
        // whose cap merges pieces moved across zero, so its box may be wider. The new result
        // lies inside the one before and is exact wherever the one before was. Until item
        // S22-exact-mislabel the box before was marked exact even when the cap had merged
        // pieces; now it is not, the linear stage narrows it, and no case of these tests
        // counts here.
        if new != old
            && (now.exact || !then.exact)
            && now.domains.keys().eq(then.domains.keys())
            && now.domains.iter().all(|(n, s)| inside(s, &then.domains[n]))
        {
            self.cases += 1;
            self.reflected += 1;
            return;
        }
        self.note(what, t, ds, d, new, old);
    }

    /// Compares the exact preimage of `d` under `t` over `ds` and `cs` with the one before.
    fn exact(&mut self, what: &str, t: &Term, ds: &Domains, cs: &Classes, d: &Demand) {
        let now = exact_preimage(t, ds, cs, d);
        let then = before::exact_preimage(t, ds, cs, &old(d));
        // Item PA-plus-if: the summary reads a sum of two summaries of one input, so a preimage
        // the transfer before found exact by listing its points is read exact without a
        // listing. The set, the stops, the relation and the refusal are those before.
        let rest = |e: bool,
                    s: &dyn std::fmt::Debug,
                    r: &dyn std::fmt::Debug,
                    f: &dyn std::fmt::Debug| format!("{e:?} {s:?} {r:?} {f:?}");
        if now.domains == then.domains
            && now.exact
            && !now.enumerated
            && then.enumerated
            && rest(now.exact, &now.stops, &now.relation, &now.refusal)
                == rest(then.exact, &then.stops, &then.relation, &then.refusal)
        {
            self.cases += 1;
            self.unlisted += 1;
            return;
        }
        let (new, old) = (format!("{now:?}"), format!("{then:?}"));
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
        assert_eq!(self.wide, 0, "a split over many periods answered");
        assert_eq!(
            self.renamed, 0,
            "a result differs from the one before only in the names of its variables"
        );
        assert_eq!(
            self.unlisted, 0,
            "an exact preimage listed before is read without a listing"
        );
    }

    /// Checks that a split over many periods answered `wide` cases with the classes'
    /// relation, and that the ones whose box is wider than the one before are `wider`, each its
    /// box now and before.
    fn split_wide(mut self, wide: usize, wider: &[&str]) -> Diffs {
        assert_eq!(
            self.wide, wide,
            "the number of splits over many periods changed"
        );
        assert_eq!(
            self.wider, wider,
            "the wider boxes of splits over many periods"
        );
        self.wide = 0;
        self
    }

    /// Checks that `renamed` results differ from the one before only in the names of the
    /// variables of their relation or refusal (item S22-transfer-rem).
    fn renamed(mut self, renamed: usize) -> Diffs {
        assert_eq!(
            self.renamed, renamed,
            "the number of results that differ only in the names of their variables changed"
        );
        self.renamed = 0;
        self
    }

    /// Checks that `unlisted` exact preimages the transfer before found by listing their points
    /// are the same set, read without a listing (item PA-plus-if).
    fn unlisted(mut self, unlisted: usize) -> Diffs {
        assert_eq!(
            self.unlisted, unlisted,
            "the number of exact preimages read without the listing before changed"
        );
        self.unlisted = 0;
        self
    }
}

/// A random domain of `i`: all integers, a half-line, or one to three intervals apart.
fn chain_domain(rng: &mut Rng) -> IntervalSet {
    match rng.below(6) {
        0 => IntervalSet::top(),
        1 => IntervalSet::range(End::of(rng.int(-20, 5)), End::PosInf),
        2 => IntervalSet::range(End::NegInf, End::of(rng.int(-5, 20))),
        _ => {
            let mut lo = rng.int(-25, -5);
            let mut ps = Vec::new();
            for _ in 0..rng.int(1, 3) {
                let hi = lo + rng.int(0, 12);
                ps.push((End::of(lo), End::of(hi)));
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
        let shared = Shared::new(t);
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
        t = Term::If(Shared::new(g), Shared::new(a), Shared::new(b));
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
        2 => (t, Demand::Ints(IntervalSet::range(End::NegInf, End::of(a)))),
        3 => (t, Demand::Ints(IntervalSet::range(End::of(a), End::PosInf))),
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

/// The families whose constants grow with the chain (`c_j = j`), at the sizes above, one test
/// per family so that each runs in well under 60 s; the cases, 68 + 72 + 68 + 72, are the 280
/// of the one test they were.
#[test]
fn chains_of_growing_constants_keep_their_preimages_cj() {
    chain_families(&[("cj", &[])], 68);
}

#[test]
fn chains_of_growing_constants_keep_their_preimages_cj_live() {
    chain_families(&[("cj_live", &[24])], 72);
}

#[test]
fn chains_of_growing_constants_keep_their_preimages_altj() {
    chain_families(&[("altj", &[])], 68);
}

#[test]
fn chains_of_growing_constants_keep_their_preimages_altj_live() {
    chain_families(&[("altj_live", &[24])], 72);
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
        // 0, was 7: CANON-stable (the solver takes the variables and rows breadth first in the
        // order of their stable colors, and the transfer before shares it) stopped `mod7` at
        // k = 3 to 8 from being refused by its shadows, and LIVE3 (the Omega test decides three
        // live variables) did the same for `mod7 k=2`, so both are exact and alike there.
        diffs.none_but(83, 0, 0, 0);
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
                let prev = Shared::new(t);
                let g = ge_i(rng.int(-25, 25));
                let c = rng.int(-6, 6);
                let more = if rng.below(10) == 0 {
                    prim(Prim::Sub, (*prev).clone(), int(-c))
                } else {
                    prim(Prim::Add, (*prev).clone(), int(c))
                };
                t = Term::If(Shared::new(g), prev, Shared::new(more));
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
/// is `{-10} | [1, 3] | {10}`. Both boxes held every point that meets the demand. The transfer
/// before cannot be kept on such demands without reading both the met and the whole demand at
/// each term, which doubles the demands per level.
///
/// Since PA-plus-if, `x + x` has a summary (the sum of two summaries of one input), which is
/// inverted in place of the map2 cap, so the preimage is now that true set, exact; the box
/// before is as it was. The narrower kind of difference is still met in
/// [`random_terms`] (6 cases).
#[test]
fn meeting_a_demand_with_the_hull_may_narrow_a_box_the_map2_cap_widened() {
    let i = || var("i");
    let abs = || Term::Prim(Prim::Abs, vec![i()]);
    let x = Term::If(
        Shared::new(prim(Prim::Ge, abs(), int(10))),
        Shared::new(prim(Prim::Sub, int(-5), i())),
        Shared::new(prim(Prim::Sub, int(6), i())),
    );
    let t = Term::If(
        Shared::new(prim(Prim::Ge, abs(), int(3))),
        Shared::new(prim(Prim::Mul, int(2), x.clone())),
        Shared::new(prim(Prim::Add, x.clone(), x)),
    );
    let ds = over(&[("i", IntervalSet::range(End::NegInf, End::of(12)))]);
    let d = Demand::Ints(pieces(&[(-30, -29), (6, 10)]));
    let (now, then) = (preimage(&t, &ds, &d), before::preimage(&t, &ds, &old(&d)));
    assert!(now.exact && !then.exact);
    assert_eq!(now.domains["i"], pieces(&[(-10, -10), (1, 3), (10, 10)]));
    assert_eq!(then.domains["i"], pieces(&[(-10, -10), (-2, 10)]));
    assert!(!refuted(&t, &ds, &d, &now.domains, true));
    let mut diffs = Diffs::default();
    diffs.preimage("the narrowed case", &t, &ds, &d);
    assert_eq!((diffs.cases, diffs.exact, diffs.found.len()), (1, 1, 0));
}

/// Every kind of guard and arm the summary reads, and some it does not: the cases `from..to`
/// of one sequence, split in tests of 250 cases each ([`GUARDED`]) so they run in parallel.
fn random_guarded_chains(
    from: usize,
    to: usize,
    (narrower, reflected, exact): (usize, usize, usize),
    (wide, wider): (usize, &[&str]),
    renamed: usize,
) {
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
        diffs.split_wide(wide, wider).renamed(renamed).none_but(
            to - from,
            narrower,
            reflected,
            exact,
        );
    });
}

/// The counts of each test of [`random_guarded_chains`]: the first case of its 250, the
/// narrower, reflected and exact boxes, and the splits over many periods with the wider of
/// them, and the results that differ only in the names of their variables. The rows of each
/// half sum to that half's counts as one test
/// (`random_guarded_chains_sum_to_the_counts_of_each_half`).
type Counts = (
    usize,
    (usize, usize, usize),
    (usize, &'static [&'static str]),
    usize,
);

const GUARDED: [Counts; 16] = [
    (0, (0, 0, 44), (10, &[]), 0),
    (
        250,
        (0, 0, 32),
        (
            9,
            &["i [..=-12, -9..=-9, -5..] before i [..=-11, -9..=1, 3..]"],
        ),
        0,
    ),
    (
        500,
        (0, 0, 39),
        (8, &["i [..=0] before i [..=-5, -3..=0]"]),
        0,
    ),
    (750, (0, 0, 32), (11, &[]), 0),
    (
        1000,
        (0, 0, 48),
        (
            14,
            &["i [-10..=-10, -7..=-6, -4..=-4, -2..] before i [-10..=7, 9..]"],
        ),
        0,
    ),
    (
        1250,
        (0, 0, 45),
        (4, &["i [-7..] before i [..=-6, -4..]"]),
        0,
    ),
    (
        1500,
        (0, 0, 36),
        (
            12,
            &[
                "i [..=0, 6..=7, 9..=10, 12..=13, 15..=16, 18..=18] before i [..=-11, -9..=0, 3..=4, 6..=18]",
                "i [-10..] before i [-10..=9, 11..]",
            ],
        ),
        0,
    ),
    (1750, (0, 0, 40), (13, &[]), 0),
    (
        2000,
        (0, 0, 40),
        (17, &["i [1..] before i [1..=4, 7..]"]),
        0,
    ),
    (
        2250,
        (0, 0, 39),
        (15, &["i [3..] before i [3..=6, 9..]"]),
        0,
    ),
    (2500, (0, 0, 39), (10, &[]), 0),
    (2750, (0, 0, 42), (5, &[]), 0),
    (
        3000,
        (0, 0, 43),
        (10, &["i [-19..] before i [-19..=2, 5..=5, 8..=8, 11..]"]),
        0,
    ),
    (3250, (0, 0, 38), (7, &[]), 0),
    (3500, (0, 0, 38), (5, &[]), 0),
    (
        3750,
        (0, 0, 45),
        (
            11,
            &[
                "i [2..] before i [2..=2, 5..]",
                "i [4..] before i [4..=5, 7..]",
                "i [..=-2, 0..=0, 2..] before i [..=0, 2..=8, 10..]",
            ],
        ),
        0,
    ),
];

/// One test per row of [`GUARDED`], each under 60 s at load 120.
macro_rules! guarded_ranges {
    ($($name:ident $row:literal),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                let (from, counts, wide, renamed) = GUARDED[$row];
                random_guarded_chains(from, from + 250, counts, wide, renamed);
            }
        )*
    };
}

guarded_ranges!(
    random_guarded_chains_keep_their_preimages_0000 0,
    random_guarded_chains_keep_their_preimages_0250 1,
    random_guarded_chains_keep_their_preimages_0500 2,
    random_guarded_chains_keep_their_preimages_0750 3,
    random_guarded_chains_keep_their_preimages_1000 4,
    random_guarded_chains_keep_their_preimages_1250 5,
    random_guarded_chains_keep_their_preimages_1500 6,
    random_guarded_chains_keep_their_preimages_1750 7,
    more_random_guarded_chains_keep_their_preimages_2000 8,
    more_random_guarded_chains_keep_their_preimages_2250 9,
    more_random_guarded_chains_keep_their_preimages_2500 10,
    more_random_guarded_chains_keep_their_preimages_2750 11,
    more_random_guarded_chains_keep_their_preimages_3000 12,
    more_random_guarded_chains_keep_their_preimages_3250 13,
    more_random_guarded_chains_keep_their_preimages_3500 14,
    more_random_guarded_chains_keep_their_preimages_3750 15,
);

/// The rows of [`GUARDED`] cover cases 0 to 4000 of the sequence, one after another, and the
/// rows of each half sum to the counts below.
///
/// The first half, cases 0 to 2000: S22e-wide changes 87 cases here: 40 more are made exact
/// (79, against 39 on main) by the split over many periods, where its projection lists the
/// periods and every member lies in its class (`covers`), one of them a box main narrowed
/// (narrower 2 before, 1 now); and 47 are inexact boxes with the classes' relation, exact on
/// the box (`split_relation_exact`), where main ran the linear stage.
///
/// The second half, cases 2000 to 4000: S22b changes 7 boxes of `c - x` here; two of them,
/// inexact before and exact now, count as made exact (on main 53 by classes of remainders,
/// S22e, and 2 by S22b; S22e-wide makes 44 more exact, 99 in all, one of them a box S22b
/// reflected, so reflected counts 4, not 5): the chains `(if (6 < i) { (if (7 < i) { (0 - …`
/// and `if ((i mod 3) == 1) { min(if (i >= -9) { …`, whose results are the same on main before
/// S22e merged (5adc3c2). 53, was 54, since LIVE3: the transfer before, which shares the
/// solver, now decides by `live3` the gray shadow over three variables that left it inexact on
/// `(if ((i mod 3) == 2) { (if ((i mod 3) == 2) { (i + 0) } … < 6)`, so both are exact and
/// alike. S22e-wide answers 49 more with the classes' relation, exact on the box; on main
/// three of those boxes were wider than the transfer before, because the hull of a class's
/// members joins pieces that its projection kept apart, where the relation holds no point.
///
/// Since NAME-ties, which eliminates variables of one color a batch at a time and answers
/// formulas whose atoms share a color without a search by name, 18 more boxes are exact in
/// the first half (97) and 15 more in the second (114), and no box is wider than the
/// transfer before. One box of cases 3250 to 3500, exact on main, is an inexact box narrower
/// than the transfer before (narrower 1), and sound.
///
/// 96, was 97, since DISJ-incremental: the transfer before, which shares the solver, now decides
/// the question of its box of `if ((i mod 3) == 1) { -(if (i == 0) { … }) } else { -6 * … }`
/// over `{-5} ∪ [-2, 1]` (no point of the box fails the demand), which the search through the
/// disjunctions refused, so both are exact and alike (cases 500 to 750).
///
/// Since PRODUCT-nested-chain, which summarizes the sum or difference of two lines of one
/// input (`i + i`, `(i + 1) - 2 * i`) as a line, more preimages are read by the summary and
/// fewer by the linear stage: in the first half 66 more boxes are exact (162), 8 more are
/// answered by a split over many periods or listed (55), 5 more are narrower inexact boxes
/// (6) and 3 more boxes of `c - x` are narrowed (9); in the second half 77 more are exact
/// (191), 9 more answered by a split (58), 4 more narrower (5) and 3 more of `c - x`
/// narrowed (7). Each is checked against the interpreter, none differs otherwise, and none
/// is wider. Measured on main 62ea3f02, cases 3500 to 3750 had one more exact box (26); on
/// main 6532d51e the transfer before decides it too (DISJ-incremental, as at cases 500 to
/// 750), so both are exact and alike (inferred from the count; the case was not isolated).
///
/// Since S22-transfer-rem, which gives one quotient and remainder to every `x mod c` of one
/// input in the linear stage, 58 results differ from the transfer before only in the names of
/// the variables of their relation or refusal (32 in the first half, 26 in the second), and
/// four are better than on main: one inexact box of cases 1500 to 1750 is exact (97 made
/// exact in the first half, was 96); one of cases 1000 to 1250 keeps its box and relation, but
/// the linear stage decides it where it refused before (reflected 7, was 6); and two boxes of
/// the second half are narrower, `[2, +inf)` for `[-1, +inf)` and `[-22, 18]` for `[-43, 18]`,
/// which count as reflected since their relation changed too (6, was 4).
///
/// With PRODUCT-nested-chain and S22-transfer-rem merged together (batch 17), the four boxes
/// S22-transfer-rem improved are improved by PRODUCT-nested-chain's summary already, so the
/// narrower, reflected, exact and split counts are PRODUCT-nested-chain's, and 49 results
/// differ from the transfer before only in the names of their variables (26 in the first
/// half, 23 in the second), measured by the run of each row.
///
/// Since S22-linear-rem, which writes an `if` on the remainder of an input by its summaries
/// over the remainder's classes in the linear stage, one variable for every copy of such an
/// `if`, no box is wider than before and none is less exact: 4 more boxes are exact in each
/// half (166 and 195); 11 more in the first half and 8 more in the second count as
/// reflected (20 and 15), each an inexact box narrower than before or the same box with the
/// refusal gone, its relation changed; one more case in each half is answered by a split
/// over many periods (56 and 59); and 26 and 22 results differ only in the names of their
/// variables, measured by the run of each row.
///
/// Since PA-plus-if, which summarizes the sum or difference of any two summaries of one input
/// (an `if` among them, `x + x` with `x` an `if`) and inverts such a sum where the transfer
/// projected it, the summary reads most of what the linear stage read. Against the counts of
/// S22-linear-rem: in the first half 213 more boxes are exact (379), 25 more are answered by
/// a split over many periods or listed (81), narrower 0 (was 6) and reflected 6 (was 20); in
/// the second half 222 more are exact (417), 21 more answered by a split (80), narrower 0
/// (was 5) and reflected 4 (was 15). The counts are the same as on main before S22-linear-rem
/// merged: the cases it changed are read by the summary here. The cases that left the
/// narrower and reflected counts were not traced one by one; every case of a row is in one
/// of its counts. No result differs from the one before only in the names of its variables
/// any more (renamed 0, was 26 and 22): those were results of the linear stage, which is no
/// longer run on them. Each is checked against the interpreter, none differs otherwise, and
/// none is wider.
///
/// Since DISJ-dpll, which removes each disjunct that the base and the rows the disjunctions
/// imply show empty before the hulls are tightened, four results of the transfer before,
/// which shares the solver, are better; no new result changes. Three inexact boxes before
/// are now exact and equal to the new result, so they leave the exact count (378, was 379, in
/// the first half; 415, was 417, in the second): `if (i <= -7) { min(i, 2) } else { (i + i) }`
/// (cases 250 to 500), `if (4 < i) { (i + i) } else { (i * 1) }` (cases 3250 to 3500) and
/// `if (i == 6) { … } else { if (-8 < i) { (-6 * i) } else { (i + i) } }` (cases 3500 to 3750),
/// each of which had kept a half-line its disjunctions leave empty. In the fourth, the
/// demand false of `(if ((i mod 3) == 1) { … } else { min(…, -4) } < 2)` (cases 3750 to
/// 4000), the box before is `i [4..=5, 7..]` where it was `i [3..]`, narrower than the split
/// over many periods' `i [4..]`, which is now listed as wider; the split's relation is exact
/// on its box. Each changed box holds every point that meets the demand and, where exact, no
/// point that fails it, over `-60..=60`. Measured on main 5b0aee39 against the rebased branch
/// over all 4000 cases.
///
/// Since PROJECT-each-canon, which writes each equation with its first coefficient positive
/// before a projection, so that the answer does not depend on the sign it was written with,
/// and removes the disjuncts with no point jointly before the greedy search, the transfer now
/// gives the same result as on main in all 4000 cases; the transfer before, which shares the
/// solver, differs in 18: 12 boxes narrower (6 of them now exact) and 6 wider (3 of them no
/// longer exact), each sound. So the first half counts as many boxes made exact as on main
/// (378), the second 3 fewer (412). Of cases 3750 to 4000, the box before of `i [2..]` is now
/// `i [2..=2, 5..]` where it was `i [0..]`, so the split over many periods is listed as wider.
///
/// Since PROJECT-canon-gcd, which divides each row by the gcd of its coefficients, one more
/// box of the transfer before, which shares the solver, is exact, in cases 250 to 500 (379,
/// was 378); no result of the transfer changes.
///
/// Since PROJECT-hull-credit-lower, which removes before a projection each disjunct whose own
/// rows put a form outside the values the other disjunctions leave it, two inexact boxes of
/// the transfer are exact and narrower than the transfer before: in cases 750 to 1000,
/// `if (abs(i) >= 5) { … }` with demand `[7, 22]` gives `i` in `[-4, -3] ∪ [-1, 0]`, where the
/// transfer before kept `(-inf, -3] ∪ [-1, +inf)`; in cases 3500 to 3750,
/// `if ((i mod 3) == 1) { … }` with demand `[-15, -13] ∪ [-9, -6]` gives `i` in `{0, 3}`, where
/// the transfer before keeps `{0} ∪ [2, 3]` (at 2 the chain gives -12). So the first half
/// counted 380 made exact, the second 413; both boxes hold no point the interpreter refutes.
///
/// Since PRES-pendants-wider, which tightens a hull end whose other end is infinite and reads
/// the bounds that rows give each other, the transfer before, which shares the solver, gives
/// 21 of the boxes counted as made exact exactly as the transfer does, 5 in the first half
/// (375) and 16 in the second (397): `(-inf, 7]` becomes `[-9, 7]`, `(-inf, 4]` becomes
/// `{2}`, `[-6, -6] ∪ [11, +inf)` becomes the exact `{-6}`, in cases 500 to 750 the box `{3}`
/// of `if (i != 3) { … }` with demand `[-13, 0] ∪ [20, 22]` loses its relation and is exact
/// (at 3 the chain gives -2, elsewhere 4 or 6), and the first case above
/// `(-inf, -3] ∪ [-1, 0]`, still inexact. Every changed box lies inside the one before, and
/// the interpreter refutes none on the points within (-60, 60); no result of the transfer
/// changes.
///
/// Since PRES-small-point, which gives the solver each atom that propagation fixed replaced
/// by its value, the transfer before, which shares the solver, gives 2 of the boxes counted
/// as made exact exactly as the transfer does, one in each half (374 and 396). Both are the
/// empty box, exact: in cases 500 to 750, `if (i != -2) { … }` with demand `[18, 27]`, and in
/// cases 2250 to 2500, `if (i != 3) { min(…, 2) } else { … }` with demand `[26, 35]`, where
/// the transfer before kept `{-2}` and `{3}`, inexact, with a relation, since the solver
/// refused the formula (`Unordered`: two copies of one subterm with the same rows); with the
/// guard's value replaced it shows the formula has no point. The transfer's own results do
/// not change in any case; the transfer before loses that refusal in 5 more cases, still
/// inexact with a relation and the same box.
///
/// Since PRES-nest-empty, whose `settle_tied` first tests the base with the rows the
/// disjunctions imply and answers that the formula has no point when they have none, before
/// two copies of one subterm with the same rows stop it (`Unordered`), the transfer before,
/// which shares the solver, gives one more of the boxes counted as made exact exactly as the
/// transfer does (cases 0 to 250: 52, was 53; first half 373). It is case 86,
/// `if (i != -5) { min(…, -1) } else { (-3 * if (i <= -4) { (0 - …) } else { … }) }` over
/// `[-21, -12] ∪ [-6, 0] ∪ [4, 12]` with demand `[13, 16]`: the transfer gives the empty box,
/// exact, before and after the change; the transfer before kept `{-5}`, inexact, with a
/// relation, since the solver refused at `i = -5` on the copies `q4`, `q5` of
/// `if ((i mod 3) == 1) { min(i, 1) } else { (i + i) }`. Their implied rows
/// `-10 <= q4, q5 <= -5` put `q4 + q5` in `[-20, -10]` and the result `-3 * -(q4 + q5)` in
/// `[-60, -30]`, outside `[13, 16]`, so the solver now shows the formula empty (at -5 the chain
/// gives -30). The one other case of this row the new test answers, case 118, keeps its result
/// (empty, exact, made exact); the box before narrows from `[-16, 5]` to `[-15, 5]`, still inexact.
/// No other row changes. Measured on the branch rebased on main 501a3330: with the new test
/// of `settle_tied` turned off, the row counts 53 again and case 86 is refused as before.
///
/// Since PROJECT-canon-precision, which tests each disjunct for a point whether or not the
/// greedy search found one first, so that a disjunct with no point no longer widens the hulls
/// by an amount the order of the parts decides, the transfer before, which shares the solver,
/// gives 8 of the boxes counted as made exact exactly as the transfer does, 5 in the first half
/// (368) and 3 in the second (393): `i [-4, -3] ∪ {0, 4}` becomes the exact `{-4, 0, 4}`,
/// `[-6, -3]` the exact `[-6, -5] ∪ {-3}`, `[-5, -4] ∪ [-1, 1]` the exact `{-5, 1}`. In 5
/// more cases the box before is now narrower than the box of a split over many periods, which
/// is listed as wider (rows 500, 1500, 2250, 3000 and 3750), its relation still exact on its
/// box: `i [3..]` against `i [3..=6, 9..]` before. In 10 more the box before narrows and stays
/// inexact. Two boxes before, both inexact, gain one point with no solution: in row 1750
/// `[-17, -7] ∪ {4}` becomes `[-17, -7] ∪ {-1} ∪ {4}`, the domain `[-17, -7] ∪ [-1, 1] ∪ [3, 7]`
/// being a set of values of `i` kept untested (`one_atom_set`), and in row 3000
/// `[-13, -9] ∪ [7, 13]` gains `{-5}` the same way. The interpreter refutes no box; no box of
/// the transfer here changes. Measured against the change with the old call (the probe only on a
/// failed search) over all 4000 cases.
///
/// Since PROJECT-box-half-open, which merges the atoms a formula defines alike before a tied
/// projection (the transfer before writes a shared subterm once at each place it is used, and
/// the twins left its questions refused, `Unordered`), the transfer before, which shares the
/// solver, gives 122 of the boxes counted as made exact exactly as the transfer does, 52 in the
/// first half (316) and 70 in the second (323). In 5 more cases the box before is now narrower
/// than the box of a split over many periods, which is listed as wider (rows 250, 1000, 1250,
/// 1500 and 2000), its relation still exact on its box: `i [1..]` against `i [1..=4, 7..]`
/// before. No other count changes, no box of the transfer here changes, and over all 4000 cases
/// no box before is wider than without the change or leaves out a point the interpreter finds.
///
/// Since S22-exact-mislabel, which marks a box of `c - x` before exact only when `x` takes no
/// value of the forward image of `{c} - z` outside the reflection of `z`, the ten boxes counted
/// as reflected (cases 366, 463, 482, 1264, 1420, 1930, 2087, 2314, 3817 and 3897) are no
/// longer exact before; each held points that fail the demand (case 3897 the 17 inputs -25 to
/// -9), which [`Diffs::preimage_listed`] now checks for both boxes. The new box, exact, counts
/// as made exact. One more box before, exact and right, is now inexact: in a case of row 250
/// the arm `(0 - A)` of `if (i == 7) { -(A) } else { (0 - A) }` has a hole `{4}` that
/// `A` reaches only at `i == 7`, where the guard excludes it, and the check at `c - x` does
/// not see the guard; the new box counts as made exact. So made exact gains 4 in row 250, 2 in
/// rows 1250 and 3750, 1 in rows 1750, 2000 and 2250 (323 in the first half, 327 in the
/// second), and reflected counts none. No box of the transfer here changes, no box before is
/// wider, and every other answer before is the same.
///
/// Since S22-guard-exact, which carries the holes of each `c - x` down as doubted values of
/// `x` and meets the inputs that take them with the boxes of the enclosing guards, that box of
/// row 250 (case 263) is exact again. Its hole is not at `(0 - A)`, as said above, but at the
/// `(2 - i)` of `if (i == -7) { i } else { (2 - i) }` inside `A`, read in the arm taken where
/// `i <= 4` fails: the hole `{2}` doubts the input `i = 2`, which that guard removes. The
/// interpreter agrees with the exact box at all 25 points of the domain. So made exact is 34
/// in row 250 (322 in the first half). Over all 4000 cases and the other tests of this file no
/// other answer before changes.
///
/// Since PERF-s22-const-chain, whose linear stage before decides the one point the transfer
/// doubts with the rest of the formula and, where that point fails the demand, gives the box
/// without it, exact, seven inexact boxes before are now exact and equal to the box of the
/// transfer, so they leave the made-exact count (317 in the first half, 325 in the second).
/// Each loses one point: in row 250, `i` over `[-18, +inf)` with demand true loses -5 and
/// over `(-inf, 18]` with demand true loses 4; in row 1250, `[-15, -4] ∪ [1, 4] ∪ [10, 18]`
/// with demand false loses -4 and `[-5, +inf)` with demand true loses 2; in row 1750,
/// `[-14, +inf)` with demand false loses -10, where the linear stage refused before; in row
/// 2000, `[-6, -2]` with demand true loses -5; in row 3750, the box `[-8, -5] ∪ [-1, 0]` over
/// `[-15, -14] ∪ [-10, -5] ∪ [-2, 0]` with demand `[-17, -4] ∪ [7, 12]` loses -5. The
/// interpreter refutes none of them on the points within (-60, 60); no box of the transfer
/// changes, and over all 4000 cases and the other tests of this file no other answer before
/// changes but these same cases in `reversed_parts_give_the_same_boxes_*` and one box of
/// `ends_of_i64_and_other_corners_keep_their_preimages`.
///
/// Since PROJECT-abs-chain-quadratic, which removes at once the disjuncts the bounds of
/// single atoms leave without a point, the transfer before, which shares the solver, gives 2
/// more of the boxes counted as made exact exactly as the transfer does, one in each half
/// (316 in the first and 324 in the second, with the seven of PERF-s22-const-chain): case 1084,
/// demand `[-23, -11] ∪ [3, 10]` on `if ((i mod 3) == 0) { min(…, -6) } else { min(…, -3) }`,
/// whose box before narrows from `{9}`, inexact with a relation, to the
/// exact empty box, and case 2695, `if ((i mod 3) == 1) { min(…, 1) } else { (4 - …) }` with
/// demand `(-inf, -9] ∪ [18, 33]`, from `[-4, 1]`, inexact, to the exact `[-4, -3]`. One more
/// box before narrows and stays inexact, `i <= -20 || i >= 3` to `i <= -21 || i >= 3`
/// (`i = -20` has no point), so no count moves for it. No other count changes and no box of
/// the transfer here changes.
#[test]
fn random_guarded_chains_sum_to_the_counts_of_each_half() {
    let sum = |rows: &[Counts]| {
        let mut s = (0, 0, 0, 0, Vec::new(), 0);
        for &(_, (narrower, reflected, exact), (wide, wider), renamed) in rows {
            s = (
                s.0 + narrower,
                s.1 + reflected,
                s.2 + exact,
                s.3 + wide,
                s.4,
                s.5 + renamed,
            );
            s.4.extend_from_slice(wider);
        }
        s
    };
    for (row, &(from, ..)) in GUARDED.iter().enumerate() {
        assert_eq!(from, 250 * row, "row {row} does not follow the one before");
    }
    assert_eq!(
        sum(&GUARDED[..8]),
        (
            0,
            0,
            316,
            81,
            vec![
                "i [..=-12, -9..=-9, -5..] before i [..=-11, -9..=1, 3..]",
                "i [..=0] before i [..=-5, -3..=0]",
                "i [-10..=-10, -7..=-6, -4..=-4, -2..] before i [-10..=7, 9..]",
                "i [-7..] before i [..=-6, -4..]",
                "i [..=0, 6..=7, 9..=10, 12..=13, 15..=16, 18..=18] before i [..=-11, -9..=0, 3..=4, 6..=18]",
                "i [-10..] before i [-10..=9, 11..]",
            ],
            0
        )
    );
    assert_eq!(
        sum(&GUARDED[8..]),
        (
            0,
            0,
            324,
            80,
            vec![
                "i [1..] before i [1..=4, 7..]",
                "i [3..] before i [3..=6, 9..]",
                "i [-19..] before i [-19..=2, 5..=5, 8..=8, 11..]",
                "i [2..] before i [2..=2, 5..]",
                "i [4..] before i [4..=5, 7..]",
                "i [..=-2, 0..=0, 2..] before i [..=0, 2..=8, 10..]",
            ],
            0
        )
    );
}

/// A run of random terms: `Mixed` runs `cases` terms of depth 3 from `seed`, tests (asked true
/// or false) where `test` holds, from seed 777 on only in every other case, and integer terms
/// with a random demand otherwise, each third term reading through calls where `calls` holds,
/// over random domains, some listed; `Deep` runs 200 terms of depth 4, each a test or an
/// integer term at random; `Exact` runs 250 terms under `@exact` over bounded boxes, `x` in a
/// random class one case in three.
#[derive(Clone, Copy)]
pub(super) enum Run {
    Mixed {
        seed: u64,
        cases: usize,
        test: bool,
        calls: bool,
    },
    Deep {
        seed: u64,
    },
    Exact {
        seed: u64,
        test: bool,
    },
}

/// The runs of [`random_terms`]: the seeds of `random.rs` and others.
pub(super) const RUNS: [Run; 18] = {
    use Run::{Deep, Exact};
    const fn mixed(seed: u64, cases: usize, test: bool, calls: bool) -> Run {
        Run::Mixed {
            seed,
            cases,
            test,
            calls,
        }
    }
    [
        mixed(25, 250, false, false),
        mixed(2025, 250, true, false),
        mixed(7, 400, false, true),
        mixed(77, 400, true, true),
        mixed(777, 1500, false, true),
        mixed(31337, 1500, true, true),
        Deep { seed: 1000 },
        Deep { seed: 1001 },
        Deep { seed: 1002 },
        Deep { seed: 1003 },
        Deep { seed: 1004 },
        Deep { seed: 1005 },
        Deep { seed: 1006 },
        Deep { seed: 1007 },
        Deep { seed: 1008 },
        Deep { seed: 1009 },
        Exact {
            seed: 7,
            test: false,
        },
        Exact {
            seed: 77,
            test: true,
        },
    ]
};

/// One case of a [`Run`]: the term, its inputs' domains, the names whose members the source
/// lists, the inputs' classes under `@exact` (an `Exact` run only), and the demand.
pub(super) struct Case {
    pub what: &'static str,
    pub term: Term,
    pub domains: Domains,
    pub listed: Listed,
    pub classes: Option<Classes>,
    pub demand: Demand,
}

/// Calls `each` on every case of `run`, in order.
pub(super) fn cases(run: Run, mut each: impl FnMut(Case)) {
    match run {
        Run::Mixed {
            seed,
            cases,
            test,
            calls,
        } => {
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
                let (ds, listed) = domains(&mut rng);
                each(Case {
                    what: "random term",
                    term: t,
                    domains: ds,
                    listed,
                    classes: None,
                    demand: d,
                });
            }
        }
        Run::Deep { seed } => {
            let mut rng = Rng::new(seed);
            for _ in 0..200 {
                let (t, d) = if rng.below(2) == 0 {
                    (bool_term(&mut rng, 4), Demand::Bool(rng.below(2) == 0))
                } else {
                    (int_term(&mut rng, 4), int_demand(&mut rng))
                };
                let (ds, listed) = domains(&mut rng);
                each(Case {
                    what: "random term, depth 4",
                    term: t,
                    domains: ds,
                    listed,
                    classes: None,
                    demand: d,
                });
            }
        }
        Run::Exact { seed, test } => {
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
                each(Case {
                    what: "exact",
                    term: t,
                    domains: ds,
                    listed: Listed::new(),
                    classes: Some(cs),
                    demand: d,
                });
            }
        }
    }
}

/// The random terms of `random.rs`, with its seeds and others, and its exact preimages: the
/// runs `RUNS[runs]`, in three tests so each stays under 60 s (since S22-exact-mislabel every
/// case runs the interpreter over its points, not only the cases that differ), with the least
/// number of cases and the narrower, made exact and unlisted counts of each.
fn random_terms(
    runs: std::ops::Range<usize>,
    (least, narrower, exact, unlisted): (usize, usize, usize, usize),
) {
    on_big_stack(|| {
        let mut diffs = Diffs::default();
        for run in RUNS[runs].iter().copied() {
            cases(run, |c| match &c.classes {
                None => diffs.preimage_listed(c.what, &c.term, &c.domains, &c.listed, &c.demand),
                Some(cs) => diffs.exact(c.what, &c.term, &c.domains, cs, &c.demand),
            });
        }
        // The one box S22b changes here, `((5 mod (3 - x)) mod abs(5))` with `x` in `[-4, ∞)`
        // and the demand `[-3, 5]`, is now exact (`x` in `[-4, 2] | [4, ∞)`, where `3 - x` is
        // not zero) and was inexact (`[-4, ∞)`), so it counts as made exact, not reflected.
        // One more is made exact since PRODUCT-nested-chain summarizes the sum or difference
        // of two lines of one input.
        //
        // Since PA-plus-if, which summarizes the sum or difference of any two summaries of one
        // input (an `if` among them) and inverts such a sum where the transfer projected it,
        // 22 more boxes are exact (24), 6 inexact boxes are narrower than the transfer
        // before and sound, and one exact preimage the transfer before listed point by point,
        // `(x <= x) || …`, is the same set read without a listing.
        //
        // 25, was 24, since SOUND-div-exact: the linear stage reads `c^0` only where `c`
        // translates, so the transfer before now lists the points of `((y mod y)^0) > ((x +
        // x)^1)` with `y` in `{-12}`, where it read `(y mod y)^0` as 1; the transfer reads the
        // same box, `x <= 0`, exact without a listing.
        //
        // Since PRES-pendants-wider, which tightens a hull end whose other end is infinite and
        // reads the bounds that rows give each other, the transfer before, which shares the
        // solver, gives one of those 6 narrower boxes as the transfer does (5). Five results
        // change, each inside the one before (`x` in `[0, ∞)` with `y` in `[3, 8]` to the
        // exact `[4, ∞)`, `y` in `(-∞, 22]` to `[11, 22]`), and the interpreter refutes none.
        //
        // 24, was 25, since PROJECT-canon-precision, which tests each disjunct for a point whether
        // or not the greedy search found one first: the transfer before, which shares the solver,
        // gives one more of those boxes exactly as the transfer does, `x` in `[-2, 2]` with `y` in
        // `(-∞, 13]`, where it kept all of `x`. Two boxes of the transfer narrow, still inexact
        // (`x` in `[-21, ∞)` for all of `x`; `y` in `[-47, -23] ∪ [-1, 23]` for `[-47, 23]`), and
        // two exact boxes are read by both transfers without listing their points; the
        // interpreter refutes none.
        //
        // The counts above are of all 18 runs, one test before S22-exact-mislabel: 6800 cases,
        // 5 narrower, 24 made exact and 1 unlisted, now split over the three tests below.
        diffs.unlisted(unlisted).none_but(least, narrower, 0, exact);
    });
}

#[test]
fn random_terms_keep_their_preimages_0() {
    random_terms(0..5, (2800, 2, 8, 0));
}

#[test]
fn random_terms_keep_their_preimages_1() {
    random_terms(5..8, (1900, 0, 9, 0));
}

#[test]
fn random_terms_keep_their_preimages_2() {
    random_terms(8..18, (2100, 3, 7, 1));
}

/// Guards, domains, offsets and demands at the two ends of `i64`, values that leave `i64`
/// inside a chain, reflections under several demands, products, and empty demands.
#[test]
fn ends_of_i64_and_other_corners_keep_their_preimages() {
    use End::{NegInf, PosInf};
    let fin = End::of;
    const MIN: i64 = i64::MIN;
    const MAX: i64 = i64::MAX;
    on_big_stack(|| {
        let mut diffs = Diffs::default();
        let ends = [MIN, MIN + 1, MIN + 2, -1, 0, 1, MAX - 2, MAX - 1, MAX];
        let doms = [(-2, 2), (MIN, MIN + 3), (MAX - 3, MAX), (MIN, MAX)];
        let demands = [
            Demand::Ints(IntervalSet::single(0)),
            Demand::Ints(IntervalSet::range(fin(MAX - 1), PosInf)),
            Demand::Ints(IntervalSet::range(NegInf, fin(MIN + 1))),
            Demand::Ints(IntervalSet::from_pieces(vec![
                (NegInf, fin(MIN + 2)),
                (fin(MAX - 2), PosInf),
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
                Shared::new(ge_i(b)),
                Shared::new(yes.clone()),
                Shared::new(no.clone()),
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
        // Two reflections, counted as reflected until S22-exact-mislabel: the boxes before
        // were marked exact while holding points that fail the demand; they are now inexact,
        // so the new exact boxes count as made exact. One, since PERF-s22-const-chain: the
        // other box before, `i` in `[-25, -20] ∪ {-5} ∪ [3, 5] ∪ [12, 17] ∪ [27, 32]` over
        // `[-30, -20] ∪ [-5, 5] ∪ [12, 40]` with demand `[-25, -20] ∪ [-10, -5] ∪ [3, 4] ∪
        // [10, 12]`, doubted only `i = 5`, which the linear stage decides alone; the box
        // before is now the exact box of the transfer, without 5.
        diffs.none_but(4000, 0, 0, 1);
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
            let prev = Shared::new(t);
            let g = prim(Prim::Ge, var("x"), int(rng.int(-10, 10)));
            let more = prim(Prim::Add, (*prev).clone(), int(rng.int(-4, 4)));
            t = Term::If(Shared::new(g), prev, Shared::new(more));
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
/// with the hull passes `i64::MAX`. Until S22-WIDE `Tx::fits` turned the summary and the clip
/// off there and the transfer before ran, at about `k^2.8` (30 s at `k = 2048`); the summary
/// now holds its values in `i128`, so the clip stays on.
#[test]
fn chain_probe_wide_scales() {
    scales("probe_wide", 256);
}

/// The probe with `i` in `[-100, i64::MAX]`: the domain's end at the end of `i64`, which the
/// summary read as an infinity until S22-WIDE, and so gave up on, leaving the transfer before.
#[test]
fn chain_probe_max_scales() {
    scales("probe_max", 256);
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

/// The probe with the guard spelled `j <= i`.
#[test]
fn chain_le_scales() {
    scales("le", 256);
}

/// The probe asked `tk >= -3 && tk <= 7`: two comparisons of the shared chain under `&&`.
#[test]
fn chain_rangeand_scales() {
    scales("rangeand", 256);
}

/// The live families, `i` in `[-k, k]`: no demand merges with another.
#[test]
fn chain_alt_live_scales() {
    scales("alt_live", 256);
}

#[test]
fn chain_eq0_live_scales() {
    scales("eq0_live", 256);
}

#[test]
fn chain_range_live_scales() {
    scales("range_live", 256);
}

/// `c_j = j` over `[-k, k]`: before S22a 28.9 times the instructions at 8 and 64 (cross-review
/// xs22, VERIFY_CLAUDE.md).
#[test]
fn chain_cj_live_scales() {
    scales("cj_live", 256);
}

/// `c_j = ±j`, the sign alternating with `j`.
#[test]
fn chain_altj_scales() {
    scales("altj", 256);
}

/// `c_j = ±j` over `[-k, k]`: before S22a 216 times the instructions at 8 and 64 (cross-review
/// xs22, VERIFY_CLAUDE.md).
#[test]
fn chain_altj_live_scales() {
    scales("altj_live", 256);
}

#[test]
fn chain_ne0_scales() {
    scales("ne0", 256);
}

/// Else arm `0 - (t + 1)`, under an integer demand of two pieces on both signs.
#[test]
fn chain_neg_scales() {
    scales("neg", 256);
}

/// Else arm `-2 * t`, under an integer demand of two pieces on both signs: `tk` reaches
/// `50 * 2^k`, which passes `i128` from `k = 122`, where the summary's coefficients and values
/// become big integers (`Int`; COMPLEXITY.md S22, `mul`). From 32 to 256 the chain crosses that
/// size.
#[test]
fn chain_mul_across_i128_scales() {
    scales("mul", 32);
}

/// `mul` past `i128` at both sizes, its ends a bit longer at each level.
#[test]
fn chain_mul_scales() {
    scales("mul", 256);
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
/// `t_k = 3^k i - (3^k - 1) / 2`. At `i = -24` that leaves `i64` from `k = 37`, where the
/// transfer once rounded and the empty preimage of `t_k >= 0` was then listed, after a walk of
/// the shared term as a tree that took over 60 s at `k = 37`. The ends are now kept exactly
/// past `i64`, so every preimage here is exact without listing the box.
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
                assert!(!p.enumerated, "{name} k={k}");
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
        Shared::new(keep),
        Shared::new(prim(Prim::Add, i(), int(1))),
        Shared::new(i()),
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
/// inputs' remainders compared, and another input narrowed differently by class (the union of
/// boxes is not a box). A stretch where one class keeps its points and another does not that
/// spans many periods is answered by the split since S22e-wide: its box, the projection of the
/// classes' relation, lists the first and last periods of the stretch, inside the box before,
/// and is inexact, with that relation.
#[test]
fn a_split_by_remainders_is_given_up_where_it_cannot_be_exact() {
    let i = || var("i");
    let j = || var("j");
    let two = over(&[
        ("i", IntervalSet::of(-30, 30)),
        ("j", IntervalSet::of(-30, 30)),
    ]);
    let both = Term::If(
        Shared::new(prim(
            Prim::Eq,
            prim(Prim::Mod, i(), int(3)),
            prim(Prim::Mod, j(), int(3)),
        )),
        Shared::new(i()),
        Shared::new(j()),
    );
    let other = Term::If(
        Shared::new(prim(Prim::Eq, prim(Prim::Mod, i(), int(3)), int(0))),
        Shared::new(j()),
        Shared::new(prim(Prim::Add, j(), int(1))),
    );
    let wide = Term::If(
        Shared::new(prim(Prim::Eq, prim(Prim::Mod, i(), int(2)), int(0))),
        Shared::new(i()),
        Shared::new(int(0)),
    );
    // Since S22-linear-rem the linear stage writes `other` by its summaries over the classes
    // of `i mod 3`, one case for each range of classes: the same box, exactness and
    // relation body, with that definition.
    for (t, ds, d, def) in [
        (both, two.clone(), ints(0, 10), None),
        (
            other,
            two,
            ints(0, 10),
            Some("j if q1 <= 0, j + 1 if q1 >= 1"),
        ),
    ] {
        let (now, then) = (preimage(&t, &ds, &d), before::preimage(&t, &ds, &old(&d)));
        match def {
            None => assert_eq!(format!("{now:?}"), format!("{then:?}"), "{t}"),
            Some(def) => {
                let (rel, was) = (
                    now.relation.as_ref().unwrap(),
                    then.relation.as_ref().unwrap(),
                );
                assert_eq!(rel.body, was.body, "{t}");
                assert_eq!(rel.defs[..2], was.defs[..2], "{t}");
                assert_eq!(rel.defs[2].1, def, "{t}");
                let rest = format!(
                    "{:?} {} {} {:?} {:?}",
                    now.domains, now.exact, now.enumerated, now.stops, now.refusal
                );
                let was = format!(
                    "{:?} {} {} {:?} {:?}",
                    then.domains, then.exact, then.enumerated, then.stops, then.refusal
                );
                assert_eq!(rest, was, "{t}");
            }
        }
        check(&t, &ds, &d, &now, (-60, 60));
    }
    let (ds, d) = (i_in(-1000, 1000), ints(10, 2000));
    let (now, then) = (
        preimage(&wide, &ds, &d),
        before::preimage(&wide, &ds, &old(&d)),
    );
    assert!(!now.exact && !then.exact);
    let listed = [
        (10, 10),
        (12, 12),
        (14, 994),
        (996, 996),
        (998, 998),
        (1000, 1000),
    ];
    assert_eq!(now.domains["i"], pieces(&listed));
    assert_eq!(then.domains["i"], pieces(&[(10, 998), (1000, 1000)]));
    assert!(split_relation_exact(&wide, &ds, &d, &now));
    check(&wide, &ds, &d, &now, (-60, 1060));
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
/// where its box stops being exact). Each box is inexact with its relation kept, and no point
/// within the interpreter's window meets the demand outside it. Before the
/// change and after, the whole preimage, relation included, was equal on every family of this
/// file (running log, LIN-cross).
#[test]
fn chains_on_two_inputs_keep_their_boxes() {
    on_big_stack(|| {
        for k in [1, 2, 3, 5, 8, 13, 21, 34, 48, 50, 51] {
            for name in ["cross", "cross_live", "cross_dead"] {
                if name == "cross_dead" && k < 5 {
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

/// `cross` from `k = 12` to `96`: at 96 the formula implies `i >= 47`, and the disjuncts
/// `i <= j - 1` for `j` up to 47 have no point. Each was refuted by its own full propagation
/// in `probe`, about `k (k - 50)` settles in all: 99.5 M and 3.98 G bytes, 40.0 times (ledger
/// LIN-probe-refute). Since then one search over the bounds those disjuncts write finds
/// `i >= 47` with `O(log k)` propagations and refutes them all: 1.00 G bytes, 10.1 times, and
/// 3.74 G instructions against 0.30 G at 12, 12.3 times.
#[test]
fn chain_cross_above_its_width_scales() {
    scales("cross", 12);
}

/// `cross_dead` (`cross` with its inputs two narrower than the chain is long) has its only
/// point outside the demand at an end, `i = k - 2` and `m = 2 - k`. The greedy search over
/// disjunctions keeps `i` where the first solution put it and fails, and the failed-literal
/// search then tests the `2k` disjuncts. It tested each with a full propagation, about `k^2.4`
/// in all (0.26, 1.40, 7.2 and 39.4 G instructions at `k` = 10, 18, 34, 66); since LIN-probe
/// it keeps without a propagation each disjunct that a point found so far meets (2.88 G at
/// `k = 66`). On `cross` from `k = 51` to `99` the `k - 50` guards `j > 50` that no input meets
/// were each still refuted by one full propagation (2.0 G at 52, was 22.9 G; 1.05 G at 48), and since
/// LIN-probe-refute by one search over their bounds (`chain_cross_above_its_width_scales`).
#[test]
fn chain_cross_dead_scales() {
    scales("cross_dead", 8);
}

/// `cross_dead` at the sizes below 5, where its inputs are at most two wide and its box is
/// exact or empty of points outside: the preimage agrees with the interpreter on a window.
#[test]
fn chain_cross_dead_at_small_sizes() {
    on_big_stack(|| {
        for k in 2..=4 {
            let (t, ds, d) = family("cross_dead", k);
            let p = preimage(&t, &ds, &d);
            check(&t, &ds, &d, &p, (-8, 8));
        }
    });
}

/// COMPLEXITY.md S22e-quad: the `2k + 1` classes of `k` distinct remainders share one reading
/// of the chain. Each class runs the transfer from the root to the chain's top `if`, whose
/// summary in that class is read from one summary of the chain over all classes, built once.
/// Before, the whole chain was read again in each class: 58.0 times the instructions at 32
/// and 256 (200,279,152 against 11,615,272,274); now about 8.5 times.
#[test]
fn many_remainders_scales() {
    on_big_stack(|| {
        let n = 32;
        let (a, b) = (many_remainders(n), many_remainders(n * scaling::FACTOR));
        scaling::check("the preimage of the chain of k remainders", n, |k| {
            let (t, ds, d) = if k == n { &a } else { &b };
            preimage(t, ds, d);
        });
    });
}

/// The chain of `k` guards `i mod 1024 == j`, else `min(t + 1, 2^40)`, asked `tk >= 0`: the
/// summary over every class does not read `min`, so each class's run reads the guards itself.
fn min_remainders(k: usize) -> Term {
    let g = |j: i64| prim(Prim::Eq, prim(Prim::Mod, var("i"), int(1024)), int(j));
    let arm = |_, t| prim(Prim::Min, prim(Prim::Add, t, int(1)), int(1 << 40));
    prim(Prim::Ge, chain(k, var("i"), g, arm), int(0))
}

/// `i mod 1024 != j` for every `j` in `1..=k`, and `i >= 0`, as a chain of `if`s whose else
/// arms are `false`: boolean arms, which the summary over every class does not read.
fn no_remainder_of(k: usize) -> Term {
    (1..=k as i64).fold(ge_i(0), |t, j| {
        let g = prim(Prim::Ne, prim(Prim::Mod, var("i"), int(1024)), int(j));
        Term::If(
            Shared::new(g),
            Shared::new(t),
            Shared::new(Term::Lit(Value::Bool(false))),
        )
    })
}

/// `k` guards `i >= 7j`, else `t + 1`, above the chain of `many_remainders`, asked `>= 0`: each
/// class's run reads the `k` guards that are not on the remainder.
fn above_remainders(k: usize) -> Term {
    let g = |j: i64| prim(Prim::Eq, prim(Prim::Mod, var("i"), int(1024)), int(j));
    let t = chain(k, var("i"), g, plus(|_| 1));
    let t = chain(k, t, |j| ge_i(j * 7), plus(|_| 1));
    prim(Prim::Ge, t, int(0))
}

/// COMPLEXITY.md S22e-quad: over one period the transfer over the box reads every guard on the
/// remainder exactly, and where a class's run reads a guard by itself the split by classes
/// costs one transfer of the chain per class. In both the transfer runs first, as before the
/// split was moved ahead of it. With the split run first, from 8 to 64 the `min` chain took
/// 45.3 times the instructions, from 16 to 128 the `!=` chain 45.7 times and the tests above
/// the chain 64.8 times (21.0M against 1361.2M); the transfer alone is linear in all three.
#[test]
fn remainders_read_by_each_class_keep_the_transfer_first_scales() {
    on_big_stack(|| {
        let ds = i_in(0, 1000);
        let d = Demand::Bool(true);
        let n = 8;
        let (a, b) = (min_remainders(n), min_remainders(n * scaling::FACTOR));
        scaling::check("the preimage of the min chain of k remainders", n, |k| {
            preimage(if k == n { &a } else { &b }, &ds, &d);
        });
        let n = 16;
        let (a, b) = (no_remainder_of(n), no_remainder_of(n * scaling::FACTOR));
        scaling::check("the preimage of k remainders excluded", n, |k| {
            preimage(if k == n { &a } else { &b }, &ds, &d);
        });
        let n = 16;
        let (a, b) = (above_remainders(n), above_remainders(n * scaling::FACTOR));
        scaling::check("the preimage of k tests above k remainders", n, |k| {
            preimage(if k == n { &a } else { &b }, &ds, &d);
        });
    });
}

/// COMPLEXITY.md S22e-quad, the three families of
/// `remainders_read_by_each_class_keep_the_transfer_first_scales` over one period, and the
/// `min` and `!=` chains over many periods, where the split before the first transfer is given
/// up after one class: each preimage agrees with the interpreter, and is exact over one period
/// (the `min` and the tests-above chains hold everywhere on `[0, 1000]`, and the `!=` chain keeps
/// `0` and `k + 1..=1000`).
#[test]
fn remainders_read_by_each_class_keep_their_preimages() {
    on_big_stack(|| {
        let d = Demand::Bool(true);
        for k in [0, 1, 2, 5] {
            for (t, lo, hi) in [
                (min_remainders(k), 0, 1000),
                (no_remainder_of(k), 0, 1000),
                (min_remainders(k), -3000, 3000),
                (no_remainder_of(k), -3000, 3000),
                (above_remainders(k), 0, 1000),
            ] {
                let ds = i_in(lo, hi);
                let p = preimage(&t, &ds, &d);
                if lo == 0 {
                    assert!(p.exact, "{t} over {ds:?}: {p:?}");
                }
                check(&t, &ds, &d, &p, (-1100, 1100));
            }
        }
    });
}

/// The chain of guards `i mod m(j) == r(j)` for `j` in `1..=k`, else arm `arm(j, t)`, asked
/// `tk >= 0`.
fn remainder_chain(
    k: usize,
    m: impl Fn(i64) -> i64,
    r: impl Fn(i64) -> i64,
    arm: impl Fn(i64, Term) -> Term,
) -> (Term, Demand) {
    let g = |j| prim(Prim::Eq, prim(Prim::Mod, var("i"), int(m(j))), int(r(j)));
    let t = chain(k, var("i"), g, arm);
    (prim(Prim::Ge, t, int(0)), Demand::Bool(true))
}

/// The interpreter agrees with `p` at each input in `points`: a point that meets the demand
/// lies inside, and when `p` is exact a point inside meets it.
fn check_at(what: &str, t: &Term, d: &Demand, p: &zedc::store::preimage::Preimage, points: &[i64]) {
    let names: Vec<Arc<str>> = vec!["i".into()];
    for &i in points {
        let inside = p.domains["i"].contains(i);
        let meets = super::meets(t, &names, &[i], d);
        assert!(
            !meets || inside,
            "{what}: {t}: {i} meets {d:?} but is outside {p:?}"
        );
        assert!(
            meets || !inside || !p.exact,
            "{what}: {t}: {i} fails {d:?} but is inside {p:?}"
        );
    }
}

/// COMPLEXITY.md S22e-quad, the shapes the summary over every class reads: no guard, one and
/// two guards, remainders repeated, a negative modulus and both signs in one chain, and
/// remainders outside `[0, m)`, which no input has. Each preimage is exact and agrees with the
/// interpreter.
#[test]
fn remainder_chains_of_every_shape_match_the_interpreter() {
    on_big_stack(|| {
        let plus1 = plus(|_| 1);
        let cases: Vec<(&str, (Term, Demand))> = vec![
            ("k=0", remainder_chain(0, |_| 16, |j| j, &plus1)),
            ("k=1", remainder_chain(1, |_| 16, |j| j, &plus1)),
            ("k=2", remainder_chain(2, |_| 16, |j| j, &plus1)),
            ("j mod 3", remainder_chain(9, |_| 16, |j| j % 3, &plus1)),
            ("all 5", remainder_chain(6, |_| 16, |_| 5, &plus1)),
            ("m = -16", remainder_chain(5, |_| -16, |j| j, &plus1)),
            (
                "m = +-16",
                remainder_chain(6, |j| if j % 2 == 0 { 16 } else { -16 }, |j| j, &plus1),
            ),
            (
                "outside",
                remainder_chain(6, |_| 16, |j| j * 7 - 20, &plus1),
            ),
            (
                "arms",
                remainder_chain(
                    6,
                    |_| 16,
                    |j| j,
                    |j, t| {
                        let s = prim(Prim::Sub, int(0), prim(Prim::Add, int(j), t));
                        Term::Prim(Prim::Neg, vec![prim(Prim::Mul, int(1), s)])
                    },
                ),
            ),
        ];
        for (what, (t, d)) in cases {
            for ds in [
                i_in(-60, 60),
                over(&[("i", pieces(&[(-60, -31), (-9, 50)]))]),
            ] {
                let p = preimage(&t, &ds, &d);
                assert!(
                    p.exact && p.refusal.is_none(),
                    "{what}: {t} over {ds:?}: {p:?}"
                );
                check(&t, &ds, &d, &p, (-70, 70));
            }
        }
    });
}

/// COMPLEXITY.md S22e-quad, the terms the summary over every class does not read, which each
/// class reads with its own transfer as before: a guard that is not on the remainder between
/// guards that are, an arm the summary does not read (`min`), values that leave `i64` at the
/// ends of the domain, and remainders and moduli at the ends of `i64`. Each agrees with the
/// interpreter, at the ends of `i64` too. Two results changed with S22e-quad: `m = i64::MAX` and
/// `m = i64::MIN + 1` over `[i64::MIN, i64::MIN + 40]` were exact and empty before, found by
/// listing the box; they are now exact and empty without listing it (`enumerated` false).
#[test]
fn remainder_chains_outside_the_shared_summary_keep_their_preimages() {
    use End::{NegInf, PosInf};
    const MIN: i64 = i64::MIN;
    const MAX: i64 = i64::MAX;
    on_big_stack(|| {
        let plus1 = plus(|_| 1);
        let r16 = |j: i64| prim(Prim::Eq, prim(Prim::Mod, var("i"), int(16)), int(j));
        let other = |j: i64| if j == 3 { ge_i(5) } else { r16(j) };
        let mixed = prim(Prim::Ge, chain(6, var("i"), other, &plus1), int(0));
        let min = |_, t| prim(Prim::Min, prim(Prim::Add, t, int(1)), int(20));
        let cases: Vec<(&str, (Term, Demand))> = vec![
            ("i >= 5 at j = 3", (mixed, Demand::Bool(true))),
            ("min", remainder_chain(6, |_| 16, |j| j, min)),
            ("plus", remainder_chain(6, |_| 16, |j| j, &plus1)),
            (
                "r = MAX",
                remainder_chain(3, |_| 16, |j| if j == 2 { MAX } else { j }, &plus1),
            ),
            (
                "r = MIN",
                remainder_chain(3, |_| 16, |j| if j == 2 { MIN } else { j }, &plus1),
            ),
            ("m = MAX", remainder_chain(4, |_| MAX, |j| MAX - j, &plus1)),
            ("m = MIN", remainder_chain(4, |_| MIN, |j| j, &plus1)),
            (
                "m = MIN + 1",
                remainder_chain(4, |_| MIN + 1, |j| MAX - j, &plus1),
            ),
        ];
        let top = IntervalSet::range(NegInf, PosInf);
        let high = IntervalSet::range(End::of(MAX - 40), End::of(MAX));
        let low = IntervalSet::range(End::of(MIN), End::of(MIN + 40));
        let mut ends: Vec<i64> = (0..=40).flat_map(|d| [MIN + d, MAX - d]).collect();
        ends.extend(-70..=70);
        for (what, (t, d)) in cases {
            for dom in [
                IntervalSet::of(-60, 60),
                top.clone(),
                high.clone(),
                low.clone(),
            ] {
                let ds = over(&[("i", dom.clone())]);
                let p = preimage(&t, &ds, &d);
                let at: Vec<i64> = ends.iter().copied().filter(|&i| dom.contains(i)).collect();
                check_at(what, &t, &d, &p, &at);
            }
        }
    });
}

/// `many_remainders(k)` below `if (i mod 1024 == 0) { false }`: over the whole box a stretch
/// where some classes keep their points and others do not spans many periods, and the split
/// over the transfer's box is exact (COMPLEXITY.md S22e-wide).
fn zero_excluded(k: usize) -> Term {
    let (t, _, _) = many_remainders(k);
    let g = prim(Prim::Eq, prim(Prim::Mod, var("i"), int(1024)), int(0));
    Term::If(
        Shared::new(g),
        Shared::new(Term::Lit(Value::Bool(false))),
        Shared::new(t),
    )
}

/// COMPLEXITY.md S22e-wide: the four programs of the plan item over `[-5000, 5000]`, about ten
/// periods of 1024. On main before it, from `k` to `2k`: the `min` chain about `k^2.7` (26.6M,
/// 136.8M and 868.8M instructions at `k` = 8, 16 and 32), the tests above the chain `k^2`
/// (28.3M and 109.1M at 16 and 32), the `!=` chain 249M and 763M at 4 and 8, and the chain
/// below `i mod 1024 == 0` 1.59G and 5.16G at 4 and 8; main left all but the first inexact.
/// Now, from `k` to `8k`, 2.24M to 17.6M (`k` = 8), 6.44M to 53.7M (16), 17.3M to 20.6M (4)
/// and 85.9M to 498M (4), and all four are exact.
#[test]
fn remainders_over_many_periods_scale() {
    on_big_stack(|| {
        let ds = i_in(-5000, 5000);
        let d = Demand::Bool(true);
        let families = [
            (
                "the min chain of k remainders",
                8,
                min_remainders as fn(usize) -> Term,
            ),
            ("k tests above k remainders", 16, above_remainders),
            ("k remainders excluded", 4, no_remainder_of),
            ("k remainders below i mod 1024 == 0", 4, zero_excluded),
        ];
        for (what, n, family) in families {
            let (a, b) = (family(n), family(n * scaling::FACTOR));
            scaling::check(what, n, |k| {
                preimage(if k == n { &a } else { &b }, &ds, &d);
            });
        }
    });
}

/// COMPLEXITY.md S22e-wide: the four programs over many periods are exact and agree with the
/// interpreter.
#[test]
fn remainders_over_many_periods_keep_their_preimages() {
    on_big_stack(|| {
        let ds = i_in(-5000, 5000);
        let d = Demand::Bool(true);
        for k in [1, 2, 5, 9] {
            for t in [
                min_remainders(k),
                above_remainders(k),
                no_remainder_of(k),
                zero_excluded(k),
            ] {
                let p = preimage(&t, &ds, &d);
                assert!(p.exact, "{t}: {p:?}");
                check(&t, &ds, &d, &p, (-1100, 1100));
                check(&t, &ds, &d, &p, (3000, 5000));
            }
        }
    });
}

/// The split by remainders at the moduli 1, 2, 3, 1024, `i64::MAX` and `i64::MIN + 1`, over an
/// empty box, a single point, a box within two periods, one over many periods, one at the top
/// of `i64`, and pieces in which some classes have no members: every preimage agrees with the
/// interpreter, is exact wherever the one before was, and lies inside it.
#[test]
fn remainder_splits_at_their_corners_keep_their_preimages() {
    on_big_stack(|| {
        let top = i64::MAX;
        for m in [1, 2, 3, 1024, i64::MAX, i64::MIN + 1] {
            let r = 3.min(m.unsigned_abs() - 1) as i64;
            let rem = || prim(Prim::Mod, var("i"), int(m));
            let is = |c: i64| prim(Prim::Eq, rem(), int(c));
            let not = |c: i64, t: Term| {
                Term::If(
                    Shared::new(prim(Prim::Ne, rem(), int(c))),
                    Shared::new(t),
                    Shared::new(Term::Lit(Value::Bool(false))),
                )
            };
            let picked = Term::If(
                Shared::new(is(r)),
                Shared::new(var("i")),
                Shared::new(int(0)),
            );
            let terms = [
                (picked, ints(10, 2000)),
                (not(1, not(2, ge_i(0))), Demand::Bool(true)),
                (is(r), Demand::Bool(true)),
            ];
            // Pieces holding the remainders 0 to 2 of 10 in each of ten periods.
            let comb: Vec<(i64, i64)> = (0..10).map(|p| (10 * p, 10 * p + 2)).collect();
            let boxes = [
                (IntervalSet::empty(), (-60, 60)),
                (IntervalSet::of(7, 7), (-60, 60)),
                (IntervalSet::of(-7, -7), (-60, 60)),
                (IntervalSet::of(-3, 2), (-60, 60)),
                (IntervalSet::of(-40, 40), (-60, 60)),
                (IntervalSet::of(-5000, 5000), (-1100, 1100)),
                (IntervalSet::of(top - 40, top), (top - 60, top)),
                (pieces(&comb), (-10, 110)),
            ];
            for (t, d) in &terms {
                for (set, window) in &boxes {
                    let ds = over(&[("i", set.clone())]);
                    let (now, then) = (preimage(t, &ds, d), before::preimage(t, &ds, &old(d)));
                    let what = format!("{t} over {ds:?}, demand {d:?}");
                    check(t, &ds, d, &now, *window);
                    assert!(now.exact || !then.exact, "{what}: {now:?} before {then:?}");
                    let inside = now.domains["i"].pieces().all(|(lo, hi)| {
                        then.domains["i"].pieces().any(|(l, h)| l <= lo && hi <= h)
                    });
                    assert!(inside, "{what}: {now:?} before {then:?}");
                }
            }
        }
    });
}

/// A stamp sheet of 1024 slots a page: slot 0 of a page is never stamped, slots below 512
/// always are, and the rest only within the six runs `[1024t + 300, 1024t + 1100]`. Each run
/// is shorter than a page and wraps past its page end with both ends in one class of the
/// split (`[1, 511]`), so the check that a box lies in its classes' sets must split the run
/// at the page end by remainder, not by the order of its end classes: the box `[2049, 5119]`
/// holds `3072`, slot 0 of a page, which is never stamped.
#[test]
fn a_stretch_wrapping_past_the_modulus_inside_one_class_is_checked_by_remainder() {
    on_big_stack(|| {
        let rem = || prim(Prim::Mod, var("i"), int(1024));
        let tt = || Term::Lit(Value::Bool(true));
        let ff = || Term::Lit(Value::Bool(false));
        let ite =
            |g: Term, a: Term, b: Term| Term::If(Shared::new(g), Shared::new(a), Shared::new(b));
        for periods in [3i64, 4, 6, 9] {
            let mut runs = ff();
            for t in (0..periods).rev() {
                let run = prim(
                    Prim::And,
                    prim(Prim::Ge, var("i"), int(1024 * t + 300)),
                    prim(Prim::Le, var("i"), int(1024 * t + 1100)),
                );
                runs = ite(run, tt(), runs);
            }
            let stamped = ite(
                prim(Prim::Eq, rem(), int(0)),
                ff(),
                ite(prim(Prim::Lt, rem(), int(512)), tt(), runs),
            );
            let ds = i_in(0, 1024 * periods + 1023);
            let d = Demand::Bool(true);
            let p = preimage(&stamped, &ds, &d);
            check(&stamped, &ds, &d, &p, (0, 1024 * periods + 1023));
        }
    });
}

/// A chain of `k` guards `x mod m == r`, each `r` drawn in `[0, m)`, whose two arms each move
/// the term before by one of `t`, `t + c`, `c - t`, `-t`, `min(t, c)` and `max(t, c)`, drawn
/// with `seed`: a remainder guard over many periods that the split by remainders does not
/// answer alone once the term around it reads another input or tests the chain.
fn moved_remainder_chain(seed: u64, k: usize, x: &str, m: i64) -> Term {
    let mut rng = Rng::new(seed);
    (0..k).fold(var(x), |t, _| {
        let r = rng.int(0, m.abs() - 1);
        let g = prim(Prim::Eq, prim(Prim::Mod, var(x), int(m)), int(r));
        let arm = |rng: &mut Rng| {
            let c = rng.int(-6, 6);
            let t = t.clone();
            match rng.below(7) {
                0 | 1 => t,
                2 => prim(Prim::Add, t, int(c)),
                3 => prim(Prim::Sub, int(c), t),
                4 => Term::Prim(Prim::Neg, vec![t]),
                5 => prim(Prim::Min, t, int(c)),
                _ => prim(Prim::Max, t, int(c)),
            }
        };
        let (a, b) = (arm(&mut rng), arm(&mut rng));
        Term::If(Shared::new(g), Shared::new(a), Shared::new(b))
    })
}

/// The shapes of item S22-transfer-rem around the chain `c` over `x`, each asked `true`: the
/// arms of an `if` reading different inputs (`y >= 0` or `x >= 0` picks `c` or `y`), a test
/// of `c` (`c >= 1` picks `y` or `-y`), and remainders of two inputs or two moduli (`c <= 2`
/// and `y mod 2 == 0`, or `x mod 2 == 0`).
fn remainder_shape(shape: &str, c: Term) -> Term {
    let le2 = |t: Term| prim(Prim::Le, t, int(2));
    let pick = |g: Term, a: Term, b: Term| Term::If(Shared::new(g), Shared::new(a), Shared::new(b));
    let even = |x: &str| prim(Prim::Eq, prim(Prim::Mod, var(x), int(2)), int(0));
    match shape {
        "arms of x and y" => le2(pick(prim(Prim::Ge, var("y"), int(0)), c, var("y"))),
        "arms over x" => le2(pick(prim(Prim::Ge, var("x"), int(0)), c, var("y"))),
        "a test of the chain" => le2(pick(
            prim(Prim::Ge, c, int(1)),
            var("y"),
            Term::Prim(Prim::Neg, vec![var("y")]),
        )),
        "remainders of two inputs" => prim(Prim::And, le2(c), even("y")),
        "two moduli of one input" => prim(Prim::And, le2(c), even("x")),
        _ => unreachable!("no shape {shape}"),
    }
}

const REMAINDER_SHAPES: [&str; 5] = [
    "arms of x and y",
    "arms over x",
    "a test of the chain",
    "remainders of two inputs",
    "two moduli of one input",
];

/// `x` and `y` in `[-w, w]`.
fn xy_in(w: i64) -> Domains {
    over(&[("x", IntervalSet::of(-w, w)), ("y", IntervalSet::of(-w, w))])
}

/// The chain of `k` guards `x mod m == j mod 3`, else `t + 1`. At `m = 3` each `x` misses two
/// guards in every three, so at `k = 3q` the chain is `x + 2q`.
fn counted_remainder_chain(k: usize, m: i64) -> Term {
    let g = |j: i64| prim(Prim::Eq, prim(Prim::Mod, var("x"), int(m)), int(j % 3));
    chain(k, var("x"), g, plus(|_| 1))
}

/// Five programs around the chain `c`, each asked `true`: `if x >= 0 { c } else { y } <= 2`,
/// `if y >= 0 { c } else { 9 } <= 2`, `if c >= 1 { y } else { 9 } <= 2`,
/// `c <= 2 && y mod 2 == 0` and `c <= 2 && x mod 2 == 0`.
fn counted_shapes(c: Term) -> [Term; 5] {
    let le2 = |t: Term| prim(Prim::Le, t, int(2));
    let pick = |g: Term, a: Term, b: Term| Term::If(Shared::new(g), Shared::new(a), Shared::new(b));
    let even = |x: &str| prim(Prim::Eq, prim(Prim::Mod, var(x), int(2)), int(0));
    [
        le2(pick(prim(Prim::Ge, var("x"), int(0)), c.clone(), var("y"))),
        le2(pick(prim(Prim::Ge, var("y"), int(0)), c.clone(), int(9))),
        le2(pick(prim(Prim::Ge, c.clone(), int(1)), var("y"), int(9))),
        prim(Prim::And, le2(c.clone()), even("y")),
        prim(Prim::And, le2(c), even("x")),
    ]
}

/// COMPLEXITY.md S22-transfer-rem: the chain `x + 2q` of `k = 3q` guards `x mod 3 == j mod 3`
/// over `x` and `y` in `[-60, 60]`, 40 periods, in each of the five programs of
/// [`counted_shapes`], has the box worked out by hand, exact where every point in it meets
/// the demand, and agrees with the interpreter. A box cannot hold the even numbers alone, so
/// the last two keep their hull, with the ends `-60` and `60` apart, and a relation.
#[test]
fn remainder_reads_outside_a_split_have_their_preimages() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(60), Demand::Bool(true));
        let all = || pieces(&[(-60, 60)]);
        // The hull of the even numbers in `[-60, hi]`, less the odd ends `-59` and `59`.
        let evens = |hi: i64| {
            let ps = [(-60, -60), (-58, hi.min(58)), (60, 60)];
            pieces(
                &ps.into_iter()
                    .filter(|&(a, b)| a <= b && b <= hi)
                    .collect::<Vec<_>>(),
            )
        };
        for k in [3, 6, 30, 96] {
            let q = k as i64 / 3;
            // `x + 2q <= 2` at `x <= 2 - 2q`, and `x + 2q >= 1` at `x >= 1 - 2q`.
            let (le, ge) = ((2 - 2 * q).max(-61), (1 - 2 * q).max(-60));
            let upto = |hi: i64| {
                if hi < -60 {
                    IntervalSet::empty()
                } else {
                    pieces(&[(-60, hi)])
                }
            };
            let want: [(IntervalSet, IntervalSet, bool); 5] = [
                // `x >= 0` meets the chain only at `x = 0`, `q = 1`; `x < 0` asks `y <= 2`.
                if q == 1 {
                    (upto(0), all(), false)
                } else {
                    (upto(-1), pieces(&[(-60, 2)]), true)
                },
                (upto(le), pieces(&[(0, 60)]), true),
                (pieces(&[(ge, 60)]), pieces(&[(-60, 2)]), true),
                (upto(le), evens(60), false),
                (evens(le), all(), false),
            ];
            for (t, (x, y, exact)) in counted_shapes(counted_remainder_chain(k, 3))
                .iter()
                .zip(want)
            {
                let p = preimage(t, &ds, &d);
                let got = (&p.domains["x"], &p.domains["y"], p.exact);
                if x.is_empty() {
                    assert!(got.0.is_empty() || got.1.is_empty(), "k={k}: {t}: {p:?}");
                } else {
                    assert_eq!(got, (&x, &y, exact), "k={k}: {t}: {p:?}");
                }
                check(t, &ds, &d, &p, (-15, 15));
                check(t, &ds, &d, &p, (-60, -45));
            }
        }
    });
}

/// COMPLEXITY.md S22-transfer-rem: on the shape `shape` of [`remainder_shape`], three chains of
/// `k` guards `x mod 3 == r` with arms drawn at random, over `x` and `y` in `[-60, 60]`, agree
/// with the interpreter: every point that meets the demand lies in the box, and when the box
/// is exact every point in it meets the demand.
fn remainder_shape_matches_the_interpreter(shape: &str) {
    on_big_stack(|| {
        let (ds, d) = (xy_in(60), Demand::Bool(true));
        for seed in 1..=3 {
            for k in [1, 2, 5, 13] {
                let t = remainder_shape(shape, moved_remainder_chain(seed, k, "x", 3));
                let p = preimage(&t, &ds, &d);
                check(&t, &ds, &d, &p, (-20, 20));
                check(&t, &ds, &d, &p, (45, 60));
            }
        }
    });
}

/// One test per shape of [`REMAINDER_SHAPES`]. The five shapes in one test took 56.5 s at load
/// 10, nearly all of it in `preimage` (the interpreter takes 5 ms to 28 ms a case), and most of
/// that on the chain of seed 2 at `k = 13`: 10 s to 22 s a shape at load 22, spent in the
/// Presburger solver the linear stage calls. Since S22-linear-rem the linear stage writes such
/// a chain by its summaries over the classes (COMPLEXITY.md S22-linear-rem), and that chain
/// takes 0.05 s to 0.11 s a shape.
macro_rules! remainder_shapes {
    ($($name:ident $shape:literal),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                remainder_shape_matches_the_interpreter(REMAINDER_SHAPES[$shape]);
            }
        )*
    };
}

remainder_shapes!(
    remainder_reads_outside_a_split_match_the_interpreter_arms_of_x_and_y 0,
    remainder_reads_outside_a_split_match_the_interpreter_arms_over_x 1,
    remainder_reads_outside_a_split_match_the_interpreter_a_test_of_the_chain 2,
    remainder_reads_outside_a_split_match_the_interpreter_remainders_of_two_inputs 3,
    remainder_reads_outside_a_split_match_the_interpreter_two_moduli_of_one_input 4,
);

/// The seed of the case of [`wide_remainders_match_the_interpreter`] at modulus `m`, `p`
/// periods and shape `s` of [`REMAINDER_SHAPES`]: the three numbers written in one, so a seed
/// names its case.
fn wide_remainder_seed(m: i64, p: i64, s: usize) -> u64 {
    ((m as u64) << 16) | ((p as u64) << 8) | s as u64
}

/// The variable naming one seed of [`wide_remainder_seed`]: when it is set, a test of
/// [`wide_remainders_match_the_interpreter`] runs that case alone.
const WIDE_REMAINDER_SEED: &str = "ZED_REMAINDER_SEED";

/// Whether the relation `rel` holds at the point `pt` of the inputs `names`: whether some
/// values of its auxiliary variables meet its definitions and its body there. `None` when the
/// solver refuses the question.
fn relation_holds(rel: &Relation, names: &[Arc<str>], pt: &[i64]) -> Option<bool> {
    let mut parts = vec![rel.defined(), rel.body.clone()];
    for (n, &v) in names.iter().zip(pt) {
        parts.push(member(&Atom::Sym(n.clone()), &IntervalSet::of(v, v)));
    }
    satisfiable(&Formula::and(parts)).ok().map(|m| m.is_some())
}

/// The first point of the box `ds` at which the interpreter refutes `p` as the preimage of
/// `d` under `t`, with the reason: a point that meets `d` lies outside the box or fails the
/// relation, or, where the box is exact, a point inside fails `d`, or a point of the box that
/// meets the relation fails `d`. A point where the solver refuses the relation's question is
/// a refutation too, since the relation then decides nothing there. `window` holds every
/// input's domain.
fn wide_remainder_refuted(
    t: &Term,
    ds: &Domains,
    d: &Demand,
    p: &Preimage,
    window: (i64, i64),
) -> Option<String> {
    let names: Vec<Arc<str>> = ds.keys().cloned().collect();
    super::points(ds, &names, window)
        .into_iter()
        .find_map(|pt| {
            let meets = super::meets(t, &names, &pt, d);
            let inside = names
                .iter()
                .zip(&pt)
                .all(|(n, &v)| p.domains[n].contains(v));
            let why = if meets && !inside {
                "meets the demand but lies outside the box"
            } else if !meets && inside && p.exact {
                "fails the demand but lies inside the exact box"
            } else {
                match (&p.relation, inside) {
                    (Some(rel), true) => match (relation_holds(rel, &names, &pt), meets) {
                        (None, _) => "is where the solver refuses the relation's question",
                        (Some(false), true) => "meets the demand but fails the relation",
                        (Some(true), false) => {
                            "lies in the box and meets the relation but fails the demand"
                        }
                        _ => return None,
                    },
                    _ => return None,
                }
            };
            Some(format!("{names:?} = {pt:?} {why}"))
        })
}

/// DESIGN.md sec:domains, "Backward transfer": Euclidean `mod` by a constant inverts
/// exactly, a branch's preimage is the union of its arms' preimages under their guards, and
/// `min` and `max` invert exactly; step L1.25: every entry's preimage is sound against the
/// interpreter on random domains, and `x mod c` inverts to the set of `x` in its interval
/// whose remainder is demanded, exact whatever the width of the interval; where the preimage
/// is not a box, the box is its projection, marked necessary, and the relation (step L1.38)
/// holds at every point meeting the demand and, inside the box, only there.
///
/// For each modulus `m` of `moduli`, each count of periods `p` of `periods` and each shape of
/// [`REMAINDER_SHAPES`], one case seeded by [`wide_remainder_seed`]: a chain of 1 to 13
/// guards `x mod m == r` with arms drawn at random ([`moved_remainder_chain`]), `x` over
/// `p * m - e` integers (`e` in `[0, m)`, so the run is longer than `p - 1` periods of `m`
/// and no longer than `p`) from a random start in `[-100, 100]`, and `y` over a random interval
/// in `[-8, 8]`. The interpreter runs at every point of the box and is compared with the
/// preimage by [`wide_remainder_refuted`]. A failure prints the case's seed and the command
/// that reruns it alone.
fn wide_remainders_match_the_interpreter(
    test: &str,
    moduli: std::ops::RangeInclusive<i64>,
    periods: std::ops::RangeInclusive<i64>,
) {
    let only: Option<u64> = std::env::var(WIDE_REMAINDER_SEED)
        .ok()
        .map(|s| s.parse().expect("a seed is a number"));
    on_big_stack(|| {
        let d = Demand::Bool(true);
        for m in moduli {
            for p in periods.clone() {
                for (s, shape) in REMAINDER_SHAPES.iter().enumerate() {
                    let seed = wide_remainder_seed(m, p, s);
                    if only.is_some_and(|o| o != seed) {
                        continue;
                    }
                    let mut rng = Rng::new(seed);
                    let k = rng.int(1, 13) as usize;
                    let chain = moved_remainder_chain(rng.next_u64(), k, "x", m);
                    let t = remainder_shape(shape, chain);
                    let x0 = rng.int(-100, 100);
                    let x1 = x0 + p * m - 1 - rng.int(0, m - 1);
                    let y0 = rng.int(-8, 8);
                    let y1 = rng.int(y0, 8);
                    let ds = over(&[
                        ("x", IntervalSet::of(x0, x1)),
                        ("y", IntervalSet::of(y0, y1)),
                    ]);
                    let pre = preimage(&t, &ds, &d);
                    let window = (x0.min(y0), x1.max(y1));
                    if let Some(why) = wide_remainder_refuted(&t, &ds, &d, &pre, window) {
                        // The chain shares its arms, so the term printed as a tree can run to
                        // hundreds of kilobytes; it is printed only when the case runs alone.
                        let term = match only {
                            Some(_) => t.to_string(),
                            None => "the term (printed when the case runs alone)".to_string(),
                        };
                        panic!(
                            "seed {seed} (modulus {m}, {p} periods, shape {shape:?}, {k} guards): \
                             {term} over {ds:?}: {why}; the preimage is {} with relation {:?}.\n\
                             Rerun this case alone from the worktree root:\n  \
                             {WIDE_REMAINDER_SEED}={seed} /home/luke/Work/wt/zcargo test -p zed-tests \
                             --test l01_25_preimage_catalog -- --exact s22::{test}",
                            super::shown(&pre),
                            pre.relation.as_ref().map(|r| r.to_string()),
                        );
                    }
                }
            }
        }
    });
}

/// One test per group of moduli and periods of [`wide_remainders_match_the_interpreter`], each a
/// piece of its own. The 900 cases in one test took 82.5 s at load 18: 11 s in `preimage` and
/// the rest in the comparison, most of it the solver's answers on whether the relation holds at
/// each point of the box, which grow with the modulus and the periods (6 s for the moduli 2 to
/// 5 together, 12 s for 16 alone). In seven groups each took 18 s to 30 s at load 12 to 16,
/// six at once; in these fourteen, 8 s to 18 s at load 17 to 19, six at once.
macro_rules! wide_remainders {
    ($($name:ident $moduli:expr, $periods:expr);* $(;)?) => {
        $(
            #[test]
            fn $name() {
                wide_remainders_match_the_interpreter(stringify!($name), $moduli, $periods);
            }
        )*
    };
}

wide_remainders!(
    wide_remainders_match_the_interpreter_moduli_2_to_5 2..=5, 1..=12;
    wide_remainders_match_the_interpreter_modulus_6 6..=6, 1..=12;
    wide_remainders_match_the_interpreter_modulus_7 7..=7, 1..=12;
    wide_remainders_match_the_interpreter_modulus_8 8..=8, 1..=12;
    wide_remainders_match_the_interpreter_modulus_9 9..=9, 1..=12;
    wide_remainders_match_the_interpreter_modulus_10 10..=10, 1..=12;
    wide_remainders_match_the_interpreter_modulus_11 11..=11, 1..=12;
    wide_remainders_match_the_interpreter_modulus_12 12..=12, 1..=12;
    wide_remainders_match_the_interpreter_modulus_13 13..=13, 1..=12;
    wide_remainders_match_the_interpreter_modulus_14 14..=14, 1..=12;
    wide_remainders_match_the_interpreter_modulus_15_periods_1_to_8 15..=15, 1..=8;
    wide_remainders_match_the_interpreter_modulus_15_periods_9_to_12 15..=15, 9..=12;
    wide_remainders_match_the_interpreter_modulus_16_periods_1_to_8 16..=16, 1..=8;
    wide_remainders_match_the_interpreter_modulus_16_periods_9_to_12 16..=16, 9..=12;
);

/// The shapes of [`counted_shapes`] at their corners, each agreeing with the interpreter: the
/// moduli 1, -3, 1024 (one period), `2^62` and `i64::MIN`, whose classes do not fit `i64`, so
/// the transfer reads the guards as before; `x` unbounded, in pieces or empty; and the demand
/// `false` over `[-60, 60]`.
#[test]
fn remainder_reads_outside_a_split_at_their_corners() {
    on_big_stack(|| {
        let y = ("y", IntervalSet::of(-60, 60));
        let domains = [
            over(&[("x", IntervalSet::of(-60, 60)), y.clone()]),
            over(&[
                ("x", IntervalSet::range(End::NegInf, End::PosInf)),
                y.clone(),
            ]),
            over(&[("x", pieces(&[(-60, -31), (-9, 50)])), y.clone()]),
            over(&[("x", IntervalSet::empty()), y]),
        ];
        for m in [1, -3, 1024, 1 << 62, i64::MIN] {
            for k in [1, 6] {
                for t in counted_shapes(counted_remainder_chain(k, m)) {
                    for (i, ds) in domains.iter().enumerate() {
                        // The demand `false` on the first domain only, to keep the test short.
                        for d in [Demand::Bool(true), Demand::Bool(false)]
                            .iter()
                            .take(if i == 0 { 2 } else { 1 })
                        {
                            let p = preimage(&t, ds, d);
                            check(&t, ds, d, &p, (-12, 12));
                        }
                    }
                }
            }
        }
        // At `m = 1` the guard `x mod 1 == j mod 3` holds at `j = 0, 3, ...` alone, so the chain
        // is `x + 4` at `k = 6`: `if y >= 0 { x + 4 } else { 9 } <= 2`.
        let t = &counted_shapes(counted_remainder_chain(6, 1))[1];
        let p = preimage(t, &xy_in(60), &Demand::Bool(true));
        assert!(p.exact, "{p:?}");
        assert_eq!(p.domains["x"], IntervalSet::of(-60, -2));
        assert_eq!(p.domains["y"], IntervalSet::of(0, 60));
    });
}

/// COMPLEXITY.md S22-transfer-rem: the three shapes the split by remainders does not answer
/// alone (arms of an `if` reading different inputs, a test of a term that reads a remainder,
/// remainders of two inputs), each over a chain of `k` guards `x mod 3 == r` across 40
/// periods, take work of order `k` from `k` to `8k`.
#[test]
fn remainder_reads_outside_a_split_scale() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(60), Demand::Bool(true));
        for shape in [
            "arms of x and y",
            "a test of the chain",
            "remainders of two inputs",
        ] {
            let n = 8;
            let terms = scaling::inputs(n, |k| {
                remainder_shape(shape, moved_remainder_chain(1, k, "x", 3))
            });
            scaling::check(shape, n, |k| {
                preimage(&terms[&k], &ds, &d);
            });
        }
    });
}

/// COMPLEXITY.md S22-linear-rem: the linear stage on what the counted chain of `k` guards
/// `x mod 3 == j mod 3` leaves, in `c <= 2 && y mod 2 == 0` and `c <= 2 && x mod 2 == 0` over
/// `x` and `y` in `[-100000, 100000]`, does work of order `k` from `k` to `8k`. Level by
/// level, one variable for each guard read together by the solver, it took 0.66 s at
/// `k = 15` and 24.6 s at `k = 120`; written by the chain's summaries over the classes of
/// `x mod 3`, it is one variable with a case for each piece of each range of classes.
#[test]
fn remainder_chains_in_the_linear_stage_scale() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(100000), Demand::Bool(true));
        for (shape, at) in [("c <= 2 && y mod 2 == 0", 3), ("c <= 2 && x mod 2 == 0", 4)] {
            let n = 5;
            let terms = scaling::inputs(n, |k| {
                counted_shapes(counted_remainder_chain(k, 3))[at].clone()
            });
            scaling::check(shape, n, |k| {
                preimage(&terms[&k], &ds, &d);
            });
        }
    });
}

/// A box of `x` as its pieces `(lo, hi)`.
type Boxes = &'static [(i64, i64)];

/// COMPLEXITY.md S22-case-cuts: in the five shapes of [`REMAINDER_SHAPES`], the boxes of `x`
/// that the hull of each case made wider than the level-by-level translation, or wider at some
/// points and narrower at others, as `(shape, seed, k, box, level-by-level box)`. Each case of
/// the remainder `if` is now cut at the starts of the pieces of the class ranges next to it,
/// which cuts out the holes again; every box but [`HOLE_WIDER`] lies within the level-by-level
/// one.
const CUT_BOXES: [(usize, u64, usize, Boxes, Boxes); 7] = [
    (3, 1, 2, &[(-4, -4), (-1, 59)], &[(-4, -4), (-1, 59)]),
    (
        3,
        1,
        5,
        &[(-58, -58), (-55, -13), (-10, -4), (-2, 59)],
        &[(-58, -58), (-55, -4), (-2, 59)],
    ),
    (
        4,
        1,
        1,
        &[(-60, -60), (-58, -4), (-2, 58), (60, 60)],
        &[(-60, -60), (-58, -4), (-2, 58), (60, 60)],
    ),
    (4, 1, 2, &[(-4, -4), (2, 56)], &[(-4, -4), (2, 56)]),
    (
        4,
        1,
        5,
        &[(-58, -58), (-54, -16), (-10, -4), (-2, 58)],
        &[(-58, -58), (-52, -4), (-2, 58)],
    ),
    (
        4,
        1,
        13,
        &[(-56, -14), (-10, -10), (-8, -8), (-4, -4), (-2, 58)],
        &[(-56, -4), (-2, 58)],
    ),
    (
        4,
        3,
        5,
        &[(-60, -60), (-56, -6), (-4, -4), (-2, 58)],
        &[(-60, -60), (-56, -4), (-2, 58)],
    ),
];

/// The `(shape, seed, k)` of [`CUT_BOXES`] whose box is wider than level by level at `-54` and
/// `-53`, 2 points (COMPLEXITY.md S22-hole-summaries): a hole of the domain of `x` cut each
/// summary there, which narrowed the hull of a case; the summaries no longer cut at holes.
const HOLE_WIDER: (usize, u64, usize) = (4, 1, 5);

/// COMPLEXITY.md S22-case-cuts: the boxes of [`CUT_BOXES`], each but [`HOLE_WIDER`] within its
/// level-by-level box, and agreeing with the interpreter.
#[test]
fn remainder_cases_cut_at_their_neighbors_keep_the_holes() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(60), Demand::Bool(true));
        for (s, seed, k, want, level) in CUT_BOXES {
            let shape = REMAINDER_SHAPES[s];
            let t = remainder_shape(shape, moved_remainder_chain(seed, k, "x", 3));
            let p = preimage(&t, &ds, &d);
            let (want, level) = (pieces(want), pieces(level));
            assert_eq!(p.domains["x"], want, "{shape}, seed {seed}, k = {k}: {t}");
            let within = (s, seed, k) != HOLE_WIDER;
            assert_eq!(
                want.is_subset(&level),
                within,
                "{shape}, seed {seed}, k = {k}"
            );
            check(&t, &ds, &d, &p, (-20, 20));
            check(&t, &ds, &d, &p, (45, 60));
        }
    });
}

/// The boxes of `x` at a modulus other than 3 that cutting at the neighbors leaves wider than
/// the level-by-level translation, or wider at some points and narrower at others, as
/// `(modulus, shape, seed, k, box, level-by-level box)`: a hole that only a farther range's
/// start cuts out stays filled (COMPLEXITY.md S22-case-cuts).
const FARTHER_HOLES: [(i64, usize, u64, usize, Boxes, Boxes); 3] = [
    (
        5,
        4,
        3,
        5,
        &[(-58, -58), (-56, -56), (-54, 58), (60, 60)],
        &[(-58, -58), (-56, -56), (-54, -4), (-2, 58), (60, 60)],
    ),
    (
        7,
        4,
        3,
        2,
        &[(-60, -60), (-58, 0), (2, 50), (58, 58)],
        &[(-60, -60), (-58, -4), (-2, 50), (58, 58)],
    ),
    (
        7,
        4,
        3,
        5,
        &[(-60, -60), (-58, -58), (-54, 52), (56, 58), (60, 60)],
        &[
            (-60, -60),
            (-58, -58),
            (-54, -4),
            (-2, 52),
            (56, 58),
            (60, 60),
        ],
    ),
];

/// COMPLEXITY.md S22-case-cuts: the five shapes of [`REMAINDER_SHAPES`] on the chains of seeds
/// 1 to 3 at k = 1, 2, 5, 13 of modulus `m`, over `x` and `y` in `[-60, 60]`: every box agrees
/// with the interpreter, the boxes of [`FARTHER_HOLES`] are as recorded, and the boxes of `x`
/// hold `points` points in all. Measured when this was written: at modulus 5, 6951 points,
/// against 7030 level by level and 6936 cut at every range's starts; at modulus 7, 6906
/// against 6951 and 6864. Level by level, a box is wider than cut at the neighbors only in
/// [`FARTHER_HOLES`]. Since row S22-hole-summaries no summary is cut at a hole of the domain
/// of `x`, which widened 3 boxes at modulus 5 by 2 to 4 points, 6959 points (exact: 5482),
/// and none at modulus 7. A change that loses more holes raises `points`.
fn boxes_at_modulus(m: i64, points: usize) {
    on_big_stack(|| {
        let (ds, d) = (xy_in(60), Demand::Bool(true));
        let mut total = 0;
        for (s, shape) in REMAINDER_SHAPES.iter().enumerate() {
            for seed in 1..=3 {
                for k in [1, 2, 5, 13] {
                    let t = remainder_shape(shape, moved_remainder_chain(seed, k, "x", m));
                    let p = preimage(&t, &ds, &d);
                    check(&t, &ds, &d, &p, (-60, 60));
                    let x = &p.domains["x"];
                    total += (-60..=60).filter(|&v| x.contains(v)).count();
                    let held = FARTHER_HOLES.iter().find(|(fm, fs, fseed, fk, _, _)| {
                        (*fm, *fs, *fseed, *fk) == (m, s, seed, k)
                    });
                    if let Some((_, _, _, _, want, level)) = held {
                        assert_eq!(*x, pieces(want), "{shape}, seed {seed}, k = {k}: {t}");
                        assert!(!pieces(want).is_subset(&pieces(level)));
                    }
                }
            }
        }
        assert_eq!(total, points, "points of the boxes of `x` at modulus {m}");
    });
}

#[test]
fn remainder_cases_cut_at_their_neighbors_at_modulus_5() {
    boxes_at_modulus(5, 6959);
}

#[test]
fn remainder_cases_cut_at_their_neighbors_at_modulus_7() {
    boxes_at_modulus(7, 6906);
}

/// The constant `c(j)` of level `j` of [`spread_remainder_chain`] and
/// [`select_remainder_chain`], spread over `[-100, 99]`.
fn spread_constant(j: i64) -> i64 {
    (53 * j) % 200 - 100
}

/// The guard `x mod 1024 != r(j)` of level `j`, the `r(j)` distinct for `j < 1024`.
fn spread_guard(j: i64) -> Term {
    let r = (37 * j) % 1024;
    prim(Prim::Ne, prim(Prim::Mod, var("x"), int(1024)), int(r))
}

/// The chain of `k` guards `x mod 1024 != r(j)`, else `max(t, c(j))` ([`spread_constant`]):
/// in class `r(j)` the chain is `max(x, c(j))`, and `x` in every other class, so `2k + 1`
/// ranges of classes. Under `c <= 2` ([`below_three_and_even_y`]) the domain of `x` narrows
/// to `x <= 2`, where `max(x, c(j))` is two pieces when `c(j) <= 1` and the constant `c(j)`
/// otherwise; each class with `c(j) > 2` meets the demand nowhere, so the narrowed domain has
/// a hole at each of its members in the first period of `[-100000, 2]`, about `k / 2` holes.
/// Cutting each case at every other range's starts would make `O(k^2)` cases, and so would
/// cutting each class's summary at every hole (COMPLEXITY.md S22-hole-summaries).
fn spread_remainder_chain(k: usize) -> Term {
    chain(k, var("x"), spread_guard, |j, t| {
        prim(Prim::Max, t, int(spread_constant(j)))
    })
}

/// The chain of `k` guards `x mod 1024 != r(j)` of [`spread_remainder_chain`], else `if x <=
/// -50 { max(t, c(j)) } else { t }`: an `if` on a test that reads no remainder, whose arms
/// read it in different ways, so that each range of classes is sliced at `-50` by itself
/// ([`Walk::pa_select`]). The holes are those of [`spread_remainder_chain`].
fn select_remainder_chain(k: usize) -> Term {
    chain(k, var("x"), spread_guard, |j, t| {
        let low = prim(Prim::Le, var("x"), int(-50));
        let clamped = prim(Prim::Max, t.clone(), int(spread_constant(j)));
        Term::If(Shared::new(low), Shared::new(clamped), Shared::new(t))
    })
}

/// `c <= 2 && y mod 2 == 0` for the chain `c`.
fn below_three_and_even_y(c: Term) -> Term {
    let even = prim(Prim::Eq, prim(Prim::Mod, var("y"), int(2)), int(0));
    prim(Prim::And, prim(Prim::Le, c, int(2)), even)
}

/// The number of cases of the definition of the remainder `if` in the relation of `p`.
fn remainder_cases(p: &Preimage) -> usize {
    let rel = p.relation.as_ref().expect("a relation");
    let cases = (rel.defs.iter())
        .filter(|(_, what, _)| what.contains(" if "))
        .map(|(_, what, _)| what.matches(" if ").count());
    let cases: Vec<usize> = cases.collect();
    assert_eq!(cases.len(), 1, "one remainder `if`: {:?}", rel.defs);
    cases[0]
}

/// COMPLEXITY.md S22-case-cuts and S22-hole-summaries: the cases of the chain of
/// [`spread_remainder_chain`] stay linear in `k`, `2k + 1 + 3T` for the `T` levels with
/// `c(j) <= 1`: `2k + 1` ranges, the second piece of each of the `T` ranges of two pieces, and
/// each of their two neighbors, ranges of one piece, cut at its start. The ranges of a
/// constant are not cut, and no case is cut at a hole of the domain. Cut at every other
/// range's starts they would be `O(k^2)`, and cut at every hole they were 229 and 953 at
/// k = 16 and 32. The answer agrees with the interpreter, also at the holes.
#[test]
fn remainder_cases_cut_at_their_neighbors_stay_linear() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(100000), Demand::Bool(true));
        for k in [1, 4, 16, 64] {
            let t = below_three_and_even_y(spread_remainder_chain(k));
            let p = preimage(&t, &ds, &d);
            let two = (1..=k as i64).filter(|&j| spread_constant(j) <= 1).count();
            assert_eq!(remainder_cases(&p), 2 * k + 1 + 3 * two, "k = {k}");
            check(&t, &ds, &d, &p, (-110, -90));
            check(&t, &ds, &d, &p, (90, 110));
            check(&t, &ds, &d, &p, (-100000, -99900));
        }
    });
}

/// COMPLEXITY.md S22-hole-summaries: the cases of the chain of [`select_remainder_chain`],
/// whose ranges of classes are each sliced at `-50`, stay within `5k + 1` (21, 78, 306 at
/// k = 4, 16, 64; cut at every hole of the domain they were 278 and 3798 at k = 16 and 64).
/// The answer agrees with the interpreter, also at the holes.
#[test]
fn remainder_cases_sliced_by_a_test_stay_linear() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(100000), Demand::Bool(true));
        for k in [1, 4, 16, 64] {
            let t = below_three_and_even_y(select_remainder_chain(k));
            let p = preimage(&t, &ds, &d);
            let cases = remainder_cases(&p);
            assert!(cases <= 5 * k + 1, "k = {k}: {cases} cases");
            check(&t, &ds, &d, &p, (-110, -90));
            check(&t, &ds, &d, &p, (-60, -40));
            check(&t, &ds, &d, &p, (-100000, -99900));
        }
    });
}

/// COMPLEXITY.md S22-case-cuts and S22-hole-summaries: the linear stage on the chain of
/// [`spread_remainder_chain`], whose cases would be `O(k^2)` cut at every other range's starts
/// or at every hole of the domain, does work of order `k` from `k` to `8k`.
#[test]
fn remainder_cases_cut_at_their_neighbors_scale() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(100000), Demand::Bool(true));
        let n = 8;
        let terms = scaling::inputs(n, |k| below_three_and_even_y(spread_remainder_chain(k)));
        scaling::check("cases of a spread remainder chain", n, |k| {
            preimage(&terms[&k], &ds, &d);
        });
    });
}

/// COMPLEXITY.md S22-hole-summaries: the linear stage on the chain of
/// [`select_remainder_chain`], whose slices would be `O(k^2)` cut at every hole of the
/// domain, does work of order `k` from `k` to `8k`.
#[test]
fn remainder_cases_sliced_by_a_test_scale() {
    on_big_stack(|| {
        let (ds, d) = (xy_in(100000), Demand::Bool(true));
        let n = 8;
        let terms = scaling::inputs(n, |k| below_three_and_even_y(select_remainder_chain(k)));
        scaling::check("cases of a sliced remainder chain", n, |k| {
            preimage(&terms[&k], &ds, &d);
        });
    });
}

/// `x` in `[-100000, 100000]` with `h` holes of one point, spread evenly, and `y` in
/// `[-100000, 100000]`.
fn x_with_holes(h: usize) -> Domains {
    let step = 198000 / h as i64;
    let mut ps = Vec::with_capacity(h + 1);
    let mut lo = -100000;
    for j in 0..h as i64 {
        let at = -99000 + step * j;
        ps.push((lo, at - 1));
        lo = at + 1;
    }
    ps.push((lo, 100000));
    over(&[("x", pieces(&ps)), ("y", IntervalSet::of(-100000, 100000))])
}

/// COMPLEXITY.md S22-hole-summaries: reading the test `x mod 1024 != r(j)` of each level of
/// [`spread_remainder_chain`] by its classes, with `16k` holes in the domain of `x`, reads
/// pieces of that domain of order `k log k` from `k` to `8k`: each range of classes is read
/// within the hull of the domain, a box is tested against the holes by binary search, and the
/// union is met with the domain once. Meeting each range with the whole domain read `O(k)`
/// pieces for each of `O(k)` ranges, `O(k^2)`: 2193 and 132225 pieces at `k = 8` and `64`,
/// 60 times (negative control, not committed), where this reads 245 and 2693, 11 times.
#[test]
fn class_ranges_read_the_holes_once() {
    on_big_stack(|| {
        let d = Demand::Bool(true);
        let n = 8;
        let reads = |k: usize| {
            let t = counted_shapes(spread_remainder_chain(k))[4].clone();
            let ds = x_with_holes(16 * k);
            class_domain_reads();
            preimage(&t, &ds, &d);
            class_domain_reads()
        };
        let (small, large) = (reads(n), reads(scaling::FACTOR * n));
        assert!(small > 0, "the tests are read by their classes");
        let ratio = large as f64 / small as f64;
        assert!(
            ratio <= scaling::limit(n, scaling::FACTOR * n, 1),
            "pieces of the domain read at sizes {n} and {}: {small} and {large}, {ratio:.1} times, \
             over {}",
            scaling::FACTOR * n,
            scaling::limit(n, scaling::FACTOR * n, 1)
        );
    });
}

/// COMPLEXITY.md S22-fwd-holes: the forward transfer of the levels of
/// [`spread_remainder_chain`], with `64k` holes in the domain of `x`, in the second program of
/// [`counted_shapes`], makes integer sets of pieces of order `k`, from `k` to `8k`: the domain
/// of `x` is shared, not copied, and a join or a `max` keeps its operands and its bounds, so
/// no set lists the holes again where no reader asks for its pieces. Copying the holes into
/// each level's set made `O(k * H)` pieces.
#[test]
fn forward_sets_of_a_chain_share_the_holes_scale() {
    on_big_stack(|| {
        let d = Demand::Bool(true);
        let n = 8;
        let made = |k: usize| {
            let t = counted_shapes(spread_remainder_chain(k))[1].clone();
            let ds = x_with_holes(64 * k);
            forward_pieces();
            let p = preimage(&t, &ds, &d);
            assert!(p.exact, "the preimage at k = {k} is exact");
            forward_pieces()
        };
        let (small, large) = (made(n), made(scaling::FACTOR * n));
        assert!(small > 0, "the forward transfer makes sets");
        let ratio = large as f64 / small as f64;
        assert!(
            ratio <= scaling::limit(n, scaling::FACTOR * n, 1),
            "pieces of the forward sets at sizes {n} and {}: {small} and {large}, {ratio:.1} \
             times, over {}",
            scaling::FACTOR * n,
            scaling::limit(n, scaling::FACTOR * n, 1)
        );
    });
}

/// COMPLEXITY.md S22-split-holes: the split of the levels of [`spread_remainder_chain`] by
/// their `2k + 1` ranges of classes, with `64k` holes in the domain of `x`, in the second
/// program of [`counted_shapes`], does work and allocates bytes of order `k log k` from `k` to
/// `8k`: the classes' runs share the domain of `x`, and their sets of `x` are compared and
/// joined without listing the holes once for each class. Copying the domain into each run,
/// meeting each class's set with it and comparing the sets piece by piece made `O(k * H)`.
/// Measured with `glibc.malloc.tcache_count=0`, load about 20: 10.1 times the instructions and
/// 11.0 times the bytes from `k = 8` to `64`; main at 01eb1be0 took 19.3 times the instructions
/// and 26.9 times the bytes (limit 17.6).
#[test]
fn split_classes_share_the_holes_scale() {
    on_big_stack(|| {
        let d = Demand::Bool(true);
        let n = 8;
        let t = scaling::inputs(n, |k| counted_shapes(spread_remainder_chain(k))[1].clone());
        let ds = scaling::inputs(n, |k| x_with_holes(64 * k));
        scaling::check(
            "split of a spread remainder chain over a domain with holes",
            n,
            |k| {
                let p = preimage(&t[&k], &ds[&k], &d);
                assert!(p.exact, "the preimage at k = {k} is exact");
            },
        );
    });
}

/// The cases of [`split_pieces_reach_each_kind_of_touched`]: programs split by the remainder of
/// `x` over domains whose pieces were placed so that, per modulus, some piece of a class's set
/// has an infinite end, spans a period (`hi - lo = |m| - 1` exactly, and longer), keeps its
/// remainders in one range, wraps past `m` into an earlier class, or wraps past `m` back into
/// the class it started in. `m = -5` reads its remainders by `5`, as `in_class` does.
fn touched_cases() -> Vec<(String, Term, Domains, Demand)> {
    let ite = |g: Term, a: Term, b: Term| Term::If(Shared::new(g), Shared::new(a), Shared::new(b));
    let tt = || Term::Lit(Value::Bool(true));
    let ff = || Term::Lit(Value::Bool(false));
    let rem = |m: i64| prim(Prim::Mod, var("x"), int(m));
    // The pieces `ps` with a half-line below and above.
    let half = |ps: &[(i64, i64)]| {
        let mut all: Vec<(End, End)> = ps.iter().map(|&(a, b)| (End::of(a), End::of(b))).collect();
        all.insert(0, (End::NegInf, End::of(-200)));
        all.push((End::of(5000), End::PosInf));
        IntervalSet::from_pieces(all)
    };
    // `m = 10`: true where the remainder is 3 or 8. The pieces: remainders 8 to 3 (wrapping
    // past `m`), 3 alone, 7 to 4 (wrapping past `m` back into the class of [4, 7]), 6 to 3, a
    // whole period, 5 to 8, 5 to 3 (`hi - lo = m - 2`), and `hi - lo = m - 1`.
    let ten_ps = [
        (-32, -27),
        (13, 13),
        (17, 24),
        (26, 33),
        (40, 49),
        (55, 58),
        (65, 73),
        (81, 90),
    ];
    let ten = ite(
        prim(Prim::Eq, rem(10), int(3)),
        tt(),
        prim(Prim::Eq, rem(10), int(8)),
    );
    // `m = -5`: the remainders by 5. The pieces: remainders 4 to 2, 2 to 0, one point,
    // [-20, 20], 4 to 2 again, 0 to 3, 1 to 2, 4 to 1 (`hi - lo = 2`), and `hi - lo = |m| - 1`.
    let five_ps = [
        (-61, -58),
        (-53, -50),
        (-45, -45),
        (-20, 20),
        (44, 47),
        (50, 53),
        (56, 57),
        (59, 61),
        (70, 74),
    ];
    // Each class bounds `x` on another side, so the classes' sets differ outside [-40, 40].
    let five = ite(
        prim(Prim::Ge, rem(-5), int(2)),
        prim(Prim::Le, var("x"), int(40)),
        prim(Prim::Ge, var("x"), int(-40)),
    );
    // One guard, true in the class [1, 4]: a piece whose remainders run from 4 past `m` to 1
    // or 2 wraps back into that class.
    let five_bare = prim(Prim::Ne, rem(-5), int(0));
    // `m = -5` chained, over `x` unbounded and over the pieces above.
    let five_chain = ite(
        prim(Prim::Eq, rem(-5), int(4)),
        prim(Prim::Ge, var("x"), int(3)),
        ite(
            prim(Prim::Lt, rem(-5), int(2)),
            ff(),
            prim(Prim::Le, var("x"), int(-8)),
        ),
    );
    // `m = 7`, the arms moving and reflecting `x`: the classes' sets are half-lines.
    let seven = prim(
        Prim::Le,
        ite(
            prim(Prim::Eq, rem(7), int(2)),
            prim(Prim::Add, var("x"), int(3)),
            prim(Prim::Sub, int(5), var("x")),
        ),
        int(20),
    );
    let seven_ps = [(-150, -140), (-30, -26), (16, 19), (24, 40)];
    let mut cases = Vec::new();
    for (name, t, x) in [
        ("ten bounded", ten.clone(), pieces(&ten_ps)),
        ("ten", ten, half(&ten_ps)),
        ("five bounded", five.clone(), pieces(&five_ps)),
        ("five", five, half(&five_ps)),
        ("five_bare bounded", five_bare.clone(), pieces(&five_ps)),
        ("five_bare", five_bare, half(&five_ps)),
        (
            "five_chain unbounded",
            five_chain.clone(),
            IntervalSet::top(),
        ),
        ("five_chain", five_chain, half(&five_ps)),
        ("seven", seven, half(&seven_ps)),
    ] {
        for b in [true, false] {
            cases.push((
                format!("{name} {b}"),
                t.clone(),
                over(&[("x", x.clone())]),
                Demand::Bool(b),
            ));
        }
    }
    cases
}

/// COMPLEXITY.md S22-split-holes: the split of programs over domains whose pieces wrap past
/// the modulus, span a whole period or have an infinite end, for `m = 10`, `m = -5` and `m = 7`
/// ([`touched_cases`]), gives byte for byte the preimage that main gave at 01eb1be0, before the
/// classes shared the domain (`touched_cases.txt`, one line per case, written by main then).
/// For `m = 10` and for `m = -5`, each kind of answer of `touched` occurs at least once.
#[test]
fn split_pieces_reach_each_kind_of_touched() {
    on_big_stack(|| {
        let want = include_str!("touched_cases.txt");
        let cases = touched_cases();
        assert_eq!(cases.len(), want.lines().count());
        let mut sums = [TouchedPaths::default(); 2];
        touched_paths();
        for ((name, t, ds, d), w) in cases.into_iter().zip(want.lines()) {
            let p = preimage(&t, &ds, &d);
            assert_eq!(format!("{name}\t{p:?}"), w, "{name}");
            let c = touched_paths();
            let s = match name.split(' ').next() {
                Some("ten") => &mut sums[0],
                Some("five" | "five_bare" | "five_chain") => &mut sums[1],
                _ => continue,
            };
            s.half_line += c.half_line;
            s.period += c.period;
            s.one_range += c.one_range;
            s.two_ranges += c.two_ranges;
            s.wrapped_into_its_class += c.wrapped_into_its_class;
        }
        for (m, s) in [10, -5].into_iter().zip(sums) {
            assert!(
                s.half_line > 0
                    && s.period > 0
                    && s.one_range > 0
                    && s.two_ranges > 0
                    && s.wrapped_into_its_class > 0,
                "m = {m}: {s:?}"
            );
        }
    });
}

/// COMPLEXITY.md S22-shapes-linear: whether the box of the first program of
/// [`counted_shapes`] over the levels of [`spread_remainder_chain`] is exact, with `64k` holes
/// in the domain of `x`, costs work of order `k` from 128 holes to 1024: 6.75 times the
/// instructions and 6.82 times the bytes for 8 times the holes, where probing to the end took
/// 17.4 times the bytes. The question has points, but the first search for one takes a piece
/// of `x` that the `if` of the chain cannot follow, and the probe after it
/// ([`zedc::store::presburger`]'s `has_point`) stops at its first point; probing to the end
/// found a point for each of the `32k` pieces of `x`, each at the cost of the whole formula,
/// `O(k^2)`.
///
/// Since PROJECT-canon-precision the probe runs whether or not the first search found a point,
/// and the domain of `x`, a set of values of one atom, is kept untested (`one_atom_set` in
/// `zedc_presburger`). The probe still asks one search per case of the chain, `k` in all, and
/// each search read the `64k` pieces of the domain: 9.4, 11.1 and 12.7 times (bytes, limit
/// 11.73, failed) from 128, 256 and 512 holes to 8 times as many, `O(k^2)`. Testing each piece
/// of the domain as well took 12.55 times from 128. A search now leaves the domain out and
/// looks its point up in it by binary search: 7.4, 8.3 and 9.7 times, where the probe only on
/// a failed search, which main ran, took 7.4, 8.5 and 9.2 times. The second test, at 512, is
/// the one that failed.
fn the_box_of_a_chain_over_holes_is_tested_in_linear_work(n: usize) {
    on_big_stack(|| {
        let d = Demand::Bool(true);
        let make = |holes: usize| {
            let k = holes / 64;
            let t = counted_shapes(spread_remainder_chain(k))[0].clone();
            (t, x_with_holes(holes))
        };
        let inputs = scaling::inputs(n, make);
        for (t, ds) in inputs.values() {
            assert!(
                !preimage(t, ds, &d).exact,
                "the box has points outside the preimage"
            );
        }
        scaling::check(
            "the exactness test of the box of a chain over the holes of `x`",
            n,
            |holes| {
                let (t, ds) = &inputs[&holes];
                preimage(t, ds, &d);
            },
        );
    });
}

#[test]
fn the_box_of_a_chain_over_many_holes_is_tested_in_linear_work() {
    the_box_of_a_chain_over_holes_is_tested_in_linear_work(128);
}

#[test]
fn the_box_of_a_chain_over_more_holes_is_tested_in_linear_work() {
    the_box_of_a_chain_over_holes_is_tested_in_linear_work(512);
}

/// Plan item SOUND-div-exact: `c^0` is 1 where `c` is defined and fails where `c` does
/// (DESIGN.md sec:failure: a loose atom operand selects no arrow and passes out), so a power 0
/// of a quotient by a term is not 1 where the divisor is 0. The linear stage read `c^0` as 1
/// without reading `c`, and so marked every `x` exact, in both transfers: the interpreter
/// refutes that at `x == -1` for the first two terms (random_terms, seed 1002) and at
/// `x == 0` for the third (seed 1006, its `if` arm). The base must now translate where the
/// relation does not track failure. Each result is checked against the interpreter.
#[test]
fn a_power_zero_of_a_quotient_by_a_term_is_not_exact_where_the_divisor_is_zero() {
    let x = || var("x");
    let pow0 = |t: Term| prim(Prim::Pow, t, int(0));
    let below = |hi: i64| Demand::Ints(IntervalSet::range(End::NegInf, End::of(hi)));
    let cases = [
        (
            pow0(prim(Prim::IntDiv, int(-4), prim(Prim::Add, int(1), x()))),
            Demand::Ints(IntervalSet::top()),
        ),
        (
            pow0(Term::Prim(
                Prim::Neg,
                vec![prim(
                    Prim::IntDiv,
                    prim(Prim::Mul, int(2), int(-2)),
                    prim(Prim::Add, int(1), x()),
                )],
            )),
            Demand::Ints(IntervalSet::range(End::of(-22), End::PosInf)),
        ),
        (
            pow0(prim(Prim::IntDiv, int(-3), prim(Prim::Max, x(), int(-2)))),
            below(34),
        ),
    ];
    let ds = over(&[("x", IntervalSet::top())]);
    for (t, d) in cases {
        let now = preimage(&t, &ds, &d);
        let then = before::preimage(&t, &ds, &old(&d));
        assert!(
            !refuted(&t, &ds, &d, &now.domains, now.exact),
            "{t}: {now:?}"
        );
        assert!(
            !refuted(&t, &ds, &d, &then.domains, then.exact),
            "{t} before: {then:?}"
        );
    }
}

/// Cases `from..to` of [`random_guarded_chains`]' sequence, each run by the transfer and by
/// the transfer before it ([`before`]) as written and with the disjunctions of every
/// projection, and the disjuncts of each, read in reverse
/// ([`zedc::store::presburger::with_parts_reversed`]): the boxes and their exactness are the
/// same both ways (item PROJECT-canon-precision). Before that item, the transfer before gave
/// 17 of the 4000 cases different boxes in reverse: a disjunct with no point stayed when the
/// greedy search found a point first, and a disjunction left with one disjunct did not start
/// another round of the propagation.
fn reversed_parts_give_the_same_boxes(from: usize, to: usize) {
    use zedc::store::presburger::with_parts_reversed as reversed;
    on_big_stack(|| {
        let mut rng = Rng::new(22);
        let mut differ = Vec::new();
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
            if i < from {
                continue;
            }
            let (a, b) = (preimage(&t, &ds, &d), reversed(|| preimage(&t, &ds, &d)));
            if a.domains != b.domains || a.exact != b.exact {
                differ.push(format!(
                    "case {i}: {:?} | reversed {:?}",
                    a.domains, b.domains
                ));
            }
            let d = old(&d);
            let (a, b) = (
                before::preimage(&t, &ds, &d),
                reversed(|| before::preimage(&t, &ds, &d)),
            );
            if a.domains != b.domains || a.exact != b.exact {
                differ.push(format!(
                    "case {i} before: {:?} | reversed {:?}",
                    a.domains, b.domains
                ));
            }
        }
        assert!(
            differ.is_empty(),
            "boxes that depend on the order:\n{}",
            differ.join("\n")
        );
    });
}

#[test]
fn reversed_parts_give_the_same_boxes_0() {
    reversed_parts_give_the_same_boxes(0, 1000);
}

#[test]
fn reversed_parts_give_the_same_boxes_1() {
    reversed_parts_give_the_same_boxes(1000, 2000);
}

#[test]
fn reversed_parts_give_the_same_boxes_2() {
    reversed_parts_give_the_same_boxes(2000, 3000);
}

#[test]
fn reversed_parts_give_the_same_boxes_3() {
    reversed_parts_give_the_same_boxes(3000, 4000);
}

/// `c - i` with `c = 4n + 3` under a demand of `2n` pieces, `n` on each side of zero, by the
/// transfer before: the reflections of the demand's pieces are all positive, so the forward
/// image of `{c} - z` caps them to the `n` pieces of one sign region of an operand and has
/// holes, and the box is exact only because the domain of `i`, the reflection itself, takes no
/// value in them (S22-exact-mislabel). The check (the reflection of the demand, the image less
/// it, and the meet with the forward image of `i`) costs `O(n log n)` at most.
#[test]
fn constant_minus_holes_scale() {
    let case = |n: usize| {
        let n = n as i64;
        let c = 4 * n + 3;
        let z = pieces(&(-n..n).map(|j| (4 * j, 4 * j + 1)).collect::<Vec<_>>());
        let reflected = (-n..n).rev().map(|j| (c - 4 * j - 1, c - 4 * j));
        let ds = over(&[("i", pieces(&reflected.collect::<Vec<_>>()))]);
        (prim(Prim::Sub, int(c), var("i")), ds, Demand::Ints(z))
    };
    let n = 256;
    let (a, b) = (case(n), case(n * scaling::FACTOR));
    on_big_stack(|| {
        for (t, ds, d) in [&a, &b] {
            let p = before::preimage(t, ds, &old(d));
            assert!(p.exact && p.domains == *ds, "{t}: {p:?}");
        }
        scaling::check("the transfer before of `c - i` with holes", n, |k| {
            let (t, ds, d) = if k == n { &a } else { &b };
            before::preimage(t, ds, &old(d));
        });
    });
}

/// The chain `t_j = if (i <= j mod 7 - 3) { t } else { (3j + 1) - t }` of `n` levels over `i`
/// in `[-20, 20]`, asked `t_n != 0`. Every level's `c - t` has holes that meet the forward
/// image of `t`, and the guards remove them, so the preimage is exact. The transfer before
/// carries the holes down as one set of doubted values and meets them with the guards' boxes
/// where `i` is read (S22-guard-exact). Measured with the whole preimage: 63 and 594 ms at 256
/// and 2,048 (9.4 times); a transfer of the holes at each level as a demand of their own, met
/// with the guards' boxes (not kept), 9.4 and 511 ms at 32 and 256 (55 times); the check before
/// (S22-exact-mislabel), which left these boxes not exact, 69 ms and 6.1 s at 8 and 64, all of
/// it in the stages after the transfer (load about 18).
#[test]
fn guarded_holes_scale() {
    let case = |n: usize| {
        let g = |j: i64| prim(Prim::Le, var("i"), int(j % 7 - 3));
        let t = chain(n, var("i"), g, |j, t| prim(Prim::Sub, int(3 * j + 1), t));
        (prim(Prim::Ne, t, int(0)), i_in(-20, 20), Demand::Bool(true))
    };
    let n = 256;
    let (a, b) = (case(n), case(n * scaling::FACTOR));
    on_big_stack(|| {
        for (t, ds, d) in [&a, &b] {
            let p = before::preimage(t, ds, &old(d));
            assert!(p.exact && !p.enumerated, "{p:?}");
            assert_eq!(first_refuted(t, ds, d, &[(&p.domains, true)]), None);
        }
        scaling::check(
            "the transfer before of a guarded chain of `c - t` with holes",
            n,
            |k| {
                let (t, ds, d) = if k == n { &a } else { &b };
                before::preimage(t, ds, &old(d));
            },
        );
    });
}

/// The chain `t_j = if (i <= j mod 7 - 3) { t } else { c - t }` of `n` levels over `i` in
/// `[-20, 20]`, asked `t_n != 0`, with the constant `c = 2`, or `c = j mod 5`. The transfer
/// before is exact but for one doubted value of `i`, the point where `t_n` may be 0, and the
/// linear stage decides that one slice of the relation: the preimage is exact, the box less
/// that point. Measured with the whole preimage before, `c = 2`: 32.8 M and 263.8 M
/// instructions at 64 and 512 (8.0 times), 5.3 MB and 42.6 MB (8.0 times), limit 13.2, load
/// 31 (item PERF-s22-const-chain). Negative control, not kept: the linear stage by the
/// projection of the relation onto `i` and the decision of its complement leaves the box
/// `[-20, 20]` inexact, and, with that check skipped, allocates 247 MB and 3.53 GB (14.3
/// times) and takes 178 ms and 3.3 s, the decision alone up to 418 G instructions at 192
/// levels. With `c = j mod 5` the preimage is exact too; its transfer is not linear in the
/// chain (COMPLEXITY.md row C48), so it is checked here at one size only.
#[test]
fn constant_guarded_chains_scale() {
    let case = |n: usize, c: fn(i64) -> i64| {
        let g = |j: i64| prim(Prim::Le, var("i"), int(j % 7 - 3));
        let t = chain(n, var("i"), g, |j, t| prim(Prim::Sub, int(c(j)), t));
        (prim(Prim::Ne, t, int(0)), i_in(-20, 20), Demand::Bool(true))
    };
    let n = 64;
    let cases = scaling::inputs(n, |m| case(m, |_| 2));
    let moving = case(n, |j| j % 5);
    on_big_stack(|| {
        for (t, ds, d) in cases.values().chain([&moving]) {
            let p = before::preimage(t, ds, &old(d));
            assert!(p.exact && !p.enumerated, "{p:?}");
            assert_eq!(first_refuted(t, ds, d, &[(&p.domains, true)]), None);
        }
        scaling::check_order(
            "the transfer and linear stage before of a guarded chain of `2 - t`",
            n,
            1,
            |k| {
                let (t, ds, d) = &cases[&k];
                before::preimage(t, ds, &old(d));
            },
        );
    });
}
