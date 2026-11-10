//! Every preimage of the random terms of `s22.rs`, from the transfer and from the transfer
//! before (`zedc::store::preimage_ref`), checked against the interpreter, whether or not the
//! two agree: a point that meets the demand lies in the box, and where the box is marked exact,
//! a point in it meets the demand. `s22.rs` ran the interpreter only where the two transfers
//! differed, so a defect both share went unseen there (SOUND-div-exact: both read `c^0` as 1
//! without reading `c`, and marked `(-4 div (1 + x))^0` exact over every `x`); it checks both
//! boxes of every case since S22-exact-mislabel.
//!
//! The points checked on each input are the ends of each piece of the box and of the input's
//! domain, the integers next to each end, the middle of each piece, and the integers from -15 to
//! 15 (the window of `random.rs`, where a term over small constants fails or turns), those of
//! them in the domain (and, under `@exact`, in the input's class). An unbounded end is checked at the end of
//! `i64`. Each point of one input is checked with a few points of the other inputs (see
//! [`points`]). The tests split the runs of `s22.rs` by seed, each part one piece.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::preimage::{Classes, Demand, Domains, exact_preimage, preimage_listed};
use zedc::store::preimage_ref as before;

use super::meets;
use super::random::WINDOW;
use super::s22::{Case, RUNS, Run, cases};

/// The integer an end stands for: an unbounded end the end of `i64` on its side, a finite one
/// itself when it fits in `i64`.
fn end_value(e: &End) -> Option<i64> {
    match e {
        End::NegInf => Some(i64::MIN),
        End::PosInf => Some(i64::MAX),
        e => e.to_i64(),
    }
}

/// The values of one input checked: the ends of each piece of `bx` and of `domain`, the
/// integers next to each end, the middle of each piece, and the integers in [`WINDOW`], those in
/// `domain` and in `class`.
fn sample(bx: &IntervalSet, domain: &IntervalSet, class: &dyn Fn(i64) -> bool) -> Vec<i64> {
    let mut vs: BTreeSet<i64> = (WINDOW.0..=WINDOW.1).collect();
    for (lo, hi) in bx.pieces().chain(domain.pieces()) {
        let (Some(a), Some(b)) = (end_value(lo), end_value(hi)) else {
            continue;
        };
        for e in [a, b] {
            vs.extend(
                [e.checked_sub(1), Some(e), e.checked_add(1)]
                    .into_iter()
                    .flatten(),
            );
        }
        vs.insert(((a as i128 + b as i128) / 2) as i64);
    }
    vs.retain(|&v| domain.contains(v) && class(v));
    vs.into_iter().collect()
}

/// The points checked, as values in the order of the inputs: each value of `samples[j]` on
/// input `j`, with the other inputs at their anchors, the least and the greatest of their
/// samples inside the box and outside it.
///
/// Complexity tradeoff: the product of the inputs' samples would check every pair of ends of
/// two inputs, `O(s^k)` points for `k` inputs of `s` samples each; these points are
/// `O(k s 4^(k-1))`, linear in the samples (`k` is 2 in the random terms). Given up: a pair of
/// two inputs' values where neither is its input's least or greatest inside or outside the box,
/// such as a corner of two pieces inside the box; the box of a term over `x` and `y` that fails
/// only at such a pair, both away from the ends, is not refuted here.
fn points(samples: &[Vec<i64>], inside: &[&dyn Fn(i64) -> bool]) -> BTreeSet<Vec<i64>> {
    let anchors: Vec<Vec<i64>> = samples
        .iter()
        .zip(inside)
        .map(|(s, inside)| {
            let (ins, outs): (Vec<i64>, Vec<i64>) = s.iter().partition(|&&v| inside(v));
            let mut a: Vec<i64> = [ins.first(), ins.last(), outs.first(), outs.last()]
                .into_iter()
                .flatten()
                .copied()
                .collect();
            a.dedup();
            a
        })
        .collect();
    let mut out = BTreeSet::new();
    for (j, s) in samples.iter().enumerate() {
        for &v in s {
            let mut partial: Vec<Vec<i64>> = vec![vec![]];
            for (m, a) in anchors.iter().enumerate() {
                let here: &[i64] = if m == j { std::slice::from_ref(&v) } else { a };
                partial = partial
                    .into_iter()
                    .flat_map(|p| {
                        here.iter().map(move |&w| {
                            let mut p = p.clone();
                            p.push(w);
                            p
                        })
                    })
                    .collect();
            }
            out.extend(partial);
        }
    }
    out
}

/// The disagreements of the interpreter with the box `bx`, marked exact when `exact`, as the
/// preimage of `case`'s demand: each point checked that meets the demand outside the box, and,
/// when exact, each that fails it inside.
fn disagreements(case: &Case, who: &str, bx: &Domains, exact: bool) -> Vec<String> {
    let names: Vec<Arc<str>> = case.domains.keys().cloned().collect();
    let class = |n: &Arc<str>| {
        let c = case.classes.as_ref().and_then(|cs| cs.get(n)).cloned();
        move |v: i64| c.as_ref().is_none_or(|c| c.contains(&Num::from(v)))
    };
    let classes: Vec<_> = names.iter().map(class).collect();
    let samples: Vec<Vec<i64>> = names
        .iter()
        .zip(&classes)
        .map(|(n, c)| sample(&bx[n], &case.domains[n], c))
        .collect();
    let insides: Vec<Box<dyn Fn(i64) -> bool + '_>> = names
        .iter()
        .map(|n| {
            let s = &bx[n];
            Box::new(move |v| s.contains(v)) as Box<dyn Fn(i64) -> bool>
        })
        .collect();
    let inside: Vec<&dyn Fn(i64) -> bool> = insides.iter().map(|f| &**f).collect();
    let mut out = Vec::new();
    for pt in points(&samples, &inside) {
        let within = inside.iter().zip(&pt).all(|(f, &v)| f(v));
        let met = meets(&case.term, &names, &pt, &case.demand);
        if met != within && (met || exact) {
            let how = if met {
                "meets the demand outside"
            } else {
                "fails the demand inside"
            };
            out.push(format!(
                "{who}: {} over {:?}, listed {:?}, classes {:?}, demand {:?}: {pt:?} {how} \
                 the box {bx:?}, exact {exact}",
                case.term, case.domains, case.listed, case.classes, case.demand
            ));
        }
    }
    out
}

/// What the interpreter found in both transfers' preimages of one case.
struct Found {
    /// The disagreements of either transfer.
    disagreements: Vec<String>,
    /// How many of the two preimages are marked exact.
    exact: usize,
}

/// The disagreements of the interpreter with both transfers' preimages of `case`.
fn check(case: &Case) -> Found {
    let old = match &case.demand {
        Demand::Ints(z) => before::Demand::Ints(z.clone()),
        Demand::Bool(b) => before::Demand::Bool(*b),
    };
    let (t, ds) = (&case.term, &case.domains);
    let (now, then) = match &case.classes {
        None => {
            let (a, b) = (
                preimage_listed(t, ds, &case.listed, &case.demand),
                before::preimage_listed(t, ds, &case.listed, &old),
            );
            ((a.domains, a.exact), (b.domains, b.exact))
        }
        Some(cs) => {
            let cs: &Classes = cs;
            let (a, b) = (
                exact_preimage(t, ds, cs, &case.demand),
                before::exact_preimage(t, ds, cs, &old),
            );
            ((a.domains, a.exact), (b.domains, b.exact))
        }
    };
    let mut disagreements = disagreements(case, "transfer", &now.0, now.1);
    disagreements.extend(self::disagreements(
        case,
        "transfer before",
        &then.0,
        then.1,
    ));
    Found {
        disagreements,
        exact: now.1 as usize + then.1 as usize,
    }
}

/// Checks every case of `runs`: no disagreement and exactly `exact` preimages marked exact;
/// panics showing every disagreement.
fn check_runs(runs: &[Run], exact: usize) {
    let (mut found, mut exact_now) = (Vec::new(), 0);
    std::thread::scope(|s| {
        let thread = std::thread::Builder::new().stack_size(1 << 28);
        thread
            .spawn_scoped(s, || {
                for &run in runs {
                    cases(run, |c| {
                        let f = check(&c);
                        found.extend(f.disagreements);
                        exact_now += f.exact;
                    });
                }
            })
            .unwrap()
            .join()
            .unwrap()
    });
    assert!(
        found.is_empty(),
        "{} disagreements with the interpreter:\n{}",
        found.len(),
        found.join("\n")
    );
    assert_eq!(exact_now, exact, "the number of exact preimages changed");
}

/// Runs of mixed terms from the seeds `seeds`, 2000 cases each, every other case a test and
/// every third term reading through calls.
fn mixed(seeds: std::ops::Range<u64>) -> Vec<Run> {
    seeds
        .map(|seed| Run::Mixed {
            seed,
            cases: 2000,
            test: true,
            calls: true,
        })
        .collect()
}

/// Runs of terms of depth 4 from the seeds `seeds`.
fn deep(seeds: std::ops::Range<u64>) -> Vec<Run> {
    seeds.map(|seed| Run::Deep { seed }).collect()
}

/// Runs under `@exact` from the seeds `seeds`, tests from the odd ones.
fn exact(seeds: std::ops::Range<u64>) -> Vec<Run> {
    seeds
        .map(|seed| Run::Exact {
            seed,
            test: seed % 2 == 1,
        })
        .collect()
}

// The counts of exact preimages below rose when the solver's hulls became tighter
// (PRES-pendants-wider, 9992e356): s22_random_terms_match_the_interpreter_2 5477 -> 5479,
// more_mixed 36144 -> 36149 and 36031 -> 36039, more_deep 35172 -> 35184 and
// 35155 -> 35163. In each of the 22 cases that changed, a preimage that was not exact became
// exact with a box inside the old one (`x + (abs(x) - -5)` in [-19, -12] or [12, inf): `x`
// from `[0, inf)` to `[4, inf)`); this happened in the transfer before in all 22, and in the
// transfer too in the 13 where it was not exact already. The interpreter met the demand at
// every point checked in each new box (7 to 108 points) and at none checked outside it. No
// case lost its exact mark, and the counts of `c - e` did not change.
//
// more_mixed_terms_match_the_interpreter_1 rose again, 36149 -> 36153, when the solver began
// to answer a disjunction of difference rows exactly (PROJECT-each-chain-xr). Two cases
// changed, each from not exact to exact in both transfers, and no other case changed its box:
// `max(x ^ 0, x) == 10` demanded false keeps `x` in (-inf, 9] or [11, inf) instead of all of
// `x`, and `(if y <= 7 then -2 else x) != x or not (0 <= 7)` demanded true over `y` in [1, 12]
// keeps `y` in [1, 7] and `x` in (-inf, -3] or [-1, 22] instead of all of `x` up to 22. Each
// new box is the term's whole solution set, which the interpreter confirmed at every point
// checked. No case lost its exact mark, and the counts of `c - e` did not change.
//
// Five counts rose since PROJECT-canon-precision, which tests each disjunct for a point
// whether or not the greedy search found one first, but for the pieces of a set of values of
// one atom, so that the hulls no longer depend on the order of the parts:
// s22_random_terms_3 4432 -> 4433, more_mixed_1 36153 -> 36160, more_mixed_2 36039 -> 36048,
// more_deep_1 35184 -> 35186 and more_deep_2 35163 -> 35171, 27 exact marks in all. The
// boxes of 30 cases changed: in 12 both transfers went from not exact to exact, in 4 the
// transfer before became exact as the transfer was already, and in 12 the box narrowed and
// stayed inexact. Two moved the other way, each to the answer the old call gives with the
// parts reversed, so that the answer no longer depends on that order:
// `abs(((g2((x + -1)) mod -4) + (x + -2)))` with `g2 = v -> ((v * -2) + ((-5)^1))`, demanded
// in [-30, -27] or [4, 5], keeps `x` in [-5, -2] or [3, 6], not [-5, -4] or [3, 6], in both
// transfers, inexact as before; and the transfer before of `abs(((x + x) * 3))`, demanded in
// [-14, -13] or [20, 25], keeps all of `x`, inexact, not the exact {-4, 4} the transfer
// still gives. In each the piece below zero of the demand has no point and is kept, as every
// piece of a set of values of one atom is (`one_atom_set` in presburger.rs). The interpreter
// met the demand at every point checked in each new box and at none checked outside the
// exact ones, and the counts of `c - e` did not change. Measured against the old call (the
// probe only on a failed search) at the same seeds, in both orders of the parts: with the
// parts reversed the old call counts 36155 and 36041 for more_mixed_1 and _2, this one
// 36160 and 36048 in both orders.
//
// Until S22-exact-mislabel, the disagreements of the transfer before on a term of `c - e` were
// counted apart and not reported (13 cases in all: 3 in more_mixed_1, 5 in more_mixed_2, 2 in
// more_deep_1, 1 in more_deep_2, 1 each in more_exact_2 and _3): it took `c - x` as the forward
// image of `{c} - z`, whose cap on the pieces of each sign region merges pieces moved across
// zero, and kept the merged box exact. It now marks that box exact only when `x` takes no value
// of the image outside the reflection of `z`, so the count is gone and every disagreement is
// reported. 14 boxes of the transfer before changed, each to a subset of the box before, and
// none of the transfer: in 6 the box is the same and no longer exact, so the exact counts
// fell by 1 (more_deep_1, the `(min(0, -5) - (abs(x) + -4)) != -1` case; more_deep_2,
// `(2 - (5 * 6)) - (((x div -3)^2) div -4)`) and by 3 (more_mixed_2); in the other 8 the
// linear stage, which now runs on the box, narrows it to the exact set the transfer gives
// (`3 - x` over [-6, 4] demanded in [-24, -20] or [1, inf) keeps `x` in [-6, 2], not
// [-6, 4]), so the counts are unchanged. 13 of the 14 boxes before were refuted at the points
// checked here; the 14th, `x` in [-7, 47] for the `x div -3` case, fails at `x` from 21 to 44,
// outside the window and away from the ends, which a dense check of `x` from -7 to 60 showed.

#[test]
fn s22_random_terms_match_the_interpreter_1() {
    check_runs(&RUNS[0..4], 2353);
}

#[test]
fn s22_random_terms_match_the_interpreter_2() {
    check_runs(&RUNS[4..6], 5479);
}

#[test]
fn s22_random_terms_match_the_interpreter_3() {
    check_runs(&RUNS[6..18], 4433);
}

#[test]
fn more_mixed_terms_match_the_interpreter_1() {
    check_runs(&mixed(10_000..10_010), 36160);
}

#[test]
fn more_mixed_terms_match_the_interpreter_2() {
    check_runs(&mixed(10_010..10_020), 36045);
}

#[test]
fn more_deep_terms_match_the_interpreter_1() {
    check_runs(&deep(2_000..2_100), 35185);
}

#[test]
fn more_deep_terms_match_the_interpreter_2() {
    check_runs(&deep(2_100..2_200), 35170);
}

// The seeds 3000 to 3039 of `@exact` terms ran as one test of 56.5 s at load 41 (68.8 s at
// load 71), above the 60 s limit; each seed's 250 cases take 0.6 to 2.6 s, so they are split
// by seed into four tests, whose counts add up to the whole's 19134 (SPLIT-exact-oracle; the
// whole also counted 2 cases of `c - e` the transfer before got wrong, none since
// S22-exact-mislabel).

#[test]
fn more_exact_terms_match_the_interpreter_1() {
    check_runs(&exact(3_000..3_010), 4764);
}

#[test]
fn more_exact_terms_match_the_interpreter_2() {
    check_runs(&exact(3_010..3_020), 4778);
}

#[test]
fn more_exact_terms_match_the_interpreter_3() {
    check_runs(&exact(3_020..3_030), 4800);
}

#[test]
fn more_exact_terms_match_the_interpreter_4() {
    check_runs(&exact(3_030..3_040), 4792);
}

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

/// `x` in `x` and `y` in `y`.
fn xy(x: (i64, i64), y: (i64, i64)) -> Domains {
    [
        ("x".into(), IntervalSet::of(x.0, x.1)),
        ("y".into(), IntervalSet::of(y.0, y.1)),
    ]
    .into()
}

/// The case of `term` over `domains` with `demand`, under `@exact` when `exact`.
fn case(term: Term, domains: Domains, demand: Demand, exact: bool) -> Case {
    Case {
        what: "a case found by the interpreter",
        term,
        domains,
        listed: Default::default(),
        classes: exact.then(Classes::new),
        demand,
    }
}

fn ints(lo: End, hi: End) -> Demand {
    Demand::Ints(IntervalSet::range(lo, hi))
}

/// Under `@exact`, the search for a point of the box that fails the demand looked only for a
/// value outside it, so a point whose run fails passed: `1 div (y - x)` over `[0, 3]` squared
/// was marked exact, though it fails on the diagonal. Each case here is neither exact nor
/// refuted, in both transfers.
#[test]
fn a_point_that_fails_keeps_the_exact_search_from_marking_its_box_exact() {
    let top = Demand::Ints(IntervalSet::top());
    let cases = [
        case(
            prim(Prim::IntDiv, int(1), prim(Prim::Sub, var("y"), var("x"))),
            xy((0, 3), (0, 3)),
            top.clone(),
            true,
        ),
        case(
            prim(Prim::IntDiv, int(1), prim(Prim::Mod, var("y"), var("x"))),
            xy((2, 4), (0, 8)),
            top.clone(),
            true,
        ),
        case(
            prim(
                Prim::IntDiv,
                int(5),
                prim(Prim::Mod, var("y"), prim(Prim::Add, var("x"), int(1))),
            ),
            xy((-12, -3), (-7, 13)),
            ints(End::of(-26), End::PosInf),
            true,
        ),
    ];
    for c in cases {
        let f = check(&c);
        assert_eq!(f.disagreements, Vec::<String>::new(), "{}", c.term);
        assert_eq!(f.exact, 0, "{}", c.term);
    }
}

/// `max(a, b) >= lo` where `a` is: `b` must still be an integer, since a failing operand
/// fails the term (DESIGN.md sec:failure). The transfers took the union of the two operands'
/// preimages, and where one was empty kept the other, so `max(x, 0 mod y)` with `x` in
/// `[8, 12]` was exact over every `y`, `0` too. Each case here is refuted by the interpreter
/// at `y == 0` if its box holds `0` and is marked exact, in neither transfer. (Neither reads
/// `0 mod y` as `y != 0`, so the boxes keep `y == 0` and are not exact.)
#[test]
fn min_and_max_read_where_the_other_operand_fails() {
    let zero_mod_y = || prim(Prim::Mod, int(0), var("y"));
    let (up, low) = ((8, 12), (-12, -8));
    let cases = [
        (Prim::Max, up, ints(End::of(8), End::of(19))),
        (Prim::Max, up, ints(End::of(9), End::of(19))),
        (Prim::Min, low, ints(End::NegInf, End::of(-8))),
        (Prim::Min, low, ints(End::of(-20), End::of(-9))),
    ];
    for (p, x, demand) in cases {
        for t in [
            prim(p, var("x"), zero_mod_y()),
            prim(p, zero_mod_y(), var("x")),
        ] {
            let c = case(t, xy(x, (0, 7)), demand.clone(), false);
            let f = check(&c);
            assert_eq!(f.disagreements, Vec::<String>::new(), "{}", c.term);
        }
    }
}
