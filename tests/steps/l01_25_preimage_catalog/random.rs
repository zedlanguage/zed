//! Soundness on random terms: every point that meets the demand is in the preimage, and where
//! the preimage is marked exact, every point in it meets the demand. The terms mix the scalar
//! operators, including divisions that can fail, with tests, branches and `min` and `max`,
//! over random domains: finite ones the enumeration may take, and wide or unbounded ones it
//! cannot, so that the catalog's own exactness is checked too.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::Congruence;
use zedc::store::preimage::{Classes, Demand, Domains, exact_preimage, preimage};

use super::{check, meets, points};

/// The window each domain is checked over.
const WINDOW: (i64, i64) = (-15, 15);

fn lit(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

/// A random integer term over `x` and `y`, of depth at most `d`.
fn int_term(rng: &mut Rng, d: u32) -> Term {
    if d == 0 || rng.below(4) == 0 {
        return match rng.below(5) {
            0 | 1 => Term::Var("x".into()),
            2 => Term::Var("y".into()),
            _ => lit(rng.int(-6, 6)),
        };
    }
    let sub = |rng: &mut Rng| int_term(rng, d - 1);
    // One operand a constant half the time, as the exact entries need.
    let pair = |rng: &mut Rng, p: Prim| {
        let a = sub(rng);
        let b = if rng.below(2) == 0 {
            lit(rng.int(-5, 5))
        } else {
            sub(rng)
        };
        if rng.below(2) == 0 {
            prim(p, vec![a, b])
        } else {
            prim(p, vec![b, a])
        }
    };
    match rng.below(12) {
        0 | 1 => pair(rng, Prim::Add),
        2 => pair(rng, Prim::Sub),
        3 | 4 => pair(rng, Prim::Mul),
        5 => pair(rng, Prim::IntDiv),
        6 => pair(rng, Prim::Mod),
        7 => prim(Prim::Neg, vec![sub(rng)]),
        8 => prim(Prim::Abs, vec![sub(rng)]),
        9 => {
            let p = rng.pick(&[Prim::Min, Prim::Max]);
            pair(rng, p)
        }
        10 => prim(Prim::Pow, vec![sub(rng), lit(rng.int(0, 3))]),
        _ => {
            let g = bool_term(rng, d - 1);
            Term::If(Arc::new(g), Arc::new(sub(rng)), Arc::new(sub(rng)))
        }
    }
}

/// A random test over `x` and `y`, of depth at most `d`.
fn bool_term(rng: &mut Rng, d: u32) -> Term {
    let cmp = [Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge, Prim::Eq, Prim::Ne];
    if d == 0 || rng.below(3) != 0 {
        let a = int_term(rng, d.saturating_sub(1));
        let b = if rng.below(2) == 0 {
            lit(rng.int(-12, 12))
        } else {
            int_term(rng, d.saturating_sub(1))
        };
        return prim(rng.pick(&cmp), vec![a, b]);
    }
    let sub = |rng: &mut Rng| bool_term(rng, d - 1);
    match rng.below(4) {
        0 => prim(Prim::Not, vec![sub(rng)]),
        1 => prim(Prim::And, vec![sub(rng), sub(rng)]),
        2 => prim(Prim::Or, vec![sub(rng), sub(rng)]),
        _ => Term::If(Arc::new(sub(rng)), Arc::new(sub(rng)), Arc::new(sub(rng))),
    }
}

/// A random domain: small and finite, wide, or unbounded on one or both sides.
fn domain(rng: &mut Rng) -> IntervalSet {
    let lo = rng.int(-15, 10);
    let hi = lo + rng.int(0, 20);
    match rng.below(5) {
        0 | 1 => IntervalSet::range(End::Fin(lo), End::Fin(hi)),
        2 => IntervalSet::range(End::Fin(lo), End::PosInf),
        3 => IntervalSet::range(End::NegInf, End::Fin(hi)),
        _ => IntervalSet::top(),
    }
}

/// Random domains of `x` and `y`; one case in two is a listed box: `x` listed, its values
/// apart from one another, and `y` one value.
fn domains(rng: &mut Rng) -> Domains {
    let point = |v: i64| IntervalSet::from_pieces(vec![(End::Fin(v), End::Fin(v))]);
    let (x, y) = if rng.below(2) == 0 {
        let lo = rng.int(-15, 10);
        let xs = (0..rng.int(1, 8)).map(|k| (End::Fin(lo + 2 * k), End::Fin(lo + 2 * k)));
        (
            IntervalSet::from_pieces(xs.collect()),
            point(rng.int(-15, 15)),
        )
    } else {
        (domain(rng), domain(rng))
    };
    [("x", x), ("y", y)]
        .into_iter()
        .map(|(k, v)| (Arc::<str>::from(k), v))
        .collect()
}

/// A random demand on an integer term: up to two intervals.
fn int_demand(rng: &mut Rng) -> Demand {
    let mut pieces = Vec::new();
    for _ in 0..rng.int(1, 2) {
        let lo = rng.int(-30, 30);
        let lo_end = if rng.below(5) == 0 {
            End::NegInf
        } else {
            End::Fin(lo)
        };
        let hi_end = if rng.below(5) == 0 {
            End::PosInf
        } else {
            End::Fin(lo + rng.int(0, 15))
        };
        pieces.push((lo_end, hi_end));
    }
    Demand::Ints(IntervalSet::from_pieces(pieces))
}

/// Counts, over the cases run, of exact and enumerated results, so that a test that claims
/// nothing fails.
#[derive(Default, Debug)]
struct Tally {
    exact: usize,
    exact_unenumerated: usize,
    enumerated: usize,
    nonempty: usize,
}

fn run(seed: u64, cases: usize, test: bool) -> Tally {
    let mut rng = Rng::new(seed);
    let mut tally = Tally::default();
    for _ in 0..cases {
        let (term, demand) = if test {
            (bool_term(&mut rng, 3), Demand::Bool(rng.below(2) == 0))
        } else {
            (int_term(&mut rng, 3), int_demand(&mut rng))
        };
        let ds = domains(&mut rng);
        let p = preimage(&term, &ds, &demand);
        assert!(p.stops.is_empty(), "{term}: {:?}", p.stops);
        for (k, v) in &p.domains {
            assert!(v.is_subset(&ds[k]), "{term}: {k} {v} is outside its domain");
        }
        if check(&term, &ds, &demand, &p, WINDOW) > 0 {
            tally.nonempty += 1;
        }
        tally.exact += p.exact as usize;
        tally.exact_unenumerated += (p.exact && !p.enumerated) as usize;
        tally.enumerated += p.enumerated as usize;
    }
    tally
}

#[test]
fn integer_preimages_are_sound_and_exact_where_claimed() {
    let t = run(25, 250, false);
    assert!(
        t.exact_unenumerated >= 60 && t.enumerated >= 5 && t.nonempty >= 100,
        "{t:?}"
    );
}

#[test]
fn test_preimages_are_sound_and_exact_where_claimed() {
    let t = run(2025, 250, true);
    // The catalog makes most tests exact before a listed box is enumerated.
    assert!(
        t.exact_unenumerated >= 40 && t.enumerated >= 2 && t.nonempty >= 100,
        "{t:?}"
    );
}

#[test]
fn a_remainder_inverts_to_its_first_and_last_periods_and_one_piece_between() {
    // Against every point of the domain: the preimage holds each point whose remainder is
    // demanded, is exact when the domain meets at most two periods, and otherwise, unless a
    // later stage made it exact, has at most `2p + 1` pieces for `p` pieces of remainders.
    let mut rng = Rng::new(1585);
    let (mut exact, mut necessary) = (0, 0);
    for _ in 0..1500 {
        let c = loop {
            let c = rng.int(-9, 9);
            if c != 0 {
                break c;
            }
        };
        let m = c.abs();
        let z = IntervalSet::from_pieces(
            (0..rng.int(1, 3))
                .map(|_| {
                    let lo = rng.int(-2, m + 1);
                    (End::Fin(lo), End::Fin(lo + rng.int(0, 2)))
                })
                .collect(),
        );
        let lo = rng.int(-200, 200);
        let span = if rng.below(2) == 0 { 400 } else { m };
        let hi = lo + rng.int(0, span);
        let body = prim(Prim::Mod, vec![Term::Var("i".into()), lit(c)]);
        let ds: Domains = [(
            Arc::<str>::from("i"),
            IntervalSet::range(End::Fin(lo), End::Fin(hi)),
        )]
        .into_iter()
        .collect();
        let demand = Demand::Ints(z.clone());
        let p = preimage(&body, &ds, &demand);
        check(&body, &ds, &demand, &p, (lo - 5, hi + 5));
        if p.enumerated {
            continue;
        }
        let rem = z.meet(&IntervalSet::range(End::Fin(0), End::Fin(m - 1)));
        let pieces = p.domains["i"].pieces().len();
        assert!(
            p.exact || pieces <= 2 * rem.pieces().len() + 1,
            "{c} {z} over {lo}..={hi}: {pieces}"
        );
        if hi.div_euclid(m) <= lo.div_euclid(m) + 1 {
            assert!(p.exact, "{c} {z} over {lo}..={hi}");
            exact += 1;
        } else {
            necessary += 1;
        }
    }
    assert!(
        exact > 300 && necessary > 150,
        "{exact} exact, {necessary} necessary"
    );
}

/// Counts, over the cases run under `@exact`, of results the search found and of results with
/// a point meeting the demand.
#[derive(Default, Debug)]
struct ExactTally {
    searched: usize,
    nonempty: usize,
    several: usize,
}

/// Under `@exact`, over random bounded boxes within the window, `x` in a random class one case
/// in three: where the result is enumerated or exact, each input's set, over the members of its
/// class, is the projection of the points that meet the demand, found by running every point;
/// and the result is exact just when every point of its box in the classes meets the demand.
fn run_exact(seed: u64, cases: usize, test: bool) -> ExactTally {
    let mut rng = Rng::new(seed);
    let mut tally = ExactTally::default();
    let names: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    for _ in 0..cases {
        let (term, demand) = if test {
            (bool_term(&mut rng, 3), Demand::Bool(rng.below(2) == 0))
        } else {
            (int_term(&mut rng, 3), int_demand(&mut rng))
        };
        let mut bounded = || {
            let lo = rng.int(-15, 10);
            IntervalSet::of(lo, (lo + rng.int(0, 20)).min(15))
        };
        let ds: Domains = [(names[0].clone(), bounded()), (names[1].clone(), bounded())].into();
        let mut classes = Classes::new();
        if rng.below(3) == 0 {
            let m = rng.int(2, 4);
            classes.insert("x".into(), Congruence::new(m as u64, rng.int(0, m - 1)));
        }
        let member = |k: &Arc<str>, v: i64| classes.get(k).is_none_or(|c| c.contains(v));
        let p = exact_preimage(&term, &ds, &classes, &demand);
        for (k, v) in &p.domains {
            assert!(v.is_subset(&ds[k]), "{term}: {k} {v} is outside its domain");
        }
        let all = points(&ds, &names, WINDOW);
        let inside = |pt: &[i64]| names.iter().zip(pt).all(|(n, &v)| member(n, v));
        let met: Vec<&Vec<i64>> = all
            .iter()
            .filter(|pt| inside(pt) && meets(&term, &names, pt, &demand))
            .collect();
        for pt in &met {
            for (n, &v) in names.iter().zip(pt.iter()) {
                assert!(
                    p.domains[n].contains(v),
                    "{term}: {pt:?} meets {demand:?}, outside {p:?}"
                );
            }
        }
        if !(p.exact || p.enumerated) {
            continue;
        }
        tally.searched += 1;
        tally.nonempty += !met.is_empty() as usize;
        for (j, n) in names.iter().enumerate() {
            for v in WINDOW.0..=WINDOW.1 {
                let shown = p.domains[n].contains(v) && member(n, v);
                let projected = met.iter().any(|pt| pt[j] == v);
                assert_eq!(
                    shown, projected,
                    "{term} {demand:?} over {ds:?} {classes:?}: {n} = {v}, {p:?}"
                );
            }
        }
        let in_box: Vec<&Vec<i64>> = all
            .iter()
            .filter(|pt| {
                inside(pt)
                    && names
                        .iter()
                        .zip(pt.iter())
                        .all(|(n, &v)| p.domains[n].contains(v))
            })
            .collect();
        tally.several += (p
            .domains
            .values()
            .filter(|s| s.bounds().is_some_and(|(a, b)| a != b))
            .count()
            > 1) as usize;
        let every = in_box.iter().all(|pt| meets(&term, &names, pt, &demand));
        assert_eq!(p.exact, every, "{term} {demand:?} over {ds:?}: exact {p:?}");
    }
    tally
}

#[test]
fn exact_integer_preimages_are_the_projection_of_the_points_that_meet_the_demand() {
    let t = run_exact(7, 250, false);
    assert!(
        t.searched >= 200 && t.nonempty >= 100 && t.several >= 20,
        "{t:?}"
    );
}

#[test]
fn exact_test_preimages_are_the_projection_of_the_points_that_meet_the_demand() {
    let t = run_exact(77, 250, true);
    assert!(
        t.searched >= 200 && t.nonempty >= 100 && t.several >= 20,
        "{t:?}"
    );
}
