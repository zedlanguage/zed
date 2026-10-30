//! Soundness on random terms: every point that meets the demand is in the preimage, and where
//! the preimage is marked exact, every point in it meets the demand. The terms mix the scalar
//! operators, including divisions that can fail, with tests, branches and `min` and `max`,
//! over random domains: finite ones the enumeration may take, and wide or unbounded ones it
//! cannot, so that the catalog's own exactness is checked too.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Demand, Domains, preimage};

use super::check;

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

fn domains(rng: &mut Rng) -> Domains {
    [("x", domain(rng)), ("y", domain(rng))]
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
    assert!(
        t.exact_unenumerated >= 40 && t.enumerated >= 5 && t.nonempty >= 100,
        "{t:?}"
    );
}
