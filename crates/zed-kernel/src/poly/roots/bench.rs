//! The cost of one unit of [`positive_roots`]'s branch and bound against one of
//! [`chain_roots`]'s evaluations at a stretch's end (plan row BENCH-over-nlogn-prediction,
//! item 16), on the families that spend the whole budget [`chain_ends`] and hand over to the
//! chain. Run by `tools/run_tests.sh --bench`; it prints the measurements and checks nothing
//! of their size.
//!
//! Measured 2026-11-20 (load5 about 80), instructions: a unit costs 9.3 to 18.0 of the
//! chain's end evaluations (12.4, 15.1, 16.5 and 9.9 on the cubic at `c = 2^16, 2^64, 2^256,
//! 2^1024`; 14.5, 15.7, 18.0 and 9.3 on the cluster), and the units of the budget 6.4 to 10.2
//! times the chain's whole run. So the claim it was written for, a unit no dearer than one
//! end evaluation, fails by that constant; the proof at [`positive_roots`] now counts the 12
//! passes a unit makes at most.

use std::hint::black_box;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::{chain_cells, chain_ends, chain_roots, derived, eval, positive_roots};

/// The coefficients of the product of `x - r` for each `r` in `rs`, as `positive_roots`
/// takes them: the terms not zero, by exponent.
fn from_roots(rs: &[BigInt]) -> Vec<(u64, BigInt)> {
    let mut c = vec![BigInt::one()];
    for r in rs {
        let mut next = vec![BigInt::zero(); c.len() + 1];
        for (i, a) in c.iter().enumerate() {
            next[i + 1] += a;
            next[i] -= a * r;
        }
        c = next;
    }
    (c.into_iter().enumerate())
        .filter(|(_, a)| !a.is_zero())
        .map(|(i, a)| (i as u64, a))
        .collect()
}

/// The chain's evaluations at the ends of its stretches on `a..=hi`, as [`chain_roots`] and
/// [`chain_cells`] make them: each member, from the last but one up, at both ends of each of
/// its stretches.
fn end_evaluations(
    p: &[(u64, BigInt)],
    a: &BigInt,
    hi: &BigInt,
) -> Vec<(Vec<(u64, BigInt)>, BigInt)> {
    let mut chain = vec![p.to_vec()];
    while chain.last().expect("one member").len() > 1 {
        let next = derived(chain.last().expect("one member"));
        chain.push(next);
    }
    let mut out = Vec::new();
    let mut below: Vec<BigInt> = Vec::new();
    for q in chain.iter().rev().skip(1) {
        let mut u = a.clone();
        for c in &below {
            if &u <= c {
                out.push((q.clone(), u.clone()));
                out.push((q.clone(), c.clone()));
            }
            u = u.max(c + 1);
        }
        if &u <= hi {
            out.push((q.clone(), u));
            out.push((q.clone(), hi.clone()));
        }
        below = chain_cells(q, &below, a, hi);
    }
    out
}

#[test]
fn a_unit_of_the_branch_and_bound_against_an_end_of_the_chain() {
    let mut meter = crate::scaling::Meter::new();
    for k in [16u64, 64, 256, 1024] {
        let c = BigInt::one() << k;
        let c2 = &c * &c;
        let flat = vec![
            (0, -(&c2 * &c + 3 * &c + 1)),
            (1, 3 * (&c2 + 1)),
            (2, -3 * &c),
            (3, BigInt::one()),
        ];
        let cluster = from_roots(&(0..4).map(|i| &c + i).collect::<Vec<_>>());
        for (family, p) in [("flat cubic", flat), ("cluster of four", cluster)] {
            let a = BigInt::from(2);
            let hi = BigInt::one()
                + p.iter()
                    .map(|(_, c)| num_traits::Signed::abs(c))
                    .max()
                    .expect("terms");
            let chained = super::tests::CHAINED.with(|c| c.get());
            let whole = meter.work(|| {
                black_box(positive_roots(&p, a.clone(), None));
            });
            assert_eq!(
                super::tests::CHAINED.with(|c| c.get()),
                chained + 1,
                "{family} at 2^{k} hands over"
            );
            let chain = meter.work(|| {
                black_box(chain_roots(&p, a.clone(), Some(hi.clone())));
            });
            let points = end_evaluations(&p, &a, &hi);
            let ends = meter.work(|| {
                for (q, x) in &points {
                    black_box(eval(q, x));
                }
            });
            let units = chain_ends(p.len());
            let bb = whole.units.saturating_sub(chain.units);
            println!(
                "bench roots-unit-cost {family} c=2^{k} t={} units={units} bb={bb} per_unit={} \
                 ends={} end_work={} per_end={} bb/ends={:.3} bb/chain={:.3}",
                p.len(),
                bb / units,
                points.len(),
                ends.units,
                ends.units / points.len() as u64,
                bb as f64 / ends.units as f64,
                bb as f64 / chain.units as f64,
            );
        }
    }
}
