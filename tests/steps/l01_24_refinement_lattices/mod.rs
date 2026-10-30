//! Step L1.24: the refinement lattices.
//!
//! The store's per-cell domains (DESIGN.md sec:domains): integer intervals with symbolic
//! affine bounds, congruences, finite sets, float classes and lengths, each held in a cell with
//! the premises it rests on. Each domain is checked against its meaning as a set: `bounds` and
//! `float` compare every operation with the members it should have, `loops` solves the
//! equations of ordinary loops with the M0.5 strategy and compares the solution with the
//! values a run takes, and `cell` follows the premises through meets, joins and widenings.

mod bounds;
mod cell;
mod float;
mod loops;
mod scaling;

use zed_tests::instances::Rng;
use zedc::store::affine::{Affine, Bound, Bounds, Sym};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::Lattice;

/// The symbols the tests use: a count and a second length.
const SYMS: [&str; 2] = ["n", "m"];

/// The integers the oracle tries.
const WINDOW: std::ops::RangeInclusive<i64> = -24..=24;

/// Symbol values the oracle tries: each pair in a small grid.
fn envs() -> Vec<[i64; 2]> {
    let vals = [-7, -2, -1, 0, 1, 3, 8];
    vals.iter()
        .flat_map(|&n| vals.iter().map(move |&m| [n, m]))
        .collect()
}

/// The function giving each symbol its value in `env`.
fn at(env: [i64; 2]) -> impl Fn(&Sym) -> i64 {
    move |s: &Sym| env[SYMS.iter().position(|x| *x == s.0).expect("a test symbol")]
}

/// The members of `b` in the window at `env`.
fn members(b: &Bounds, env: [i64; 2]) -> Vec<i64> {
    WINDOW.filter(|&x| b.contains(x, &at(env))).collect()
}

/// `k1 · n + k2 · m + c`.
fn affine(k: [i64; 2], c: i64) -> Affine {
    let mut a = Affine::constant(c);
    for (s, k) in SYMS.iter().zip(k) {
        if k != 0 {
            a.terms.insert(Sym(s.to_string()), k);
        }
    }
    a
}

/// A random element: an interval union of up to two pieces, and up to two symbolic bounds on
/// each side, over `n`, `m`, `-n`, `2 * n` or `n - m`, some with a floor.
fn random_bounds(rng: &mut Rng) -> Bounds {
    if rng.below(12) == 0 {
        return Bounds::bottom();
    }
    let ints = match rng.below(4) {
        0 => IntervalSet::top(),
        1 => IntervalSet::range(End::Fin(rng.int(-10, 4)), End::PosInf),
        2 => IntervalSet::range(End::NegInf, End::Fin(rng.int(-4, 10))),
        _ => {
            let lo = rng.int(-12, 6);
            let mid = lo + rng.int(0, 6);
            IntervalSet::from_pieces(vec![
                (End::Fin(lo), End::Fin(mid)),
                (
                    End::Fin(mid + rng.int(2, 4)),
                    End::Fin(mid + rng.int(4, 12)),
                ),
            ])
        }
    };
    let terms = [[1, 0], [0, 1], [-1, 0], [2, 0], [1, -1]];
    // A bound has a floor one time in three, as a join with a number gives.
    let side = |rng: &mut Rng, none: End| {
        (0..rng.below(3))
            .map(|_| Bound {
                affine: affine(rng.pick(&terms), rng.int(-3, 3)),
                floor: match rng.below(3) {
                    0 => End::Fin(rng.int(-6, 6)),
                    _ => none,
                },
            })
            .collect::<Vec<_>>()
    };
    let (lo, hi) = (side(rng, End::PosInf), side(rng, End::NegInf));
    Bounds::from_bounds(ints, lo, hi)
}
