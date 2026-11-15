//! The benchmarks of `equation_sign.rs`, run by `tools/run_tests.sh --bench`: sweeps of many
//! systems (author P178), each piece of 50, and the scaling of the colors that choose the sign
//! of an equation such as `a - b == 0`.

use crate::equation_sign::{differing, layered, system};
use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, decide};

/// No system numbered `range` of `seed` changes answer with the naming, the writing of its
/// equations or the order of its parts. Before PRES-solve-equation-sign, 38 of the 600
/// layered systems of seeds 1 and 2 did.
fn none_differ(seed: u64, range: std::ops::Range<usize>, layers: bool) {
    let (differ, refused) = if layers {
        differing(seed, range.clone(), layered)
    } else {
        differing(seed, range.clone(), system)
    };
    println!(
        "equation_sign seed {seed} {range:?}: {refused} refused, {} differ",
        differ.len()
    );
    assert_eq!(differ, Vec::new(), "seed {seed}");
}

#[test]
fn layered_seed_1_systems_0_to_49() {
    none_differ(1, 0..50, true);
}

#[test]
fn layered_seed_1_systems_50_to_99() {
    none_differ(1, 50..100, true);
}

#[test]
fn layered_seed_1_systems_100_to_149() {
    none_differ(1, 100..150, true);
}

#[test]
fn layered_seed_1_systems_150_to_199() {
    none_differ(1, 150..200, true);
}

#[test]
fn layered_seed_1_systems_200_to_249() {
    none_differ(1, 200..250, true);
}

#[test]
fn layered_seed_1_systems_250_to_299() {
    none_differ(1, 250..300, true);
}

#[test]
fn layered_seed_2_systems_0_to_49() {
    none_differ(2, 0..50, true);
}

#[test]
fn layered_seed_2_systems_50_to_99() {
    none_differ(2, 50..100, true);
}

#[test]
fn layered_seed_2_systems_100_to_149() {
    none_differ(2, 100..150, true);
}

#[test]
fn layered_seed_2_systems_150_to_199() {
    none_differ(2, 150..200, true);
}

#[test]
fn layered_seed_2_systems_200_to_249() {
    none_differ(2, 200..250, true);
}

#[test]
fn layered_seed_2_systems_250_to_299() {
    none_differ(2, 250..300, true);
}

#[test]
fn plain_seed_1_systems_0_to_49() {
    none_differ(1, 0..50, false);
}

/// A ring of `n` variables in `[0, 5]` joined by `v[i] - v[i + 1] == 0`, each written in turn
/// as `t == 0`, as `-t == 0` and as `t >= 0 && -t >= 0`: every equation is one whose sign only
/// the names could choose, so the colors of all the rows are made.
fn ring_of_equations(n: usize) -> Formula {
    let v = |i: usize| Lin::atom(Atom::Sym(format!("v{i}").into()));
    let mut fs = Vec::new();
    for i in 0..n {
        fs.push(Formula::Con(Con::ge(&v(i), &Lin::constant(0))));
        fs.push(Formula::Con(Con::ge(&Lin::constant(5), &v(i))));
        let t = v(i).minus(&v((i + 1) % n));
        let zero = Lin::constant(0);
        match i % 3 {
            0 => fs.push(Formula::Con(Con::eq(&t, &zero))),
            1 => fs.push(Formula::Con(Con::eq(&t.times(-1), &zero))),
            _ => {
                fs.push(Formula::Con(Con::ge(&t, &zero)));
                fs.push(Formula::Con(Con::ge(&zero, &t)));
            }
        }
    }
    Formula::and(fs)
}

#[test]
fn decide_scales_over_a_ring_of_equations_whose_sign_only_the_names_choose() {
    // One coloring of the 4n rows and a lookup per equation: O(n log n).
    let (small, large) = (
        ring_of_equations(6000),
        ring_of_equations(6000 * scaling::FACTOR),
    );
    assert_eq!((decide(&small), decide(&large)), (Ok(true), Ok(true)));
    scaling::check_order("decide on a ring of equations", 6000, 1, |n| {
        let f = if n == 6000 { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}
