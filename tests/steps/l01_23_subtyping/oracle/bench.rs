//! The benchmarks of `oracle.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169, P178). Each check has a drawn sample among
//! the correctness tests of `oracle.rs`.

use super::*;

/// The types of one piece of the 12,000-type battery ([`fuzz`]; plan row
/// TESTS-T2-types-rest-4-random-vs-recursive). Small instance:
/// `random_types_agree_with_the_oracle`, 200 types.
const FUZZ_PIECE: usize = 1500;

fn fuzz_piece(k: usize) {
    let what = format!("12,000 types, piece {k}");
    zed_tests::scaling::timed(&what, || fuzz(&what, FUZZ_PIECE));
}

#[test]
fn twelve_thousand_types_agree_with_the_oracle_0() {
    fuzz_piece(0);
}

#[test]
fn twelve_thousand_types_agree_with_the_oracle_1() {
    fuzz_piece(1);
}

#[test]
fn twelve_thousand_types_agree_with_the_oracle_2() {
    fuzz_piece(2);
}

#[test]
fn twelve_thousand_types_agree_with_the_oracle_3() {
    fuzz_piece(3);
}

#[test]
fn twelve_thousand_types_agree_with_the_oracle_4() {
    fuzz_piece(4);
}

#[test]
fn twelve_thousand_types_agree_with_the_oracle_5() {
    fuzz_piece(5);
}

#[test]
fn twelve_thousand_types_agree_with_the_oracle_6() {
    fuzz_piece(6);
}

#[test]
fn twelve_thousand_types_agree_with_the_oracle_7() {
    fuzz_piece(7);
}

/// Every system of seeds 1 and 2 the cross-review measured (wt/xv/Q1Q7/REPORT.md, check 4),
/// with the check the correctness test made on all 8000 before TEST-bench-move-l0123;
/// `the_two_routes_agree_on_recursive_systems` asks 1500 of them each run.
#[test]
fn every_recursive_system() {
    let (routes, accepted) = recursive_routes(
        (1..=2).flat_map(|seed| (0..SYSTEMS_PER_SEED as usize).map(move |idx| (seed, idx))),
        "every system",
    );
    assert!(
        routes.same > 3900 && routes.refused < 100,
        "{routes:?} of {accepted}"
    );
}
