//! The large fixed-seed suites of `oracle.rs` (TEST-corr-slow-l0138), run by
//! `tools/run_tests.sh --bench`: the counts measured on them record how much the solver decides.
//! Each correctness test of the same family in `oracle.rs` runs a few hundred systems.

use crate::oracle::*;

#[test]
fn the_12000_rows_of_three_terms_of_seed_0x383b_tight_at_a_corner_match_enumeration() {
    // `oracle::rows_of_three_terms_tight_at_a_corner_match_enumeration` as first written, 7.2 s
    // (2026-11-14, load 25): 12,000 systems; `run` fails at the first wrong answer.
    let t = run(0x38_3b, 12_000, 4, 3, |rng| corner_rows(rng, 4, 3));
    // The counts measured with design R and the five points of its box stage (XT3). Without
    // the box test 5,074 are refused (control run once, STATUS.md, L1.38); the box shows most
    // of the empty ones empty. With only the point nearest zero the counts were (2550, 9282,
    // 168): the corners and midpoints find 36 more points, (2586, 9282, 132). The `hull3`
    // stage (XT3 B4) decided 25 more with a point and showed 24 more empty. The row test of the
    // box stage (Q1-ROWBOX) shows 14 more empty. Without the `hull3` stage it shows 23 of the
    // 64 systems with no rational point empty that design R and the five points refused
    // (2586, 9305, 109, as cross-review XR3 counted); `hull3` already decided 9 of those 23.
    // `live3` decides 20 more with a point and shows 20 more empty: (2631, 9340, 29); without
    // the row test it showed 25 more empty, 5 of them among the 14 the row test shows. Since
    // the `hull3` stage was removed (HULL3-subsumed) `live3` decides its systems too, and the
    // counts are unchanged. Exact eliminations counted by the rows they write
    // (`System::shrink`, Q1-LOCAL) decide 3 more with a point and show 2 more empty: (2634,
    // 9342, 24).
    assert_eq!(
        (t.sat, t.unsat, t.growth, t.shadows),
        (2634, 9342, 24, 0),
        "{t:?}"
    );
    eprintln!("three terms: {t:?}");
}

#[test]
fn small_coefficients_over_four_variables_are_refused_839_times_in_3000() {
    // The refusals, measured with the row test of the box stage (Q1-ROWBOX) and `live3`: 896;
    // 839 since Q1-LOCAL, whose exact eliminations counted by the rows they write
    // (`System::shrink`) decide 57 more.
    assert_eq!(refusals_at(0x38_40, 3000, 4, 4, small_coefficients), 839);
}

#[test]
fn rows_of_three_terms_over_four_variables_are_refused_13_times_in_4000() {
    // 4000 systems, not 3000: since the row test of the box stage (Q1-ROWBOX), 3000 of them
    // gave 17 refusals and 4000 gave 25. `live3` decides the parts left with three variables,
    // which left 13 of 3000 refused without the row test (more than 20 before it). With both,
    // 15 of the 4000 are refused, and each of them was compared under every naming and order.
    // 14 since NAME-ties, whose eliminations go by color a batch at a time, which decides one more.
    // 13 since Q1-LOCAL, whose exact eliminations counted by the rows they write
    // (`System::shrink`) decide one more.
    assert_eq!(
        refusals_at(0x38_41, 4000, 4, 3, |rng| corner_rows(rng, 4, 3)),
        13
    );
}

#[test]
fn the_3000_rows_over_three_variables_of_seed_0x3842_are_never_refused() {
    // The fixed-seed half of
    // `oracle::rows_over_three_variables_answer_the_same_under_any_names_and_order` as first
    // written (1.7 s with it, 2026-11-14, load 25).
    assert_eq!(refusals_at(0x38_42, 3000, 3, 3, three_variables), 0);
}

#[test]
fn the_3000_large_coefficients_of_seed_0x3843_are_never_refused() {
    // The fixed-seed half of
    // `oracle::large_coefficients_answer_the_same_under_any_names_and_order` as first written
    // (0.7 s with it, 2026-11-14, load 25).
    assert_eq!(refusals_at(0x38_43, 3000, 2, 40, large_coefficients), 0);
}
