//! The benchmarks of `tie_group_tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run: the families whose classes, times their namings, number 70,000 to 1,152,960,
//! each naming checked through [`System::rekey`] and [`System::symmetries`] (10 to 24 s each at
//! load 51 to 60, FAIL-tie-group-tests-piece-time). Unusual sizes are benchmarks (author P178).
//! The correctness tests keep a small instance of each case they reach: every kind of pair on
//! two and three variables, the graphs and the tournaments on five, and the three disjoint pairs
//! on six that only six variables give.

use super::*;

/// Every system of four variables whose pairs each hold one of the seven kinds.
#[test]
fn pairs_of_seven_kinds_on_four_variables() {
    let seen = check(&Family::new(4, 2, pair_kinds(&[0, 1, 2, 3, 4, 5, 6])));
    eprintln!("{seen:?}");
    assert!(seen.answered > 0 && seen.refused > 0);
}

/// Every system of five variables whose pairs each hold no row, `x[i] >= x[j]` or
/// `x[j] >= x[i]`: the oriented graphs.
#[test]
fn oriented_graphs_on_five_variables() {
    let seen = check(&Family::new(5, 2, pair_kinds(&[0, 1, 2])));
    eprintln!("{seen:?}");
    // The number of oriented graphs on five vertices (OEIS A001174).
    assert_eq!(seen.classes, 582);
    assert!(seen.answered_with_cell > 0);
}

/// Every system of five variables whose pairs each hold no row, `x[i] >= x[j]`, `x[j] >=
/// x[i]` or `x[i] + x[j] >= 1`, in eight pieces (9,608 classes, 1,152,960 namings).
fn arcs_and_sums_on_five_variables(part: usize) {
    let seen = check_part(&Family::new(5, 2, pair_kinds(&[0, 1, 2, 3])), part, 8);
    eprintln!("{seen:?}");
    assert!(seen.answered_with_cell > 0);
}

#[test]
fn arcs_and_sums_on_five_variables_0() {
    arcs_and_sums_on_five_variables(0);
}

#[test]
fn arcs_and_sums_on_five_variables_1() {
    arcs_and_sums_on_five_variables(1);
}

#[test]
fn arcs_and_sums_on_five_variables_2() {
    arcs_and_sums_on_five_variables(2);
}

#[test]
fn arcs_and_sums_on_five_variables_3() {
    arcs_and_sums_on_five_variables(3);
}

#[test]
fn arcs_and_sums_on_five_variables_4() {
    arcs_and_sums_on_five_variables(4);
}

#[test]
fn arcs_and_sums_on_five_variables_5() {
    arcs_and_sums_on_five_variables(5);
}

#[test]
fn arcs_and_sums_on_five_variables_6() {
    arcs_and_sums_on_five_variables(6);
}

#[test]
fn arcs_and_sums_on_five_variables_7() {
    arcs_and_sums_on_five_variables(7);
}

/// Every system of six variables whose pairs each hold no row or `x[i] + x[j] >= 1`: the
/// graphs, among them three disjoint pairs, which fixing two variables does not tell apart. In
/// two pieces, every other class each (FAIL-colab-presburger-bench-piece-time: the whole took
/// 11.7 s on one core at load 22, b30-pres4, 2026-11-28; each piece 3.8 to 4.0 s on one core
/// in the release build).
fn graphs_on_six_variables(part: usize) {
    let seen = check_part(&Family::new(6, 2, pair_kinds(&[0, 3])), part, 2);
    eprintln!("{seen:?}");
    // The number of graphs on six vertices is 156 (OEIS A000088): 78 in each piece.
    assert_eq!(seen.classes, 78);
    assert!(seen.answered_with_cell > 0 && seen.refused_symmetric > 0);
}

#[test]
fn graphs_on_six_variables_0() {
    graphs_on_six_variables(0);
}

#[test]
fn graphs_on_six_variables_1() {
    graphs_on_six_variables(1);
}

/// Every system of six variables whose pairs each hold `x[i] >= x[j]` or the reverse: the
/// tournaments.
#[test]
fn tournaments_on_six_variables() {
    let seen = check(&Family::new(6, 2, pair_kinds(&[1, 2])));
    eprintln!("{seen:?}");
    // The number of tournaments on six vertices (OEIS A000568).
    assert_eq!(seen.classes, 56);
    assert!(seen.answered_with_cell > 0);
}
