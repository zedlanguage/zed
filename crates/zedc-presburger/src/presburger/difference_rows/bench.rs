//! The benchmarks of `difference_rows`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. Their small instance is `solve_never_refuses_rows_of_two_unit_terms`, 1000
//! systems.

use super::*;

/// DISJ-diff-fast checked its premise on 120,000 random systems; the test committed with it
/// drew 6000, cut to 1000 by TEST-bench-move-crates (TESTS-C2-chain-old-products, test audit
/// 2026-11-08 row 17). The 120,000 are drawn here in twelve pieces of `PIECE`, each from a
/// seed of its own, so that each piece stays well under 20 s.
const PIECE: usize = 10_000;

fn piece(k: usize) {
    let start = std::time::Instant::now();
    never_refuses(
        &format!("solve never refuses rows of two unit terms, piece {k}"),
        PIECE,
    );
    eprintln!(
        "{PIECE} systems of two unit terms, piece {k}, in {:.2?}",
        start.elapsed()
    );
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_0() {
    piece(0);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_1() {
    piece(1);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_2() {
    piece(2);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_3() {
    piece(3);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_4() {
    piece(4);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_5() {
    piece(5);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_6() {
    piece(6);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_7() {
    piece(7);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_8() {
    piece(8);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_9() {
    piece(9);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_10() {
    piece(10);
}

#[test]
fn solve_never_refuses_rows_of_two_unit_terms_11() {
    piece(11);
}
