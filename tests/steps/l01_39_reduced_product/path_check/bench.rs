//! Benchmarks of `path_check`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn the_checker_on_a_chain_of_difference_tests_is_linear() {
    checked_in_linear_work("chain of n difference tests, zedc check", N_CHECK, chain);
}

#[test]
fn the_checker_on_a_raised_head_is_linear() {
    checked_in_linear_work("n raises of a chain's head, zedc check", N_CHECK, raise);
}

/// At [`N_READS`]: from 32 names up the work grows more than 10.5 times at 8 times the names,
/// 12.2 times in instructions from 32, 16.1 from 64 and 22.9 from 128 (TEST-bench-move-l0139;
/// plan row PATH-reads-scale). A profile at 128 and 1,024 spends its time in insertions into
/// the persistent maps of the names' products and in comparisons of interval sets. Not yet
/// confirmed as the cause: the `O(n)` diff after each refused test on a difference path that
/// the note in `Scope::seen_fresh` (zedc-preimage `product.rs`) accepts, `n` tests here.
#[test]
fn the_checker_reading_names_bound_under_a_chain_is_linear() {
    checked_in_linear_work(
        "n names bound under a chain, one input, zedc check",
        N_READS,
        |n| reads(n, false),
    );
}

/// Checks each program of `make` at `n` and at 8 times it and holds the work to the limit of
/// order n. On main before ST-walk-checker-admit the checker took no test on paths and these
/// grew, from 16 to 128, 23.5 (chain), 25.9 (raise) and 21.1 (one input read) times in
/// instructions; a growth of order n² grows more at a larger size.
fn checked_in_linear_work(what: &str, n: usize, make: fn(usize) -> String) {
    let programs = zed_tests::scaling::inputs(n, make);
    zed_tests::scaling::check(what, n, |m| {
        if let Err(e) = zedc::run::load(programs[&m].as_bytes()) {
            panic!("{what}, n = {m}: rejected: {e}");
        }
    });
}

/// The sizes. [`N_CHECK`] is set so the 1x check runs about 0.13 s (TEST-bench-move-l0139;
/// was 16, 0.03 s); [`N_READS`] stays at 16, 0.03 s.
const N_CHECK: usize = 128;
const N_READS: usize = 16;
