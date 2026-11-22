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

/// Before PATH-reads-scale the work grew more than 10.5 times at 8 times the names: 12.2 times
/// in instructions from 32, 16.1 from 64 and 22.9 from 128 (TEST-bench-move-l0139; 12.9 from
/// 64 on 7b58d316e). The cause, found in a callgrind profile at 64 and 256 names: each
/// read of a `w_i` in the innermost scope binds the names it reads there, and each fresh
/// binding rebased the scope's caches by their diff with the names (`Scope::seen_fresh`,
/// zedc-preimage `product.rs`), which the chain's admissions onto paths had moved at every
/// member, `Theta(n)` a binding. Now the binding sets its own entry in each cache, `O(log n)`:
/// 8.10 times from 128 (load 159), 8.15 from 384 (load 50).
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
/// was 16, 0.03 s); [`N_READS`] so it runs about 1 s (PATH-reads-scale; was 16, 0.03 s;
/// 0.60 s at 384 under load 50).
const N_CHECK: usize = 128;
const N_READS: usize = 384;
