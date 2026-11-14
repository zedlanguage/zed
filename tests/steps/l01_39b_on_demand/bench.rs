//! Benchmarks of step L1.39b: the checks of a program of n functions and of 8n, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`). Each has a small instance among the
//! correctness tests in `mod.rs`: `clean(3)` and `one_rejection(3)` in
//! `the_program_of_n_functions_is_accepted_and_the_one_with_a_bad_condition_is_not`, and
//! `many_parameters(3, 40)` in `functions_of_many_parameters_are_accepted_with_no_derivation`.

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::check::derivation_steps;

use super::{STACK, clean, counted, many_parameters, one_rejection};

#[test]
fn one_rejection_builds_the_same_derivation_among_n_functions_as_among_8n() {
    scaling::on_a_thread(STACK, || {
        let (r, small) = counted(&one_rejection(50));
        let small_out = r.expect_err("rejected");
        let (r, large) = counted(&one_rejection(400));
        let large_out = r.expect_err("rejected");
        assert!(small > 0);
        assert_eq!(small, large);
        // The same rejection, printed the same, but for its line.
        let tail = |s: &str| s.lines().skip(1).filter(|l| !l.contains(':')).count();
        assert_eq!(tail(&small_out), tail(&large_out));
    });
}

#[test]
fn checking_functions_that_ask_for_no_derivation_scales() {
    // Each source is loaded, then parsed and resolved, before the runs are measured; only the
    // check is measured (COMPLEXITY.md F85).
    let n = N_CLEAN;
    let units: HashMap<usize, _> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            let src = clean(k);
            assert_eq!(counted(&src), (Ok(()), 0));
            (k, zed_tests::deep::resolved(&src))
        })
        .collect();
    scaling::check_order("checking n functions with no rejection", n, 1, |k| {
        let (stmts, res) = &units[&k];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(derivation_steps(), 0);
    });
}

#[test]
fn checking_functions_of_many_parameters_scales() {
    // n · 40 and 8n · 40 parameters, each with an origin. A parameter costs the checker about
    // 10,000 instructions, so a step that grows with the origins recorded before it, such as a
    // scan of them all comparing spans, shows here; among `clean`'s functions, at about 1.7
    // million instructions per function, it does not. Only the check is measured: the
    // statements are parsed and resolved before the runs.
    let n = N_PARAMS;
    let units: HashMap<usize, _> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            let stmts = zed_tests::deep::statements(&many_parameters(k, 40));
            let res = zedc::resolve::resolve(&stmts).expect("resolves");
            (k, (stmts, res))
        })
        .collect();
    scaling::check_order("checking n functions of 40 parameters", n, 1, |k| {
        let (stmts, res) = &units[&k];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(derivation_steps(), 0);
    });
}

/// The sizes, set so the check of the 1x case runs about 0.15 s alone: `scaling::check` runs
/// the smaller size 3 times and the larger 2 times, about 19 times the 1x in all, and at 3000
/// and 2000 (0.27 and 0.24 s timed) the pieces took 16 and 11 s alone, and the first timed out
/// at 20 s at load 23.
const N_CLEAN: usize = 1500;
const N_PARAMS: usize = 1000;
