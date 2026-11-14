//! The benchmarks of `table_life.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `table_life.rs`.

use super::*;

#[test]
fn a_run_of_checks_on_recursive_groups_scales_by_its_length() {
    // A check's cost does not grow with the recursive groups checked before it.
    // TEST-bench-move-l0123 (author P169): n was 64, now 1,536; 1x measured 336 ms (ns=335774042)
    // at load 26.77 on 2026-11-14.
    let next = AtomicU64::new(1 << 43);
    scaling::check_order(
        "a run of checks on recursive groups, by checks",
        1536,
        1,
        |m| {
            for _ in 0..m {
                rec_unit(next.fetch_add(64, Relaxed));
            }
        },
    );
}

#[test]
fn a_run_of_independent_checks_scales_by_its_length() {
    // A check's cost does not grow with the checks run before it: the tables it searches hold
    // only the nodes alive.
    // TEST-bench-move-l0123 (author P169): n was 64, now 384; 1x measured 351 ms (ns=351162222) at
    // load 26.77 on 2026-11-14.
    let next = AtomicU64::new(1 << 41);
    scaling::check_order("a run of independent checks, by checks", 384, 1, |m| {
        for _ in 0..m {
            unit(next.fetch_add(64, Relaxed));
        }
    });
}
