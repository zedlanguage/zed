//! The benchmarks of `table_life.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `table_life.rs`.

use super::*;

#[test]
fn a_run_of_checks_on_recursive_groups_scales_by_its_length() {
    // A check's cost does not grow with the recursive groups checked before it.
    let next = AtomicU64::new(1 << 43);
    scaling::check_order(
        "a run of checks on recursive groups, by checks",
        64,
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
    let next = AtomicU64::new(1 << 41);
    scaling::check_order("a run of independent checks, by checks", 64, 1, |m| {
        for _ in 0..m {
            unit(next.fetch_add(64, Relaxed));
        }
    });
}
