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

// The two long runs of `table_life.rs`, moved here as they stood by TEST-bench-move-l0123
// (author P178: a long run is a benchmark). Their small instances in `table_life.rs` are
// `independent_checks_release_their_nodes` and
// `checks_on_recursive_groups_release_their_instances`, at n = 4.

/// TEST-bench-move-l0123 (author P169): was n = 256 (256 + 256 + 2,048 checks, 2.5 s under
/// load); now n = 32 (32 + 32 + 256 checks). The 8n run fails when it leaves more than 4,096
/// bytes over the n run, that is over 224 more checks, so it still catches a leak of 19 bytes a
/// check, less than one table slot for each node a check makes. Measured on the code of
/// 2026-11-14, 12 runs each on a fresh thread: with no leak the 8n run leaves between -3,936 and
/// +3,936 bytes over the n run at every n from 32 to 256 alike (table capacity), so the smaller
/// n is no closer to the limit; a check that leaves one type node more leaves 299,264 bytes.
#[test]
fn a_long_run_of_independent_checks_holds_bounded_memory() {
    independent_checks_hold_bounded_memory(32);
}

/// TEST-bench-move-l0123 (author P169): was n = 256 (256 + 256 + 2,048 checks, 0.76 s under
/// load); now n = 64 (64 + 64 + 512 checks). The 8n run fails when it leaves more than 4,096
/// bytes over the n run, that is over 448 more checks, so it still catches a leak of 10 bytes a
/// check, far less than the group, members and unfoldings a check whose cycle is not broken
/// leaves. Measured on the code of 2026-11-14, 12 runs each on a fresh thread at n = 32 to 128:
/// with no leak the 8n run leaves exactly 0 bytes over the n run.
#[test]
fn a_long_run_of_checks_on_recursive_groups_holds_bounded_memory() {
    recursive_checks_hold_bounded_memory(64);
}
