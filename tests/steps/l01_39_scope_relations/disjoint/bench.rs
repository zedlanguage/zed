//! Benchmarks of `disjoint`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// The join of two arms that each narrow `k` groups the other does not, at `k = n` and `8n`
/// groups, the arms built before the timing: near linear in `k`, for groups the solver
/// decides and groups it does not, and with the reduction that follows a join. One check per
/// test: the four in one test took 17 s, near the 20 s piece limit.
///
/// The arms are built by `check_inputs`, only at the sizes this process runs: built at both
/// sizes before the first run, under DynamoRIO, the first phase of each of these benchmarks
/// passed its limit of 20 s (rc 124 at 20.1 s and 20.2 s on l43, b22-tests8 job f2,
/// FAIL-bench-pieces-past-limit-on-main); the arms at 8n are now built in the process that
/// runs 8n, in the phase whose limit is 10.5 times the run at n.
fn join_scales(what: &str, group: Group, reduced: bool, n: usize) {
    let what = format!(
        "the join of arms on k disjoint {what} groups{}",
        if reduced { ", reduced" } else { "" }
    );
    scaling::check_inputs(
        &what,
        n,
        |k| arms(k, group),
        |(l, r)| {
            let mut j = l.join(r);
            if reduced {
                j.reduce();
            }
        },
    );
}

#[test]
fn the_join_of_arms_on_many_disjoint_decided_groups_scales() {
    join_scales("decided", decided, false, 128);
}

#[test]
fn the_join_of_arms_on_many_disjoint_decided_groups_reduced_scales() {
    join_scales("decided", decided, true, 128);
}

#[test]
fn the_join_of_arms_on_many_disjoint_refused_groups_scales() {
    join_scales("refused", refused, false, 128);
}

/// At 64 and 512 groups, not 128 and 1024 as the others: at 128 the piece took 34.3 s alone
/// against its cap of 36 s (b22-misc3, 2026-11-22). Building the arms is most of it, outside
/// the timing (each refused group's `assume` runs the solver to its refusal, about 8 ms a group,
/// so 9.5 s for the 1,152 groups of both sizes at load 69), then the two timed runs (0.57 s and
/// 6.96 s at load 69). At 64 the piece took 24.8 s at load 69, the run at 128 took 59.7 s at load
/// 64; instructions 1,864 M and 12,993 M, ratio 6.97 (7.67 at 128).
#[test]
fn the_join_of_arms_on_many_disjoint_refused_groups_reduced_scales() {
    join_scales("refused", refused, true, 64);
}
