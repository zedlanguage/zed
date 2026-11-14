//! Benchmarks of `disjoint`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// The join of two arms that each narrow `k` groups the other does not, at `k` and `8k`
/// groups, the arms built before the timing: near linear in `k`, for groups the solver
/// decides and groups it does not, and with the reduction that follows a join. One check per
/// test: the four in one test took 17 s, near the 20 s piece limit.
fn join_scales(what: &str, group: Group, reduced: bool) {
    let n = 128;
    let built: BTreeMap<usize, (Scope, Scope)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|k| (k, arms(k, group)))
        .collect();
    let what = format!(
        "the join of arms on k disjoint {what} groups{}",
        if reduced { ", reduced" } else { "" }
    );
    scaling::check(&what, n, |k| {
        let (l, r) = &built[&k];
        let mut j = l.join(r);
        if reduced {
            j.reduce();
        }
    });
}

#[test]
fn the_join_of_arms_on_many_disjoint_decided_groups_scales() {
    join_scales("decided", decided, false);
}

#[test]
fn the_join_of_arms_on_many_disjoint_decided_groups_reduced_scales() {
    join_scales("decided", decided, true);
}

#[test]
fn the_join_of_arms_on_many_disjoint_refused_groups_scales() {
    join_scales("refused", refused, false);
}

#[test]
fn the_join_of_arms_on_many_disjoint_refused_groups_reduced_scales() {
    join_scales("refused", refused, true);
}
