//! Benchmarks of `disjoint`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// The join of two arms that each narrow `k` groups the other does not, at `k` and `8k`
/// groups, the arms built before the timing: near linear in `k`, for groups the solver
/// decides and groups it does not, and with the reduction that follows a join.
#[test]
fn the_join_of_arms_on_many_disjoint_groups_scales() {
    let n = 128;
    for (what, group) in [("decided", decided as Group), ("refused", refused as Group)] {
        let built: BTreeMap<usize, (Scope, Scope)> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|k| (k, arms(k, group)))
            .collect();
        scaling::check(
            &format!("the join of arms on k disjoint {what} groups"),
            n,
            |k| {
                let (l, r) = &built[&k];
                l.join(r);
            },
        );
        scaling::check(
            &format!("the join of arms on k disjoint {what} groups, reduced"),
            n,
            |k| {
                let (l, r) = &built[&k];
                l.join(r).reduce();
            },
        );
    }
}
