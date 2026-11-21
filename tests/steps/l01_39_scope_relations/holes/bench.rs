//! Benchmarks of `holes`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// The rings of [`families`] at `n` and `8n` names: the ends solve each ring once, by
/// composing the maps of its names around it (COMPLEXITY.md S25), so each is near linear in
/// `n`. The scopes and conjunctions are built before the timing. The ends are checked at
/// small sizes by `one_cycle_of_holes_has_exact_ends`.
#[test]
fn scaling_of_one_cycle_of_holes_is_near_linear() {
    let p = Premises::new();
    for (what, family, _) in families() {
        let built = scaling::inputs(N, family);
        scaling::check_order(what, N, 1, |n| {
            let (s, d) = &built[&n];
            assert!(!s.assume(d, true, &p).bottom);
        });
    }
}

/// The ring of item O7 (COMPLEXITY.md S25, row PERF-project-raises-o7): `n` names within
/// `0..=4n`, `x{i}` without `4n - 2i`, and `x0 >= x1 >= … >= x{n - 1} >= x0 - 2n`, a cycle with
/// slack enough that every raise of a gap holds ([`slack_ring`]). Built before the timing.
/// One raise at a time, each moved O(n) names: 472 M and 13,024 M instructions at n = 128 and
/// 1,024, ratio 27.6 (2026-11-21), so this checked order 2. The raises made at once
/// (`Scope::raise_all`, row PERF-project-raises-o7-batch) move each name O(1) times, so the
/// order checked is 1.
#[test]
fn a_ring_with_slack_whose_raises_all_hold_is_near_linear() {
    let p = Premises::new();
    let built = scaling::inputs(SLACK_N, slack_ring);
    scaling::check_order(
        "the ring of item O7, every raise holding",
        SLACK_N,
        1,
        |n| {
            let (s, d) = &built[&n];
            assert!(!s.assume(d, true, &p).bottom);
        },
    );
}

/// The ring of item O7's size at 1x.
const SLACK_N: usize = 128;

/// The rings' size at 1x.
const N: usize = 256;
