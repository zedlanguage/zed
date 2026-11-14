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

/// The rings' size at 1x.
const N: usize = 256;
