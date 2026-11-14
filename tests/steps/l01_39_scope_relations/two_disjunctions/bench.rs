//! Benchmarks of `two_disjunctions`: each times the work at a size and at 8 times it, run
//! apart from the correctness tests (`tools/run_tests.sh --bench`). The value each family
//! settles is checked at a small size by `dead_sides_settle_the_star` and
//! `live_sides_settle_the_star`.

use super::*;

/// The narrowing by a disjunction of `k` sides, all dead but one, keeps the relation of the
/// live side in O(k log k): the sides' liveness comes from the cases, and one more relation
/// is taken, of the live side. (For many live sides, [`a_disjunction_of_live_sides_scales`].)
#[test]
fn a_disjunction_with_dead_sides_scales() {
    let p = Premises::new();
    for lazy in [false, true] {
        let built = scaling::inputs(2_048, |k| (star(lazy, 4096), dead_sides(k, 4096)));
        let what = format!("a disjunction of k sides, all dead but one, lazy {lazy}");
        scaling::check_order(&what, 2_048, 1, |k| {
            let (s, t) = &built[&k];
            s.assume(t, true, &p);
        });
    }
}

/// The narrowing by a disjunction of `k` live sides over the two hubs is O(k log k): each
/// case is reduced once and the joins of the cases are not reduced (`join_cases` in
/// zedc-preimage, NARROW-many-relational-sides). Before, each join that was joined again was
/// reduced, projecting each of its sides again at each of the `log k` levels: 14.3 times
/// the bytes from 32 to 256 sides, above the limit of 14.1; at 192 and 1,536 (since
/// TEST-bench-move-l0139) each side is projected at more levels, so the old method fails by
/// more (inferred, not rerun).
#[test]
fn a_disjunction_of_live_sides_scales() {
    let p = Premises::new();
    for lazy in [false, true] {
        let built = scaling::inputs(192, |k| (star(lazy, 4096), live_sides(k)));
        let what = format!("a disjunction of k live sides, lazy {lazy}");
        scaling::check_order(&what, 192, 1, |k| {
            let (s, t) = &built[&k];
            s.assume(t, true, &p);
        });
    }
}
