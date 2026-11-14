//! Benchmarks of `two_disjunctions`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// The narrowing by a disjunction of `k` sides, all dead but one, keeps the relation of the
/// live side in O(k log k): the sides' liveness comes from the cases, and one more relation
/// is taken, of the live side. (For many live sides, [`a_disjunction_of_live_sides_scales`].)
#[test]
fn a_disjunction_with_dead_sides_scales() {
    let p = Premises::new();
    for lazy in [false, true] {
        let built = scaling::inputs(64, |k| (star(lazy, 4096), dead_sides(k, 4096)));
        let what = format!("a disjunction of k sides, all dead but one, lazy {lazy}");
        scaling::check_order(&what, 64, 1, |k| {
            let (s, t) = &built[&k];
            s.assume(t, true, &p);
        });
    }
    // The live side gives `n + m >= 0`, so `max(n, m) >= 0` and `a >= 2`.
    let s = star(true, 5).assume(&dead_sides(5, 5), true, &p);
    let a: Arc<str> = "a".into();
    assert_eq!(
        s.settled(&a).ints().bounds().and_then(|(l, _)| l.to_i64()),
        Some(2)
    );
}

/// The narrowing by a disjunction of `k` live sides over the two hubs is O(k log k): each
/// case is reduced once and the joins of the cases are not reduced (`join_cases` in
/// zedc-preimage, NARROW-many-relational-sides). Before, each join that was joined again was
/// reduced, projecting each of its sides again at each of the `log k` levels: 14.3 times
/// the bytes from 32 to 256 sides, above the limit of 14.1.
#[test]
fn a_disjunction_of_live_sides_scales() {
    let p = Premises::new();
    for lazy in [false, true] {
        let built = scaling::inputs(32, |k| (star(lazy, 4096), live_sides(k)));
        let what = format!("a disjunction of k live sides, lazy {lazy}");
        scaling::check_order(&what, 32, 1, |k| {
            let (s, t) = &built[&k];
            s.assume(t, true, &p);
        });
    }
    // The sides give `n + m >= -4`, so `max(n, m) >= -2` and `a >= 0`, eager and lazy.
    let a: Arc<str> = "a".into();
    for lazy in [false, true] {
        let s = star(lazy, 5).assume(&live_sides(5), true, &p);
        assert_eq!(
            s.settled(&a).ints().bounds().and_then(|(l, _)| l.to_i64()),
            Some(0),
            "lazy {lazy}"
        );
    }
}
