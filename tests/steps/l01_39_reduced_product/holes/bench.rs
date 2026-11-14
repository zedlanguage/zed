//! Benchmarks of `holes`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn scaling_of_one_cycle_of_holes_is_near_linear() {
    // Three rings of `n` names, each with its bounds and holes in the scope, narrowed by its
    // `n` differences in one conjunction.
    //
    // Laps: `x0` a multiple of 3 and `x{n / 2}` 0 or 1 more than one, within `0..=6n`, and
    // `x0 >= x1 >= … >= x{n - 1} >= x0 - 1`: `x{n / 2}` is `x0` or `x0 - 1`, which only 0 is
    // both, so every name is 0. Narrowing the names in turn takes one lap of the ring for each
    // multiple of 3 it leaves out, `2n` laps of `n` names.
    //
    // Staircase: within `0..=2n`, `x{i}` without `2n - i`, all equal: every name is in `0..=n`,
    // and narrowing in turn takes a lap for each hole.
    //
    // Mixed: the laps within `0..=3n`, and `x{i}` without `3n - i` too.
    //
    // The ends solve each ring once, by composing the maps of its names around it (COMPLEXITY.md
    // S25), so each is near linear in `n`. The scopes and conjunctions are built before the
    // timing.
    let p = Premises::new();
    type Ring = fn(usize) -> (Scope, Term);
    type Family = (&'static str, Ring, fn(usize) -> Vec<String>);
    let families: [Family; 3] = [
        (
            "a ring of n names, two with holes every third value, in 0..=6n",
            |n| laps(n, 6 * n as i64, |_| Vec::new()),
            |n| vec!["[0..=0]".to_string(); n],
        ),
        (
            "a staircase of n names on one cycle, each with one hole, in 0..=2n",
            |n| ring(n, 2 * n as i64, 0, |i| vec![2 * n as i64 - i as i64]),
            |n| vec![format!("[0..={n}]"); n],
        ),
        (
            "a ring of n names, two with holes every third value and each with one hole, in 0..=3n",
            |n| laps(n, 3 * n as i64, |i| vec![3 * n as i64 - i as i64]),
            |n| vec!["[0..=0]".to_string(); n],
        ),
    ];
    for (what, family, expected) in families {
        for n in [4, 9, 16] {
            let (s, d) = family(n);
            assert_eq!(
                printed(&s.assume(&d, true, &p), n),
                expected(n),
                "{what}, n = {n}"
            );
        }
        let built = scaling::inputs(64, family);
        scaling::check_order(what, 64, 1, |n| {
            let (s, d) = &built[&n];
            assert!(!s.assume(d, true, &p).bottom);
        });
    }
}
