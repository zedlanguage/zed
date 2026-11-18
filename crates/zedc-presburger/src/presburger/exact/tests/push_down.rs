//! Tests of the bounds of one atom that a conjunction passes down to the blocks under it in
//! `read_once` (PRES-cover-unary-push-down; Gemini, round 3 of XR-cover-hybrid). They sit in a
//! file of their own so that tests appended to tests.rs do not conflict with them.

use super::*;

#[test]
fn repaired_unary_push_down_handles_counterexamples_ce1_to_ce3() {
    // CE1: escape under a boxed conjunction contributes the ancestor box [-5, 5], not Z.
    let ce1 = Formula::and(vec![
        ge(&[("s", 1)], 5),
        ge(&[("s", -1)], 5),
        Formula::or(vec![ge(&[("s", 1)], 0), ge(&[("y", 1)], 0)]),
    ]);
    let (has, sets) = read_once_answers(&ce1).expect("CE1 answered by repaired read_once");
    assert!(has);
    assert_eq!(sets[&a("s")], IntervalSet::of(-5, 5));
    assert_eq!(sets[&a("y")], IntervalSet::top());

    // CE1b: nested Or above a boxed And contributes [-5, 5] U {10}.
    let ce1b = Formula::or(vec![ce1, eq(&[("s", 1)], -10)]);
    let (has, sets) = read_once_answers(&ce1b).expect("CE1b answered by repaired read_once");
    assert!(has);
    assert_eq!(
        sets[&a("s")],
        IntervalSet::from_pieces(vec![(End::of(-5), End::of(5)), (End::of(10), End::of(10))])
    );
    assert_eq!(sets[&a("y")], IntervalSet::top());

    // CE2: individually non-empty nested unary intervals [-5, 2] and [4, 6] meet to empty,
    // killing the inner And even on its `y >= 0` escape branch.
    let inner = Formula::and(vec![
        ge(&[("s", 1)], -4),
        ge(&[("s", -1)], 6),
        Formula::or(vec![ge(&[("s", 1)], 0), ge(&[("y", 1)], 0)]),
    ]);
    let dead_other = Formula::and(vec![eq(&[("z", 1)], -1), eq(&[("z", 1)], -2)]);
    let ce2 = Formula::and(vec![
        ge(&[("s", 1)], 5),
        ge(&[("s", -1)], 2),
        Formula::or(vec![inner, dead_other]),
    ]);
    let (has, sets) = read_once_answers(&ce2).expect("CE2 answered unsat by repaired read_once");
    assert!(!has);
    for n in ["s", "y", "z"] {
        assert!(sets.get(&a(n)).is_none_or(IntervalSet::is_empty), "{n}");
    }

    // CE2b (seed 9080448372955771913 round 109): an outer `Or` arm whose `And` is killed solely
    // by an unsolvable unary equation `2 * y == 1` (`unsat = true` with no wide child block on `y`)
    // must set `ctx = false` on its inner `Or` over `z`, so `z` gets `[-1, 4]` from the live arm,
    // not `[-4, 4]` from the dead arm.
    let live_arm = Formula::and(vec![
        ge(&[("y", 1)], 4),
        ge(&[("y", -1)], 4),
        ge(&[("z", 1)], 4),
        ge(&[("z", -1)], 4),
        ge(&[("z", 2)], 2),
    ]);
    let dead_arm = Formula::and(vec![
        ge(&[("x", 1)], 4),
        ge(&[("x", -1)], 3),
        ge(&[("y", 1)], 4),
        ge(&[("y", -1)], 4),
        ge(&[("y", 2)], -1),
        eq(&[("y", 2)], -1),
        Formula::or(vec![
            Formula::and(vec![
                ge(&[("z", 1)], 4),
                ge(&[("z", -1)], 4),
                ge(&[("z", 3)], -2),
            ]),
            Formula::and(vec![ge(&[("z", 1)], 4), ge(&[("z", -1)], 4)]),
        ]),
    ]);
    let ce2b = Formula::or(vec![live_arm, dead_arm]);
    let (has, sets) = read_once_answers(&ce2b).expect("CE2b answered by repaired read_once");
    assert!(has);
    assert_eq!(sets[&a("z")], IntervalSet::of(-1, 4));

    // CE3: non-unary row `s - 2*w == 0` sharing `s` with `(s == 1 || s == 2)` must still decline.
    let ce3 = Formula::and(vec![
        ge(&[("s", 1)], 5),
        ge(&[("s", -1)], 5),
        eq(&[("s", 1), ("w", -2)], 0),
        Formula::or(vec![eq(&[("s", 1)], -1), eq(&[("s", 1)], -2)]),
    ]);
    assert!(read_once_answers(&ce3).is_none());
}

#[test]
fn outer_boxed_wide_pairs_is_answered_by_read_once_within_budget() {
    let k = 512usize;
    let names: Vec<String> = (0..k).map(|i| format!("z{i}")).collect();
    let arm = |sign: i64| {
        Formula::and(
            names
                .windows(2)
                .map(|w| ge(&[(w[0].as_str(), 1), (w[1].as_str(), sign)], 0))
                .collect(),
        )
    };
    let mut parts: Vec<Formula> = names
        .iter()
        .flat_map(|n| [ge(&[(n.as_str(), 1)], 5), ge(&[(n.as_str(), -1)], 5)])
        .collect();
    parts.push(Formula::or(vec![arm(1), arm(-1)]));
    let f = Formula::and(parts);

    let (has, sets) =
        read_once_answers(&f).expect("outer-boxed wide_pairs answered by repaired read_once");
    assert!(has);
    for n in &names {
        assert_eq!(sets[&a(n)], IntervalSet::of(-5, 5), "{n}");
    }
}
