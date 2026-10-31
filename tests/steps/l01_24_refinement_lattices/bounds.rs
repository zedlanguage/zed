//! Intervals with symbolic affine bounds, against their members at each symbol value.

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::store::affine::{Affine, Bound, Bounds, Side};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::{Landmarks, Lattice};

use super::{WINDOW, affine, at, envs, members, random_bounds};

#[test]
fn meet_is_exact_and_join_and_widening_hold_both_sides() {
    let mut rng = Rng::new(0x124);
    let envs = envs();
    for _ in 0..RANDOM_INSTANCES {
        let (a, b) = (random_bounds(&mut rng), random_bounds(&mut rng));
        let (meet, join) = (a.meet(&b), a.join(&b));
        let widened = a.widen(&join, &Landmarks::none());
        assert_eq!(join, b.join(&a), "join of {a} and {b} is not symmetric");
        for &env in &envs {
            let at = at(env);
            for x in WINDOW {
                let (ia, ib) = (a.contains(x, &at), b.contains(x, &at));
                assert_eq!(
                    meet.contains(x, &at),
                    ia && ib,
                    "{x} at {env:?}: {a} meet {b} is {meet}"
                );
                if ia || ib {
                    assert!(
                        join.contains(x, &at),
                        "{x} at {env:?}: {a} join {b} is {join}"
                    );
                    assert!(
                        widened.contains(x, &at),
                        "{x} at {env:?}: {a} widened by {join} is {widened}"
                    );
                }
            }
        }
    }
}

#[test]
fn the_order_is_sound_and_holds_of_meets_and_joins() {
    let mut rng = Rng::new(0x1240);
    let envs = envs();
    let mut below = 0;
    for _ in 0..RANDOM_INSTANCES {
        let (a, b) = (random_bounds(&mut rng), random_bounds(&mut rng));
        assert!(a.leq(&a), "{a} is not below itself");
        assert!(a.leq(&a.join(&b)), "{a} is not below its join with {b}");
        assert!(
            a.meet(&b).leq(&a),
            "the meet of {a} and {b} is not below {a}"
        );
        if a.leq(&b) {
            below += 1;
            for &env in &envs {
                let (ma, mb) = (members(&a, env), members(&b, env));
                assert!(
                    ma.iter().all(|x| mb.contains(x)),
                    "{a} is taken as below {b}, but not at {env:?}"
                );
            }
        }
    }
    // The bottom and the tops of the random elements make the order hold sometimes.
    assert!(below > 0);
}

#[test]
fn an_offset_moves_every_member() {
    let mut rng = Rng::new(0x1241);
    for _ in 0..RANDOM_INSTANCES {
        let a = random_bounds(&mut rng);
        let c = rng.int(-5, 5);
        let moved = a.offset(c);
        for env in envs() {
            for x in WINDOW {
                assert_eq!(
                    moved.contains(x, &at(env)),
                    a.contains(x - c, &at(env)),
                    "{x} at {env:?}: {a} moved by {c} is {moved}"
                );
            }
        }
    }
}

#[test]
fn widening_chains_are_finite() {
    let mut rng = Rng::new(0x1242);
    let mut longest = 0;
    for _ in 0..RANDOM_INSTANCES {
        let mut x = random_bounds(&mut rng);
        let mut steps = 0;
        for _ in 0..64 {
            let next = x.join(&random_bounds(&mut rng));
            let w = x.widen(&next, &Landmarks::none());
            if w == x {
                continue;
            }
            x = w;
            steps += 1;
        }
        longest = longest.max(steps);
    }
    // Each step either drops a symbolic bound or moves an end of the union to infinity or
    // removes a piece, and an element has at most 9 pieces and a few bounds.
    assert!(longest <= 24, "a widening chain took {longest} steps");
}

#[test]
fn bounds_print_in_the_type_syntax() {
    let n = || Affine::sym("n");
    let zero = || Affine::constant(0);
    let cases = [
        (Bounds::range(Some(zero()), n().plus(-1)), "[0..=n - 1]"),
        (Bounds::range(Some(n()), None), "[n..]"),
        (Bounds::range(None, n().times(2)), "[..=2 * n]"),
        (
            Bounds::range(Some(zero()), Some(affine([1, -1], 1))),
            "[0..=-m + n + 1]",
        ),
        (
            Bounds::range(Some(Affine::sym("m")), Some(n()))
                .meet(&Bounds::ints(IntervalSet::of(0, 9))),
            "[max(0, m)..=min(9, n)]",
        ),
        (
            Bounds::from_bounds(
                IntervalSet::range(End::Fin(0), End::PosInf),
                [],
                [Bound {
                    affine: n(),
                    floor: End::Fin(0),
                }],
            ),
            "[0..=max(0, n)]",
        ),
        (
            Bounds::new(
                IntervalSet::from_pieces(vec![
                    (End::Fin(0), End::Fin(3)),
                    (End::Fin(5), End::PosInf),
                ]),
                [],
                [n()],
            ),
            "[0..=3, 5..] & [..=n]",
        ),
        (Bounds::ints(IntervalSet::of(2, 4)), "[2..=4]"),
    ];
    for (b, want) in cases {
        assert_eq!(b.to_string(), want);
    }
}

#[test]
fn a_bound_crossing_its_opposite_is_empty() {
    // `int[n..=n - 1]` has no member whatever `n` is.
    let n = Affine::sym("n");
    let b = Bounds::range(Some(n.clone()), n.plus(-1));
    assert_eq!(b, Bounds::bottom());
    // `int[n..=m]` is empty only when `n > m`, so it stays.
    let c = Bounds::range(Some(n), Some(Affine::sym("m")));
    assert_ne!(c, Bounds::bottom());
    assert_eq!(c.bounds(Side::Lower).len() + c.bounds(Side::Upper).len(), 2);
}

#[test]
fn a_tighter_bound_with_the_same_terms_replaces_the_looser() {
    let n = Affine::sym("n");
    let b = Bounds::range(None, Some(n.clone())).meet(&Bounds::range(None, n.plus(-2)));
    assert_eq!(b.to_string(), "[..=n - 2]");
    // A bound the union already implies is dropped: `max(5, n)` when every member is at most 3.
    let c = Bounds::from_bounds(
        IntervalSet::of(0, 3),
        [],
        [Bound {
            affine: n,
            floor: End::Fin(5),
        }],
    );
    assert_eq!(c, Bounds::ints(IntervalSet::of(0, 3)));
}
