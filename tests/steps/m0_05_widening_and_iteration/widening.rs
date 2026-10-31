//! The widening and the narrowing of each lattice: a value between the operands' join or
//! meet and the old value, with every chain finite, within the bound step M0.5 states for it
//! from the first value and the landmarks.

use std::collections::BTreeSet;

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::{Card, Congruence, FiniteSet, Landmarks, Lattice};

use super::iv;

/// A random union of up to 12 intervals with endpoints in `-50..=50`.
fn random_set(rng: &mut Rng) -> IntervalSet {
    let pieces = (0..rng.below(13))
        .map(|_| {
            let lo = rng.int(-50, 50);
            (End::Fin(lo), End::Fin(lo + rng.int(0, 6)))
        })
        .collect();
    IntervalSet::from_pieces(pieces)
}

/// Runs `x ∇ (x ⊔ step())` from the bottom until it is stable, returning the chain.
fn chain<L: Lattice>(mut step: impl FnMut() -> L, marks: &Landmarks, limit: usize) -> Vec<L> {
    let mut out = vec![L::bottom()];
    loop {
        let x = out.last().unwrap().clone();
        let next = x.widen(&x.join(&step()), marks);
        assert!(
            x.join(&next) == next,
            "the widening is not an upper bound: {x:?} ∇ … = {next:?}"
        );
        if next == x {
            // A few more steps confirm the chain is stable, not momentarily unchanged.
            let y = (0..8).fold(next.clone(), |y, _| y.widen(&y.join(&step()), marks));
            if y == x {
                return out;
            }
            out.push(y);
        } else {
            out.push(next);
        }
        assert!(out.len() <= limit, "chain longer than {limit}: {out:?}");
    }
}

/// Runs `x Δ (x ⊓ step())` from `top` until it is stable, checking that each value lies
/// between the meet and the one before; returns the chain.
fn descent<L: Lattice>(
    top: L,
    mut step: impl FnMut() -> L,
    marks: &Landmarks,
    limit: usize,
) -> Vec<L> {
    let mut out = vec![top];
    loop {
        let x = out.last().unwrap().clone();
        let m = x.meet(&step());
        let next = x.narrow(&m, marks);
        assert!(
            m.leq(&next) && next.leq(&x),
            "the narrowing is not between: {x:?} Δ {m:?} = {next:?}"
        );
        if next == x {
            let y = (0..8).fold(next.clone(), |y, _| y.narrow(&y.meet(&step()), marks));
            if y == x {
                return out;
            }
            out.push(y);
        } else {
            out.push(next);
        }
        assert!(out.len() <= limit, "descent longer than {limit}: {out:?}");
    }
}

/// Random landmarks: up to four literals in `-50..=50`.
fn random_marks(rng: &mut Rng) -> Landmarks {
    Landmarks::of((0..rng.below(5)).map(|_| rng.int(-50, 50)), [])
}

/// The finite endpoints of `x`.
fn ends(x: &IntervalSet) -> BTreeSet<i64> {
    x.pieces()
        .iter()
        .flat_map(|&(lo, hi)| [lo, hi])
        .filter_map(|e| match e {
            End::Fin(v) => Some(v),
            _ => None,
        })
        .collect()
}

#[test]
fn interval_widening_chains_stay_on_the_first_ends_and_the_landmarks() {
    // Every element's finite ends lie in K, the first element's and the landmarks, and the
    // chain has at most 2|K| + 2 elements, at any number of pieces.
    let mut rng = Rng::new(0x71de);
    let mut longest = 0;
    for _ in 0..RANDOM_INSTANCES {
        let marks = random_marks(&mut rng);
        let first = random_set(&mut rng).join(&IntervalSet::single(rng.int(-50, 50)));
        let mut fed = Some(first.clone());
        let c = chain(
            || fed.take().unwrap_or_else(|| random_set(&mut rng)),
            &marks,
            usize::MAX,
        );
        let k: BTreeSet<i64> = ends(&first).union(marks.ints()).copied().collect();
        assert!(
            c.len() <= 2 * k.len() + 3,
            "{} elements, |K| = {}",
            c.len(),
            k.len()
        );
        for x in &c[1..] {
            assert!(ends(x).is_subset(&k), "{x} has an end outside {k:?}");
        }
        longest = longest.max(c.len());
    }
    assert!(longest > 3, "the chains are all short");
}

#[test]
fn interval_narrowing_chains_stay_on_the_first_ends_and_the_landmarks() {
    // Each value lies between its meet and the one before; its finite ends are the first
    // value's, landmarks, or a bound that replaced an infinite end, once on each side.
    let mut rng = Rng::new(0x71df);
    for _ in 0..RANDOM_INSTANCES {
        let marks = random_marks(&mut rng);
        let first = random_set(&mut rng).join(&iv(Some(rng.int(-60, 60)), None));
        let c = descent(
            first.clone(),
            || random_set(&mut rng).join(&iv(Some(rng.int(-60, 60)), None)),
            &marks,
            usize::MAX,
        );
        let k: BTreeSet<i64> = ends(&first).union(marks.ints()).copied().collect();
        assert!(
            c.len() <= 2 * k.len() + 5,
            "{} elements, |K| = {}",
            c.len(),
            k.len()
        );
        for x in &c {
            assert!(ends(x).difference(&k).count() <= 2, "{x} against {k:?}");
        }
    }
}

#[test]
fn a_moved_endpoint_goes_to_the_next_landmark_or_infinity() {
    let none = Landmarks::none();
    let x = IntervalSet::of(0, 3).join(&IntervalSet::of(10, 12));
    // The upper bound moved: with no landmark above it, it goes to +inf.
    assert_eq!(
        x.widen(&x.join(&IntervalSet::of(12, 14)), &none),
        IntervalSet::of(0, 3).join(&iv(Some(10), None))
    );
    // With the literal 20 written, it stops at 19, for `< 20`.
    assert_eq!(
        x.widen(&x.join(&IntervalSet::of(12, 14)), &Landmarks::of([20], [])),
        IntervalSet::of(0, 3).join(&IntervalSet::of(10, 19))
    );
    // A new piece inside the gap: its new endpoints move to the old ones and merge it with
    // both neighbors, unless a landmark is nearer.
    assert_eq!(
        x.widen(&x.join(&IntervalSet::single(6)), &none),
        IntervalSet::of(0, 12)
    );
    assert_eq!(
        x.widen(&x.join(&IntervalSet::single(8)), &Landmarks::of([6], [])),
        IntervalSet::of(0, 3).join(&IntervalSet::of(7, 12))
    );
    // The lower bound moved: it goes to -inf.
    assert_eq!(
        x.widen(&x.join(&IntervalSet::single(-1)), &none)
            .to_string(),
        "[..=3, 10..=12]"
    );
    // From the bottom, the widening is the value.
    assert_eq!(IntervalSet::empty().widen(&x, &none), x);
}

#[test]
fn a_narrowing_keeps_old_ends_and_takes_a_bound_for_an_infinite_one() {
    let none = Landmarks::none();
    let x = iv(Some(0), None);
    // An infinite end takes the bound.
    assert_eq!(
        x.narrow(&IntervalSet::of(0, 99), &none),
        IntervalSet::of(0, 99)
    );
    // A finite one moves back to the old end, or to a landmark in between.
    let y = IntervalSet::of(0, 99);
    assert_eq!(y.narrow(&IntervalSet::of(5, 50), &none), y);
    assert_eq!(
        y.narrow(&IntervalSet::of(5, 50), &Landmarks::of([10, 60], [])),
        IntervalSet::of(0, 59)
    );
}

#[test]
fn congruence_chains_end_when_the_modulus_stops_dividing() {
    // A pointer's offsets 4, 12, 16, 10 and 7, seen in turn: the class weakens from 4 to
    // 4 mod 8, 0 mod 4, 0 mod 2 and every integer. Each modulus divides the one before, so
    // every chain is finite.
    let steps = [
        Congruence::single(4),
        Congruence::single(12),
        Congruence::single(16),
        Congruence::single(10),
        Congruence::single(7),
    ];
    let mut x = Congruence::bottom();
    let mut seen = Vec::new();
    for s in steps {
        x = x.widen(&x.join(&s), &Landmarks::none());
        seen.push(x);
    }
    assert_eq!(
        seen,
        [
            Congruence::single(4),
            Congruence::new(8, 4),
            Congruence::new(4, 0),
            Congruence::new(2, 0),
            Congruence::top()
        ]
    );
    let mut rng = Rng::new(0xc0);
    for _ in 0..RANDOM_INSTANCES {
        // The modulus of a 64-bit value has at most 64 prime factors, plus the first value.
        chain(
            || Congruence::single(rng.int(-1000, 1000)),
            &Landmarks::none(),
            66,
        );
    }
}

#[test]
fn a_congruence_narrows_at_most_three_times() {
    // Meets alone could descend 0 mod 2, 0 mod 4, 0 mod 8, ... without end; the narrowing
    // leaves the top once and then moves only to one value or none.
    let none = Landmarks::none();
    let even = Congruence::new(2, 0);
    assert_eq!(Congruence::top().narrow(&even, &none), even);
    assert_eq!(even.narrow(&Congruence::new(4, 0), &none), even);
    assert_eq!(
        even.narrow(&Congruence::single(8), &none),
        Congruence::single(8)
    );
    let mut rng = Rng::new(0xc1);
    for _ in 0..RANDOM_INSTANCES {
        descent(
            Congruence::top(),
            || Congruence::new(1 << rng.below(8), 0),
            &none,
            4,
        );
    }
}

#[test]
fn a_finite_set_widens_to_the_top_at_a_member_the_program_does_not_write() {
    // Tags the program writes, 0 to 200, stay exact however many there are.
    let tags = Landmarks::of((0..=200).step_by(3), []);
    let mut next = (0..=200).step_by(3);
    let c = chain(|| FiniteSet::of(next.next()), &tags, 70);
    assert!(matches!(c.last(), Some(FiniteSet::Set(s)) if s.len() == 67));
    // A computed value the program does not write gives the top.
    let codes = FiniteSet::of([200, 404]);
    let marks = Landmarks::of([200, 404, 500], []);
    assert_eq!(
        codes.widen(&codes.join(&FiniteSet::of([500])), &marks),
        FiniteSet::of([200, 404, 500])
    );
    assert_eq!(
        codes.widen(&codes.join(&FiniteSet::of([1000])), &marks),
        FiniteSet::Top
    );
}

#[test]
fn a_growing_buffer_length_widens_to_unbounded_and_stays_nonnegative() {
    // A buffer that grows: a new upper bound on its length widens to unbounded at once when
    // no landmark is above it.
    let len = Card::range(End::Fin(0), End::Fin(1));
    let none = Landmarks::none();
    let grown = len.widen(&len.join(&Card::range(End::Fin(2), End::Fin(2))), &none);
    assert_eq!(grown, Card::range(End::Fin(0), End::PosInf));
    // A length that shrinks below its old minimum widens to 0, not -inf.
    let shrunk = Card::range(End::Fin(3), End::Fin(5));
    assert_eq!(
        shrunk.widen(&shrunk.join(&Card::range(End::Fin(1), End::Fin(1))), &none),
        Card::range(End::Fin(0), End::Fin(5))
    );
    let mut rng = Rng::new(0xca);
    for _ in 0..RANDOM_INSTANCES {
        chain(
            || {
                let a = rng.int(0, 40);
                Card::range(End::Fin(a), End::Fin(a + rng.int(0, 3)))
            },
            &none,
            4,
        );
    }
}
