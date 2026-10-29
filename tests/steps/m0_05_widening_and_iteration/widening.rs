//! The widening of each lattice: an upper bound of both operands, with every chain of
//! widenings finite, and within the bound step M0.5 states for it.

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::store::interval::{End, IntervalSet, PIECE_LIMIT};
use zedc::store::lattice::{Card, Congruence, FINITE_SET_LIMIT, FiniteSet, Lattice};

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
fn chain<L: Lattice>(mut step: impl FnMut() -> L, limit: usize) -> Vec<L> {
    let mut out = vec![L::bottom()];
    loop {
        let x = out.last().unwrap().clone();
        let next = x.widen(&x.join(&step()));
        assert!(
            x.join(&next) == next,
            "the widening is not an upper bound: {x:?} ∇ … = {next:?}"
        );
        if next == x {
            // A few more steps confirm the chain is stable, not momentarily unchanged.
            let y = (0..8).fold(next.clone(), |y, _| y.widen(&y.join(&step())));
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

#[test]
fn interval_widening_chains_have_at_most_seventeen_elements_above_the_bottom() {
    // Each strict step above the first removes a finite endpoint, and at most 8 pieces have
    // at most 16 finite endpoints.
    let mut rng = Rng::new(0x71de);
    for _ in 0..RANDOM_INSTANCES {
        let c = chain(|| random_set(&mut rng), 2 * PIECE_LIMIT + 2);
        assert!(c[1..].iter().all(|x| x.pieces().len() <= PIECE_LIMIT));
        for w in c[1..].windows(2) {
            assert!(
                w[1].finite_endpoints() < w[0].finite_endpoints(),
                "{} then {}",
                w[0],
                w[1]
            );
        }
    }
}

#[test]
fn a_moved_endpoint_goes_to_infinity_and_a_new_gap_endpoint_closes_the_gap() {
    let x = IntervalSet::of(0, 3).join(&IntervalSet::of(10, 12));
    // The upper bound moved: it goes to +inf.
    assert_eq!(
        x.widen(&x.join(&IntervalSet::of(12, 14))),
        IntervalSet::of(0, 3).join(&iv(Some(10), None))
    );
    // A new piece inside the gap: its new endpoints merge it with both neighbors.
    assert_eq!(
        x.widen(&x.join(&IntervalSet::single(6))),
        IntervalSet::of(0, 12)
    );
    // The lower bound moved: it goes to -inf.
    assert_eq!(
        x.widen(&x.join(&IntervalSet::single(-1))).to_string(),
        "[..=3, 10..=12]"
    );
    // From the bottom, the widening is the value.
    assert_eq!(IntervalSet::empty().widen(&x), x);
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
        x = x.widen(&x.join(&s));
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
        chain(|| Congruence::single(rng.int(-1000, 1000)), 66);
    }
}

#[test]
fn a_finite_set_of_tags_widens_to_the_top_past_sixty_four() {
    let mut rng = Rng::new(0xf5);
    let c = chain(|| FiniteSet::of([rng.int(0, 200)]), FINITE_SET_LIMIT + 3);
    assert_eq!(c.last(), Some(&FiniteSet::Top));
    // A small set of status codes stays exact.
    let codes = FiniteSet::of([200, 404]);
    assert_eq!(
        codes.widen(&codes.join(&FiniteSet::of([500]))),
        FiniteSet::of([200, 404, 500])
    );
}

#[test]
fn a_growing_buffer_length_widens_to_unbounded_and_stays_nonnegative() {
    // A buffer that grows: a new upper bound on its length widens to unbounded at once (the
    // iteration's delay decides when widening starts, not the lattice).
    let len = Card::range(End::Fin(0), End::Fin(1));
    let grown = len.widen(&len.join(&Card::range(End::Fin(2), End::Fin(2))));
    assert_eq!(grown, Card::range(End::Fin(0), End::PosInf));
    // A length that shrinks below its old minimum widens to 0, not -inf.
    let shrunk = Card::range(End::Fin(3), End::Fin(5));
    assert_eq!(
        shrunk.widen(&shrunk.join(&Card::range(End::Fin(1), End::Fin(1)))),
        Card::range(End::Fin(0), End::Fin(5))
    );
    let mut rng = Rng::new(0xca);
    for _ in 0..RANDOM_INSTANCES {
        chain(
            || {
                let a = rng.int(0, 40);
                Card::range(End::Fin(a), End::Fin(a + rng.int(0, 3)))
            },
            4,
        );
    }
}
