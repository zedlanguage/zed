//! Tests of [`Classed`] with the plain-set shortcut of [`Classed::new`] taken and not taken
//! ([`plain_shortcut::both`], VERIFY-classed-wider-class-callers).

use super::{Classed, plain_shortcut};
use crate::interval::{End, IntervalSet, Num};
use crate::landmarks::Landmarks;
use crate::lattice::{Congruence, Lattice};
use crate::seed::Rng;

/// Raw pieces with ends in `-w..=w`: points on a stride of 2 to 5 (so that some sets have a
/// class wider than every integer), short ranges, and now and then an infinite end, unless
/// `finite`.
fn raw_pieces(rng: &mut Rng, w: i64, finite: bool) -> Vec<(End, End)> {
    let n = rng.below(7);
    let mut raw = Vec::new();
    if rng.coin() {
        let (s, a) = (rng.int(2, 5), rng.int(-w, w));
        for i in 0..n as i64 {
            let v = a + s * i;
            raw.push((End::of(v), End::of(v)));
        }
    } else {
        for _ in 0..n {
            let lo = rng.int(-w, w);
            raw.push((End::of(lo), End::of(lo + rng.int(0, 3))));
        }
    }
    if !finite && rng.below(6) == 0 {
        raw.push((End::NegInf, End::of(rng.int(-w, w))));
    }
    if !finite && rng.below(6) == 0 {
        raw.push((End::of(rng.int(-w, w)), End::PosInf));
    }
    raw
}

/// A random set built by one of `IntervalSet`'s builders, so that the shortcut sees trees made
/// by every builder, not only by `from_pieces`: a join, a meet, a difference, a cap, a
/// negation, a class's members, a shift by `lift1`, a hull or a widening.
fn random_set(rng: &mut Rng, finite: bool) -> IntervalSet {
    let w = 30;
    let a = IntervalSet::from_pieces(raw_pieces(rng, w, finite));
    let b = IntervalSet::from_pieces(raw_pieces(rng, w, finite));
    match rng.below(10) {
        0 => a,
        1 => a.join(&b),
        2 => a.meet(&b),
        3 => a.minus(&b),
        4 => a.cap(1 + rng.below(3)),
        5 => a.neg(),
        6 => a.in_class(&Num::from(rng.int(2, 4)), &Num::from(rng.int(0, 3))),
        7 => {
            let k = rng.int(-5, 5);
            a.lift1(|(lo, hi)| vec![(shift(lo, k), shift(hi, k))])
        }
        8 if finite => a.join(&b).hull(),
        8 => a.hull(),
        _ if finite => a.join(&b),
        _ => a.widen(&a.join(&b), &Landmarks::none()),
    }
}

fn shift(e: &End, k: i64) -> End {
    match e {
        End::Fin(v) => End::Fin(v + &Num::from(k)),
        e => e.clone(),
    }
}

/// A random class: every integer most often, else a modulus of 2 to 4 or one value (modulus
/// 0); with every integer the ranges may be infinite, else they are finite.
fn random_classed(rng: &mut Rng) -> Classed {
    match rng.below(4) {
        0 | 1 => Classed::new(random_set(rng, false), Congruence::top()),
        2 => Classed::new(
            random_set(rng, true),
            Congruence::new(rng.int(2, 4), rng.int(0, 3)),
        ),
        _ => Classed::new(random_set(rng, true), Congruence::new(0, rng.int(-30, 30))),
    }
}

/// Everything a reader can see of a `Classed`: the value, how it prints, and how it counts.
fn seen(c: &Classed) -> (Classed, String, String, String, u64) {
    (
        c.clone(),
        format!("{c}"),
        format!("{c:?}"),
        c.type_text(Some("x")),
        c.count(),
    )
}

/// Every operation of `Classed` gives the same answer, printed and compared, with the shortcut
/// of `Classed::new` taken and not taken, on 2 000 random cases of each (sets built by every
/// `IntervalSet` builder, classes of every kind). Each case's first set is plain with a first
/// piece of two values or more, so that it takes the shortcut on every draw, and the count of
/// cases whose first run took it is asserted to be every case. Negative control (run once on
/// the VM, not kept): the shortcut made to return the set's hull fails the equality.
#[test]
fn every_operation_answers_the_same_with_and_without_the_shortcut() {
    let (mut rng, seed) =
        Rng::fresh("every_operation_answers_the_same_with_and_without_the_shortcut");
    let cases = 2000;
    let mut took = 0;
    for case in 0..cases {
        // A first piece of two values or more rules a wider class out at once.
        let lo = rng.int(-30, 30);
        let mut raw = raw_pieces(&mut rng, 30, false);
        raw.push((End::of(lo), End::of(lo + 1)));
        let wide = IntervalSet::from_pieces(raw);
        let (a_set, b_set, b, c, d) = (
            random_set(&mut rng, false),
            random_set(&mut rng, false),
            random_classed(&mut rng),
            random_classed(&mut rng),
            random_classed(&mut rng),
        );
        let (with, without, count) = plain_shortcut::both(|| {
            let w = Classed::plain(wide.clone());
            let a = Classed::plain(a_set.clone());
            let ops = [
                w.clone(),
                a.clone(),
                Classed::plain(b_set.clone()),
                a.join(&b),
                b.join(&c),
                w.join(&d),
                Classed::join_all([a.clone(), b.clone(), c.clone(), d.clone()]),
                Classed::join_all([b.clone(), c.clone()]),
                a.meet(&b),
                b.meet(&c),
                b.meet_ranges(&a_set),
                c.meet_ranges(&wide),
                a.minus(&b),
                b.minus(&c),
                c.minus(&w),
            ];
            let unlisted = [b.minus_unlisted(&c), a.minus_unlisted(&d)];
            let eqs = [b == a_set, a == a_set, c == wide, w == wide];
            (
                ops.iter().map(seen).collect::<Vec<_>>(),
                unlisted.map(|u| u.as_ref().map(seen)),
                eqs,
            )
        });
        assert_eq!(with, without, "seed {seed}, case {case}");
        if count > 0 {
            took += 1;
        }
    }
    assert_eq!(took, cases, "seed {seed}");
}

/// `Classed::new` gives the same value with and without the shortcut for every set built by
/// `IntervalSet`'s builders and every class, 4 000 random cases, of which those that took the
/// shortcut are counted and must be at least one in four: every fourth case is plain with a
/// first piece of two values, which takes it on every draw.
#[test]
fn the_one_form_is_the_same_with_and_without_the_shortcut() {
    let (mut rng, seed) = Rng::fresh("the_one_form_is_the_same_with_and_without_the_shortcut");
    let cases = 4000;
    let mut took = 0;
    for case in 0..cases {
        let (set, class) = match case % 4 {
            0 => {
                let lo = rng.int(-30, 30);
                let mut raw = raw_pieces(&mut rng, 30, false);
                raw.push((End::of(lo), End::of(lo + 1)));
                (IntervalSet::from_pieces(raw), Congruence::top())
            }
            1 => (random_set(&mut rng, false), Congruence::top()),
            2 => (
                random_set(&mut rng, true),
                Congruence::new(rng.int(2, 4), rng.int(0, 3)),
            ),
            _ => (
                random_set(&mut rng, true),
                Congruence::new(0, rng.int(-30, 30)),
            ),
        };
        let (with, without, count) =
            plain_shortcut::both(|| seen(&Classed::new(set.clone(), class.clone())));
        assert_eq!(
            with, without,
            "seed {seed}, case {case}: {set:?} in {class}"
        );
        if count > 0 {
            took += 1;
        }
    }
    assert!(
        took >= cases / 4,
        "seed {seed}: {took} of {cases} took the shortcut"
    );
}
