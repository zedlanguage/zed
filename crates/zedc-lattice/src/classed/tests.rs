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

/// `Classed::pieces` lists exactly the pieces of `Classed::met`, in order, for strided and
/// plain sets alike: the strided values it lists without building a set are already that
/// set's pieces (proof at `Classed::listed`), 4 000 random cases, half of them with a class
/// other than every integer (FAIL-s22-remainder-corners-under-load).
#[test]
fn the_pieces_are_those_of_the_set_listed() {
    let (mut rng, seed) = Rng::fresh("the_pieces_are_those_of_the_set_listed");
    let mut strided = 0;
    for case in 0..4000 {
        let c = match case % 2 {
            0 => Classed::new(
                random_set(&mut rng, true),
                Congruence::new(rng.int(2, 5), rng.int(0, 4)),
            ),
            _ => Classed::plain(random_set(&mut rng, false)),
        };
        if c.strided().is_some() {
            strided += 1;
        }
        let pieces: Vec<(End, End)> = c.pieces().collect();
        assert_eq!(
            pieces,
            c.met().into_pieces(),
            "seed {seed}, case {case}: {c:?}"
        );
    }
    assert!(
        strided >= 500,
        "seed {seed}: {strided} of 4000 cases strided"
    );
}

/// A random set of one of five kinds, by `kind`: 0 single values on a stride of 2 to 5,
/// sometimes with one value moved off the stride; 1 single values with one wide range among
/// them, first, last or between (the shape of a name whose holes are tested from below); 2
/// ranges of 1 to 10 values, sometimes with an infinite end; 3 empty; 4 a set made by one of
/// `IntervalSet`'s builders ([`random_set`]).
fn wider_class_case(rng: &mut Rng, kind: usize) -> IntervalSet {
    let points = |rng: &mut Rng| -> Vec<(End, End)> {
        let (s, a, n) = (rng.int(2, 5), rng.int(-40, 40), rng.below(12));
        let mut vs: Vec<i64> = (0..n as i64).map(|i| a + s * i).collect();
        if !vs.is_empty() && rng.below(3) == 0 {
            let i = rng.below(vs.len());
            vs[i] += 1;
        }
        vs.into_iter().map(|v| (End::of(v), End::of(v))).collect()
    };
    match kind {
        0 => IntervalSet::from_pieces(points(rng)),
        1 => {
            let mut raw = points(rng);
            let lo = match rng.below(3) {
                0 => -60,
                1 => 60,
                _ => rng.int(-40, 40),
            };
            raw.push((End::of(lo), End::of(lo + rng.int(1, 6))));
            IntervalSet::from_pieces(raw)
        }
        2 => {
            let mut raw: Vec<(End, End)> = (0..rng.below(6))
                .map(|_| {
                    let lo = rng.int(-40, 40);
                    (End::of(lo), End::of(lo + rng.int(1, 9)))
                })
                .collect();
            if rng.below(4) == 0 {
                raw.push((End::NegInf, End::of(rng.int(-60, -41))));
            }
            if rng.below(4) == 0 {
                raw.push((End::of(rng.int(51, 60)), End::PosInf));
            }
            IntervalSet::from_pieces(raw)
        }
        3 => IntervalSet::empty(),
        _ => {
            let finite = rng.coin();
            random_set(rng, finite)
        }
    }
}

/// `Classed::wider_class`, whose check of the count of members skips the walk on a set with a
/// piece of two values or more (FAIL-xst-holes-laps-ratio), gives what the walk alone
/// (`Classed::wider_class_walk`, the version before the check) gives, on 5 000 random sets of
/// each kind of [`wider_class_case`], and again on each set with one value taken out, which
/// changes one path of a tree whose counts were already asked, as a test's narrowing does.
/// Both answers occur in the cases compared. Negative control, kept: a check that takes a set
/// of single values to be in a wider class without the walk's gcd (wrong for `{0, 1, 3}`)
/// must disagree with the walk on some case.
#[test]
fn the_members_check_gives_the_walks_answer() {
    let (mut rng, seed) = Rng::fresh("the_members_check_gives_the_walks_answer");
    let wrong =
        |set: &IntervalSet| set.len() >= 2 && set.members() == Some(Num::from(set.len() as u64));
    let (mut answers, mut caught) = ([0usize; 2], 0usize);
    for kind in 0..5 {
        for case in 0..5000 {
            let set = wider_class_case(&mut rng, kind);
            let narrowed = match set.bounds() {
                Some((End::Fin(lo), End::Fin(hi))) => {
                    let v = lo + &Num::from(rng.int(0, 70)).min(hi - lo);
                    set.minus(&IntervalSet::point(v))
                }
                _ => set.minus(&IntervalSet::single(rng.int(-40, 40))),
            };
            for s in [&set, &narrowed] {
                let want = Classed::wider_class_walk(s);
                assert_eq!(
                    Classed::wider_class(s),
                    want,
                    "seed {seed}, kind {kind}, case {case}: {s:?}"
                );
                answers[usize::from(want)] += 1;
                caught += usize::from(wrong(s) != want);
            }
        }
    }
    assert!(
        answers[0] >= 1000 && answers[1] >= 1000,
        "seed {seed}: answers (false, true) {answers:?}"
    );
    assert!(
        caught > 0,
        "seed {seed}: the wrong check agreed with the walk on every case"
    );
}
