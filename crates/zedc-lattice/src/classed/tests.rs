//! Tests of [`Classed`] with the plain-set shortcut of [`Classed::new`] taken and not taken
//! ([`plain_shortcut::both`], VERIFY-classed-wider-class-callers).

use super::{Classed, Tail, plain_shortcut};
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

/// A residue table modulo `n·reps`: a block of `n` letters with both kinds, repeated `reps`
/// times, so that [`Tail::new`] has a table to cut to its least period.
fn random_table(rng: &mut Rng) -> Vec<bool> {
    let n = rng.int(2, 6) as usize;
    let block: Vec<bool> = loop {
        let b: Vec<bool> = (0..n).map(|_| rng.coin()).collect();
        if b.contains(&true) && b.contains(&false) {
            break b;
        }
    };
    let reps = rng.int(1, 3) as usize;
    (0..n * reps).map(|i| block[i % n]).collect()
}

/// Whether `table` marks the residue of `v`.
fn marks(table: &[bool], v: i64) -> bool {
    table[v.rem_euclid(table.len() as i64) as usize]
}

/// Sets with tails (row CLASSED-periodic-tail) read value by value against the set they stand
/// for, listed: a random finite middle, a tail above, below, both (apart, or meeting with no
/// value between), or one tail over every value, each table random and repeated up to three
/// times. Every value within 15 of the middle is checked, and each again at a distance
/// `M = 720720·10^9` above and below, a multiple of every table length here (up to 18), where
/// only a tail can hold it. Negative controls: the wider set (tails dropped) differs from the
/// listed one in some case, and so does a reading of the tail above by the residue of
/// `v + 1`.
#[test]
fn tailed_sets_agree_with_the_values_listed() {
    const W: i64 = 20;
    const M: i64 = 720_720_000_000_000;
    let (mut rng, seed) = Rng::fresh("tailed_sets_agree_with_the_values_listed");
    let (mut wider_differs, mut shifted_differs) = (0, 0);
    for case in 0..3000 {
        let middle: Vec<bool> = (-W..=W).map(|_| rng.coin()).collect();
        let in_middle = |v: i64| (-W..=W).contains(&v) && middle[(v + W) as usize];
        let (up, down) = (random_table(&mut rng), random_table(&mut rng));
        let kind = rng.below(4);
        // The first value at or above (below) a random start that the table marks: the end of
        // a tail is a member.
        let mut u = rng.int(-W, W + 5);
        while !marks(&up, u) {
            u += 1;
        }
        let mut l = rng.int(-W - 5, W);
        while !marks(&down, l) {
            l -= 1;
        }
        let (above, below) = match kind {
            0 => (Some(u), None),
            1 => (None, Some(l)),
            2 => {
                // Apart, or close: `l` the first mark below `u`, and `u` then the first mark
                // from `l + 1` up, so the ends meet where the table above marks `l + 1`.
                if rng.coin() {
                    let lo = l.min(u - 1);
                    let mut l = lo;
                    while !marks(&down, l) {
                        l -= 1;
                    }
                    (Some(u), Some(l))
                } else {
                    let mut l = u - 1;
                    while !marks(&down, l) {
                        l -= 1;
                    }
                    let u2 = l + 1;
                    let mut u = u2;
                    while !marks(&up, u) {
                        u += 1;
                    }
                    (Some(u), Some(l))
                }
            }
            _ => (None, None),
        };
        let whole = kind == 3;
        let truth = |v: i64| match (whole, above, below) {
            (true, _, _) => marks(&up, v),
            (_, Some(u), _) if v >= u => marks(&up, v),
            (_, _, Some(l)) if v <= l => marks(&down, v),
            _ => in_middle(v),
        };
        let mut pieces: Vec<(End, End)> = (-W - 30..=W + 30)
            .filter(|&v| above.is_none_or(|u| v < u) && below.is_none_or(|l| v > l) && truth(v))
            .map(|v| (End::of(v), End::of(v)))
            .collect();
        if let Some(u) = above {
            pieces.push((End::of(u), End::PosInf));
        }
        if let Some(l) = below {
            pieces.push((End::NegInf, End::of(l)));
        }
        let set = if whole {
            let tail = Tail::new(End::NegInf, &up);
            Classed::tailed(Classed::plain(IntervalSet::top()), None, Some(tail))
        } else {
            Classed::tailed(
                Classed::plain(IntervalSet::from_pieces(pieces)),
                below.map(|l| Tail::new(End::of(l), &down)),
                above.map(|u| Tail::new(End::of(u), &up)),
            )
        };
        assert!(set.tails.is_some(), "seed {seed}, case {case}");
        let wider = set.without_tails();
        for v in -W - 15..=W + 15 {
            assert_eq!(
                set.contains(v),
                truth(v),
                "seed {seed}, case {case}, {v}: {set:?}"
            );
            wider_differs += usize::from(wider.contains(v) != truth(v));
            assert!(
                !truth(v) || wider.contains(v),
                "seed {seed}, case {case}: wider"
            );
            for far in [v + M, v - M] {
                let want = match (whole, above, below) {
                    (true, _, _) => marks(&up, far),
                    (_, Some(_), _) if far > 0 => marks(&up, far),
                    (_, _, Some(_)) if far < 0 => marks(&down, far),
                    _ => false,
                };
                assert_eq!(
                    set.contains_end(&End::of(far)),
                    want,
                    "seed {seed}, case {case}, {far}: {set:?}"
                );
            }
            if above.is_some_and(|u| v >= u) {
                shifted_differs += usize::from(marks(&up, v + 1) != truth(v));
            }
        }
    }
    assert!(
        wider_differs > 0 && shifted_differs > 0,
        "seed {seed}: the controls"
    );
}

/// One set has one form: a table repeated is cut to its least period (corner: a table of
/// period 2 written as 6 letters, and one whose least period is its length), so two writings
/// of one tailed set are equal and hash alike, and a tailed set is never equal to a set of
/// ranges.
#[test]
fn tailed_sets_of_one_set_are_equal() {
    use std::hash::{BuildHasher, RandomState};
    let (t, f) = (true, false);
    let short = Tail::new(End::of(0), &[t, f]);
    let long = Tail::new(End::of(0), &[t, f, t, f, t, f]);
    assert_eq!(short, long);
    assert_eq!(long.step, Num::from(2));
    assert_eq!(&*long.have, &[t, f]);
    let odd = Tail::new(End::of(0), &[t, t, f]);
    assert_eq!(odd.step, Num::from(3));
    let wider = || Classed::plain(IntervalSet::range(End::of(0), End::PosInf));
    let a = Classed::tailed(wider(), None, Some(short));
    let b = Classed::tailed(wider(), None, Some(long));
    let hasher = RandomState::new();
    assert_eq!(a, b);
    assert_eq!(hasher.hash_one(&a), hasher.hash_one(&b));
    assert!(a != IntervalSet::range(End::of(0), End::PosInf));
    assert!(wider() == IntervalSet::range(End::of(0), End::PosInf));
    assert_ne!(a, wider(), "the tails are read by ==");
}

/// Corners of the form: no tails gives the set as it was (here empty, so a tailed form of the
/// empty set is never made); a middle of one value, class of modulus 0, beside a tail; a tail
/// over every value (end `-inf`); and a tail whose end is a kept value too wide to build,
/// `3^(2^40)`, read by its order and its residue modulo 6 (3, as `3^k` is 3 mod 6 for k >= 1).
#[test]
fn tailed_corners_read_their_members() {
    let (t, f) = (true, false);
    let empty = Classed::plain(IntervalSet::empty());
    let same = Classed::tailed(empty.clone(), None, None);
    assert!(same.tails.is_none() && same.is_empty() && same == empty);
    // Modulus 0, the class of one value: with no tails, the set as it was.
    let one = Classed::new(IntervalSet::of(5, 5), Congruence::new(0, 5));
    let same = Classed::tailed(one.clone(), None, None);
    assert!(same == one && same.contains(5) && !same.contains(6));
    // The one value 5, then the even values from 10 up.
    let ranges = IntervalSet::of(5, 5).join(&IntervalSet::range(End::of(10), End::PosInf));
    let set = Classed::tailed(
        Classed::plain(ranges),
        None,
        Some(Tail::new(End::of(10), &[t, f])),
    );
    let want = |v: i64| v == 5 || (v >= 10 && v % 2 == 0);
    for v in -10..40 {
        assert_eq!(set.contains(v), want(v), "{v}");
    }
    // A tail over every value: the multiples of 3.
    let thirds = Classed::tailed(
        Classed::plain(IntervalSet::top()),
        None,
        Some(Tail::new(End::NegInf, &[t, f, f])),
    );
    for v in -30..30 {
        assert_eq!(thirds.contains(v), v % 3 == 0, "{v}");
    }
    // A tail from a kept value: `[3^(2^40), +inf)` with the residues 3 and 4 modulo 6.
    let k = Num::from(
        &zed_kernel::num::Rat::int(3.into())
            .pow(&(num_bigint::BigUint::from(1u32) << 40u32))
            .expect("a power of a prime is kept"),
    );
    let ranges = IntervalSet::of(0, 10).join(&IntervalSet::range(End::Fin(k.clone()), End::PosInf));
    let table = [f, f, f, t, t, f];
    let set = Classed::tailed(
        Classed::plain(ranges),
        None,
        Some(Tail::new(End::Fin(k.clone()), &table)),
    );
    let at = |d: i64| set.contains_end(&End::Fin(&k + &Num::from(d)));
    assert_eq!(
        (at(-1), at(0), at(1), at(2), at(3), at(6), at(7)),
        (false, true, true, false, false, true, true)
    );
    assert!(set.contains(5) && !set.contains(11));
}
