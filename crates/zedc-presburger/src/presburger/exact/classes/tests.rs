use std::collections::BTreeSet;

use super::*;

/// The values in `-W..=W` that the tests read; every set drawn lies well inside.
const W: i64 = 40;

/// A meter with no limit, for the operations that charge one.
fn no_limit() -> Work {
    Work {
        used: 0,
        limit: u64::MAX,
        solver: super::super::super::SOLVER,
    }
}

fn num(v: i64) -> Num {
    Num::from(v)
}

fn range(lo: i64, hi: i64) -> IntervalSet {
    IntervalSet::range(End::Fin(num(lo)), End::Fin(num(hi)))
}

/// A set of a random class (modulus 1 to 6) on one to three random ranges in `-30..=30`.
fn draw(rng: &mut crate::seed::Rng) -> Classed {
    let m = rng.int(1, 6);
    let r = rng.int(0, m - 1);
    let mut pieces = Vec::new();
    for _ in 0..rng.int(1, 3) {
        let lo = rng.int(-30, 30);
        let hi = lo + rng.int(0, 20);
        pieces.push((End::Fin(num(lo)), End::Fin(num(hi))));
    }
    Classed::new(
        IntervalSet::from_pieces(pieces),
        Congruence::new(num(m), num(r)),
    )
}

fn union_of(rng: &mut crate::seed::Rng) -> ClassUnion {
    let mut u = ClassUnion::empty();
    for _ in 0..rng.int(0, 4) {
        u.add(draw(rng));
    }
    u
}

/// The values of `u` in `-W..=W`, read by `contains`.
fn values(u: &ClassUnion) -> BTreeSet<i64> {
    (-W..=W)
        .filter(|v| u.contains(&End::Fin(num(*v))))
        .collect()
}

/// The values of a [`Classed`] in `-W..=W`, read from its plain set.
fn classed_values(c: &Classed) -> BTreeSet<i64> {
    let met = c.met();
    (-W..=W)
        .filter(|v| met.contains_end(&End::Fin(num(*v))))
        .collect()
}

/// The checks that hold of every union: each set nonempty, no two of one class, `at` true,
/// `met` and `into_classed` the same values as `contains`, `into_classed` the one form of
/// those values (as `Classed::plain` of the listed set gives), and `ranges` holding them all.
fn well_formed(u: &ClassUnion, what: &str) {
    let mut classes = BTreeSet::new();
    for (i, s) in u.sets.iter().enumerate() {
        assert!(!s.is_empty(), "{what}: an empty set kept");
        assert!(
            classes.insert(format!("{:?}", s.class)),
            "{what}: two sets of one class"
        );
        assert_eq!(u.at.get(&s.class), Some(&i), "{what}: `at` out of step");
    }
    assert_eq!(
        u.at.len(),
        u.sets.len(),
        "{what}: `at` holds a class no set has"
    );
    let got = values(u);
    let met = u.met(&mut no_limit()).expect("no limit");
    let listed: BTreeSet<i64> = (-W..=W)
        .filter(|v| met.contains_end(&End::Fin(num(*v))))
        .collect();
    assert_eq!(listed, got, "{what}: `met` differs from `contains`");
    let one = u.clone().into_classed();
    assert_eq!(classed_values(&one), got, "{what}: `into_classed` differs");
    assert_eq!(
        one,
        Classed::plain(met),
        "{what}: `into_classed` not the one form"
    );
    let hull = u.ranges();
    assert!(
        got.iter().all(|v| hull.contains_end(&End::Fin(num(*v)))),
        "{what}: `ranges` misses a value"
    );
}

/// `join`, `minus`, `meet_range` and `cut` on random unions, each checked value by value
/// against the same operation on the sets of values (`BTreeSet`), and every result well
/// formed. Red before green: with `cut` keeping only the outside part (`(R \ S) ∩ C`, the
/// values of `R ∩ S` in `C \ D` dropped), `minus` loses values and the check fails.
#[test]
fn class_unions_agree_with_the_sets_of_their_values() {
    let (mut rng, seed) =
        crate::seed::Rng::fresh("class_unions_agree_with_the_sets_of_their_values");
    for case in 0..2000 {
        let (a, b) = (union_of(&mut rng), union_of(&mut rng));
        let what = |op: &str| format!("seed {seed}, case {case}, {op}: {a:?} and {b:?}");
        let (va, vb) = (values(&a), values(&b));
        well_formed(&a, &what("a"));
        let j = a.join(&b);
        well_formed(&j, &what("join"));
        assert_eq!(values(&j), &va | &vb, "{}", what("join"));
        let d = a.minus(&b, &mut no_limit()).expect("no limit");
        well_formed(&d, &what("minus"));
        assert_eq!(values(&d), &va - &vb, "{}", what("minus"));
        let lo = rng.int(-35, 35);
        let hi = lo + rng.int(0, 30);
        let m = a.meet_range(&range(lo, hi));
        well_formed(&m, &what("meet_range"));
        let inside: BTreeSet<i64> = va
            .iter()
            .copied()
            .filter(|v| (lo..=hi).contains(v))
            .collect();
        assert_eq!(values(&m), inside, "{}", what("meet_range"));
        if let (Some(x), Some(y)) = (a.sets.first(), b.sets.first()) {
            let mut c = ClassUnion::empty();
            for s in cut(x, y, &mut no_limit()).expect("no limit") {
                c.add(s);
            }
            let want = &classed_values(x) - &classed_values(y);
            assert_eq!(values(&c), want, "{}", what("cut"));
        }
        if let Some(((lo, hi), class)) = a.first() {
            let least = va.iter().next().copied();
            assert_eq!(
                lo,
                End::Fin(num(least.expect("a value"))),
                "{}",
                what("first")
            );
            assert!(
                a.sets
                    .iter()
                    .any(|s| s.class == class && s.ranges.contains_end(&hi))
            );
        } else {
            assert!(va.is_empty(), "{}", what("first"));
        }
    }
}

/// The odd values cut from a range of a million: two sets, never a range a value, so the cost
/// does not grow with the range (the reason for [`ClassUnion`]).
#[test]
fn a_class_cut_from_a_long_range_is_not_listed() {
    let r = 1_000_000;
    let whole = ClassUnion::plain(range(0, 2 * r));
    let evens = ClassUnion::of(Classed::new(
        range(0, 2 * r),
        Congruence::new(num(2), num(0)),
    ));
    let odds = whole.minus(&evens, &mut no_limit()).expect("no limit");
    assert_eq!(odds.len(), 1);
    let only = &odds.sets()[0];
    assert_eq!(only.class, Congruence::new(num(2), num(1)));
    assert_eq!(only.ranges, range(1, 2 * r - 1));
    let none = (odds.join(&evens))
        .minus(&whole, &mut no_limit())
        .expect("no limit");
    assert!(none.is_empty());
}
