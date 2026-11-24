//! Tests of [`ClassUnion`] against the sets of its values, read in a window.

use std::collections::BTreeSet;

use super::ClassUnion;
use crate::classed::Classed;
use crate::interval::{End, IntervalSet, Num};
use crate::lattice::Congruence;
use crate::seed::Rng;

/// The values in `-W..=W` that the tests read; every set drawn lies well inside.
const W: i64 = 40;

fn num(v: i64) -> Num {
    Num::from(v)
}

fn range(lo: i64, hi: i64) -> IntervalSet {
    IntervalSet::range(End::Fin(num(lo)), End::Fin(num(hi)))
}

/// A set of a random class (modulus 1 to 6) on one to three random ranges in `-30..=30`.
fn draw(rng: &mut Rng) -> Classed {
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

fn union_of(rng: &mut Rng) -> ClassUnion {
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

/// The values of a [`Classed`] in `-W..=W`, read by its own `contains`.
fn classed_values(c: &Classed) -> BTreeSet<i64> {
    (-W..=W).filter(|v| c.contains(*v)).collect()
}

/// The checks that hold of every union: each set nonempty, no two of one class, `at` true,
/// `into_classed` the same values as `contains`, `ranges` holding them all, and the union equal
/// to itself rebuilt in the reverse order of its sets.
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
    assert_eq!(
        classed_values(&u.clone().into_classed()),
        got,
        "{what}: `into_classed` differs"
    );
    let hull = u.ranges();
    assert!(
        got.iter().all(|v| hull.contains_end(&End::Fin(num(*v)))),
        "{what}: `ranges` misses a value"
    );
    let mut back = ClassUnion::empty();
    for s in u.sets.iter().rev() {
        back.add(s.clone());
    }
    assert_eq!(&back, u, "{what}: equality hangs on the order of the sets");
}

/// `join`, `meet_range`, `meet_classed`, `first` and equality on random unions, each checked
/// value by value against the same operation on the sets of values (`BTreeSet`), and every
/// result well formed. Red before green: with `meet_classed` meeting only the ranges (the
/// classes left as they were), the values outside the drawn class stay and the check fails.
#[test]
fn class_unions_agree_with_the_sets_of_their_values() {
    let (mut rng, seed) = Rng::fresh("class_unions_agree_with_the_sets_of_their_values");
    for case in 0..2000 {
        let (a, b) = (union_of(&mut rng), union_of(&mut rng));
        let what = |op: &str| format!("seed {seed}, case {case}, {op}: {a:?} and {b:?}");
        let (va, vb) = (values(&a), values(&b));
        well_formed(&a, &what("a"));
        let j = a.join(&b);
        well_formed(&j, &what("join"));
        assert_eq!(values(&j), &va | &vb, "{}", what("join"));
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
        let c = draw(&mut rng);
        let mc = a.meet_classed(&c);
        well_formed(&mc, &what("meet_classed"));
        assert_eq!(
            values(&mc),
            &va & &classed_values(&c),
            "{}: meet_classed with {c:?}",
            what("meet_classed")
        );
        if va != vb {
            assert_ne!(a, b, "{}: unequal values compare equal", what("eq"));
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
                (a.sets.iter()).any(|s| s.class == class && s.ranges.contains_end(&hi)),
                "{}",
                what("first")
            );
        } else {
            assert!(va.is_empty(), "{}", what("first"));
        }
    }
}

/// The odd values of `0..=2r` and the multiples of 4 there, joined: two sets of two ranges in
/// all at every `r`, never a range a value, so the cost of the union does not grow with the
/// range (the reason for [`ClassUnion`]); `into_classed` of the two lists them, as one
/// [`Classed`] of two classes must.
#[test]
fn a_union_of_two_classes_does_not_list_their_values() {
    for r in [1_000i64, 1_000_000] {
        let odd = Classed::new(range(0, 2 * r), Congruence::new(num(2), num(1)));
        let fours = Classed::new(range(0, 2 * r), Congruence::new(num(4), num(0)));
        let u = ClassUnion::of(odd).join(&ClassUnion::of(fours));
        assert_eq!(u.sets().len(), 2, "r = {r}");
        assert_eq!(u.len(), 2, "r = {r}");
        assert!(u.contains(&End::Fin(num(2 * r))), "r = {r}");
        assert!(!u.contains(&End::Fin(num(2))), "r = {r}");
    }
}
