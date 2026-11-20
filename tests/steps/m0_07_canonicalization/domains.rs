//! Domain normal forms: integer facts that admit the same integers share a normal form and
//! an address, checked on the examples of sec:constraints and by brute force.

use std::collections::BTreeMap;

use zed_kernel::term::build::var;
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::canon::{Def, Domain};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::{Congruence, FiniteSet, Lattice};

use super::addr;

fn dom(ints: IntervalSet, class: Congruence, finite: FiniteSet<i64>) -> Domain {
    Domain {
        ints,
        class,
        finite,
    }
}

/// `index: <domain> = i` as a definition.
fn index(d: Domain) -> Def {
    Def {
        name: "index".into(),
        domain: Some(d),
        facets: vec![],
        body: var("i"),
    }
}

#[test]
fn one_set_of_integers_has_one_normal_form() {
    let one_mod_four = Congruence::new(4, 1);
    let a = dom(IntervalSet::of(0, 10), one_mod_four.clone(), FiniteSet::Top);
    let b = dom(IntervalSet::of(1, 9), one_mod_four.clone(), FiniteSet::Top);
    let c = dom(
        IntervalSet::top(),
        Congruence::top(),
        FiniteSet::of([1, 5, 9]),
    );
    let d = dom(
        IntervalSet::of(1, 1).join(&IntervalSet::of(5, 9)),
        one_mod_four.clone(),
        FiniteSet::Top,
    );
    for x in [&b, &c, &d] {
        assert_eq!(a.normal(), x.normal());
        assert_eq!(addr(&index(a.clone())), addr(&index(x.clone())));
    }
    assert_eq!(a.normal().ints, IntervalSet::of(1, 9));
    assert_eq!(a.normal().class, one_mod_four);
    // `int[2..=4]` with `1 mod 4` admits nothing, like every other empty domain.
    let empty = dom(IntervalSet::of(2, 4), one_mod_four.clone(), FiniteSet::Top);
    let none = dom(IntervalSet::top(), Congruence::top(), FiniteSet::of([]));
    assert_eq!(empty.normal(), none.normal());
    // An HTTP status in 400..=499 among the codes the client handles is just 404.
    let status = dom(
        IntervalSet::of(400, 499),
        Congruence::top(),
        FiniteSet::of([200, 404, 500]),
    );
    assert_eq!(
        status.normal(),
        dom(
            IntervalSet::single(404),
            Congruence::single(404),
            FiniteSet::Top
        )
    );
    // An even count of at least 2 is not an even count from 0.
    let even = |lo| {
        dom(
            IntervalSet::range(End::of(lo), End::PosInf),
            Congruence::new(2, 0),
            FiniteSet::Top,
        )
    };
    assert_eq!(even(1).normal(), even(2).normal());
    assert_ne!(even(0).normal(), even(2).normal());
    assert_ne!(addr(&index(even(0))), addr(&index(even(2))));
}

/// A class built with its fields directly, not by `Congruence::new`, can hold a residue
/// outside `0..modulus` or a negative modulus (the fields are public). Its normal form is
/// that of the same class built by `new`, so one set of integers keeps one address, and the
/// normal form is its own normal form (the domain rule applies once: `Domain::normal`'s
/// proof, step 2). Before the class was normalized, `9 mod 4` and `1 mod 4` over `0..=10`
/// gave two normal forms.
#[test]
fn a_class_built_with_its_fields_has_the_normal_form_of_the_same_class() {
    let made = Congruence::new(4, 1);
    let at = |class: Congruence| dom(IntervalSet::of(0, 10), class, FiniteSet::Top);
    for raw in [(4, 9), (4, -3), (-4, 1), (-4, 9)] {
        let written = Congruence::Class {
            modulus: raw.0.into(),
            residue: raw.1.into(),
        };
        let n = at(written.clone()).normal();
        assert_eq!(n, at(made.clone()).normal(), "{raw:?}");
        assert_eq!(n.normal(), n, "{raw:?}");
        assert_eq!(addr(&index(at(written))), addr(&index(at(made.clone()))), "{raw:?}");
    }
}

/// A random domain: up to three pieces with endpoints in -20..=20 or infinite, a class of
/// modulus 0, 1, 2, 3, 4 or 6, and half the time a finite set in -25..=25.
fn random(rng: &mut Rng) -> Domain {
    let end = |rng: &mut Rng, inf: End| {
        if rng.below(5) == 0 {
            inf
        } else {
            End::of(rng.int(-20, 20))
        }
    };
    let pieces = (0..rng.below(4))
        .map(|_| (end(rng, End::NegInf), end(rng, End::PosInf)))
        .collect();
    let class = Congruence::new(rng.pick(&[0, 1, 1, 2, 3, 4, 6]), rng.int(-20, 20));
    let finite = if rng.below(2) == 0 {
        FiniteSet::Top
    } else {
        FiniteSet::of((0..rng.below(7)).map(|_| rng.int(-25, 25)))
    };
    dom(IntervalSet::from_pieces(pieces), class, finite)
}

/// The members in -60..=60. Beyond ±25 every domain above repeats with a period dividing 12,
/// so this window decides equality of the sets admitted.
fn members(d: &Domain) -> Vec<i64> {
    (-60..=60).filter(|&v| d.contains(v)).collect()
}

#[test]
fn the_normal_form_admits_the_same_integers_and_is_unique() {
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_normal_form_admits_the_same_integers_and_is_unique",
    ));
    let mut by_members: BTreeMap<Vec<i64>, Domain> = BTreeMap::new();
    for _ in 0..RANDOM_INSTANCES * 2 {
        one_normal_form_per_set(&mut by_members, random(&mut rng));
    }
    // Spellings built to admit one set, the even numbers 0..=10: as the integers 0..=11 of
    // class 0 mod 2, as 0..=10 of that class, and as 0..=10 of every class with the finite set
    // {0, 2, …, 10}. The second and third meet the set the first recorded.
    let mut by_members = BTreeMap::new();
    let evens = || FiniteSet::of((0..=5).map(|k| 2 * k));
    let spellings = [
        dom(
            IntervalSet::of(0, 11),
            Congruence::new(2, 0),
            FiniteSet::Top,
        ),
        dom(
            IntervalSet::of(0, 10),
            Congruence::new(2, 0),
            FiniteSet::Top,
        ),
        dom(IntervalSet::of(0, 10), Congruence::new(1, 0), evens()),
    ];
    let met: Vec<bool> = spellings
        .into_iter()
        .map(|d| one_normal_form_per_set(&mut by_members, d))
        .collect();
    assert_eq!(met, [false, true, true], "three spellings of one set");
}

/// Asserts that `d`'s normal form admits the same integers, is its own normal form, and is the
/// normal form recorded in `by_members` for the same set, if one is; records it otherwise.
/// Returns whether one was recorded already.
fn one_normal_form_per_set(by_members: &mut BTreeMap<Vec<i64>, Domain>, d: Domain) -> bool {
    let n = d.normal();
    assert_eq!(members(&n), members(&d), "{d:?}");
    assert_eq!(n.normal(), n, "not idempotent on {d:?}");
    assert_eq!(n.rank(), 0);
    match by_members.get(&members(&d)) {
        Some(m) => {
            assert_eq!(*m, n, "two normal forms for one set: {d:?}");
            true
        }
        None => {
            by_members.insert(members(&d), n);
            false
        }
    }
}
