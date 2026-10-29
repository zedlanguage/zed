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
    let a = dom(IntervalSet::of(0, 10), one_mod_four, FiniteSet::Top);
    let b = dom(IntervalSet::of(1, 9), one_mod_four, FiniteSet::Top);
    let c = dom(
        IntervalSet::top(),
        Congruence::top(),
        FiniteSet::of([1, 5, 9]),
    );
    let d = dom(
        IntervalSet::of(1, 1).join(&IntervalSet::of(5, 9)),
        one_mod_four,
        FiniteSet::Top,
    );
    for x in [&b, &c, &d] {
        assert_eq!(a.normal(), x.normal());
        assert_eq!(addr(&index(a.clone())), addr(&index(x.clone())));
    }
    assert_eq!(a.normal().ints, IntervalSet::of(1, 9));
    assert_eq!(a.normal().class, one_mod_four);
    // `int[2..=4]` with `1 mod 4` admits nothing, like every other empty domain.
    let empty = dom(IntervalSet::of(2, 4), one_mod_four, FiniteSet::Top);
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
            IntervalSet::range(End::Fin(lo), End::PosInf),
            Congruence::new(2, 0),
            FiniteSet::Top,
        )
    };
    assert_eq!(even(1).normal(), even(2).normal());
    assert_ne!(even(0).normal(), even(2).normal());
    assert_ne!(addr(&index(even(0))), addr(&index(even(2))));
}

/// A random domain: up to three pieces with endpoints in -20..=20 or infinite, a class of
/// modulus 0, 1, 2, 3, 4 or 6, and half the time a finite set in -25..=25.
fn random(rng: &mut Rng) -> Domain {
    let end = |rng: &mut Rng, inf: End| {
        if rng.below(5) == 0 {
            inf
        } else {
            End::Fin(rng.int(-20, 20))
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
    let mut rng = Rng::new(0xd0d0);
    let mut by_members: BTreeMap<Vec<i64>, Domain> = BTreeMap::new();
    let mut collisions = 0;
    for _ in 0..RANDOM_INSTANCES * 8 {
        let d = random(&mut rng);
        let n = d.normal();
        assert_eq!(members(&n), members(&d), "{d:?}");
        assert_eq!(n.normal(), n, "not idempotent on {d:?}");
        assert_eq!(n.rank(), 0);
        match by_members.get(&members(&d)) {
            Some(m) => {
                assert_eq!(*m, n, "two normal forms for one set: {d:?}");
                collisions += 1;
            }
            None => {
                by_members.insert(members(&d), n);
            }
        }
    }
    // Many spellings of one set were met, so uniqueness was tested.
    assert!(collisions > 1_000, "{collisions}");
}
