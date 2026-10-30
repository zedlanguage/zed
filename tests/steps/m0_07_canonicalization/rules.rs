//! The rules: facet ordering and hints, the termination ranks, the independence of the
//! normal form from the order the rules are applied in, and the version tag.

use std::sync::Arc;

use zed_kernel::term::Prim;
use zed_kernel::term::build::{lam, let_, lit, prim, var};
use zed_kernel::value::Value;
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::canon::{Def, Domain, Facet, RULES, VERSION, address_at, canonicalize, ranks, serialize};
use zedc::store::interval::IntervalSet;
use zedc::store::lattice::{Congruence, FiniteSet};

use super::{addr, def, facet, none};

/// `balance = (deposits, withdrawals) -> deposits - withdrawals`, in units of cents.
fn balance(a: &str, b: &str) -> Def {
    let mut d = def(
        "balance",
        lam(&[a, b], prim(Prim::Sub, vec![var(a), var(b)])),
    );
    d.facets = vec![
        facet("units", "cent"),
        facet("monotone", Value::atom("none")),
    ];
    d
}

#[test]
fn facets_in_any_order_and_repeated_give_one_address() {
    let a = balance("deposits", "withdrawals");
    let mut b = balance("d", "w");
    b.facets.reverse();
    b.facets.push(facet("units", "cent"));
    assert_eq!(addr(&a), addr(&b));
    // A hint never changes the address; a changed facet value does.
    b.facets.push(Facet {
        hint: true,
        kind: "doc".into(),
        value: Value::str("the account balance"),
    });
    assert_eq!(addr(&a), addr(&b));
    let mut c = a.clone();
    c.facets[0] = facet("units", "dollar");
    assert_ne!(addr(&a), addr(&c));
    // The normal form keeps the facets sorted, once each.
    let n = canonicalize(&b);
    assert_eq!(n.facets.len(), 2);
    assert!(n.facets.windows(2).all(|w| w[0] < w[1]));
}

/// A random definition: a body with binders, facets with repeats and hints in random order,
/// and sometimes a domain.
fn random(rng: &mut Rng) -> Def {
    let names = ["n", "acc", "row"];
    let mut body = var(rng.pick(&names));
    for _ in 0..rng.below(5) {
        let x = rng.pick(&names);
        body = match rng.below(2) {
            0 => lam(&[x], body),
            _ => let_(x, lit(rng.int(0, 3)), prim(Prim::Add, vec![body, var(x)])),
        };
    }
    let facets = (0..rng.below(6))
        .map(|_| Facet {
            hint: rng.below(3) == 0,
            kind: Arc::from(rng.pick(&["units", "monotone", "doc"])),
            value: Value::Int(rng.int(0, 2)),
        })
        .collect();
    let domain = (rng.below(2) == 0).then(|| Domain {
        ints: IntervalSet::of(rng.int(-5, 5), rng.int(-5, 15)),
        class: Congruence::new(rng.pick(&[1, 2, 3]), rng.int(0, 2)),
        finite: if rng.below(2) == 0 {
            FiniteSet::Top
        } else {
            FiniteSet::of((0..3).map(|_| rng.int(-5, 15)))
        },
    });
    Def {
        name: "d".into(),
        domain,
        facets,
        body,
    }
}

#[test]
fn every_rule_decreases_its_rank_and_no_later_rule_raises_an_earlier_one() {
    let mut rng = Rng::new(0x7e57);
    let mut fired = [0usize; 4];
    for _ in 0..RANDOM_INSTANCES {
        let mut d = random(&mut rng);
        loop {
            let before = ranks(&d);
            let Some(r) = RULES.iter().position(|r| (r.apply)(&mut d)) else {
                break;
            };
            let after = ranks(&d);
            fired[r] += 1;
            assert!(
                after[r] < before[r],
                "{} did not decrease its rank",
                RULES[r].name
            );
            for e in 0..r {
                assert!(
                    after[e] <= before[e],
                    "{} raised the rank of {}",
                    RULES[r].name,
                    RULES[e].name
                );
            }
            assert!(after < before);
        }
    }
    assert!(fired.iter().all(|&n| n > 50), "{fired:?}");
}

#[test]
fn the_facet_rank_counts_the_pairs_out_of_order_and_the_facets() {
    let mut d = def("d", lit(0));
    let (a, b, c) = (facet("doc", 1), facet("doc", 2), facet("doc", 3));
    // `c a a b`: `c` is before three smaller facets; the equal `a`s are not out of order.
    d.facets = vec![c.clone(), a.clone(), a.clone(), b.clone()];
    assert_eq!(ranks(&d)[2], 3 + 4);
    d.facets = vec![b, c, a];
    assert_eq!(ranks(&d)[2], 2 + 3);
}

#[test]
fn the_normal_form_does_not_depend_on_the_order_of_the_rules() {
    let mut rng = Rng::new(0xc0f1);
    for _ in 0..RANDOM_INSTANCES {
        let d0 = random(&mut rng);
        let mut d = d0.clone();
        // Any rule that applies, chosen at random, until none does.
        loop {
            let live: Vec<usize> = (0..RULES.len())
                .filter(|&r| (RULES[r].apply)(&mut d.clone()))
                .collect();
            if live.is_empty() {
                break;
            }
            (RULES[live[rng.below(live.len())]].apply)(&mut d);
        }
        assert_eq!(d, canonicalize(&d0));
    }
}

#[test]
fn the_version_tag_separates_rule_sets() {
    let d = balance("deposits", "withdrawals");
    assert_eq!(VERSION, 2);
    assert_ne!(
        address_at(VERSION, &d, &none),
        address_at(VERSION + 1, &d, &none)
    );
    // The address of this definition under version 2. A change to a rule or to the
    // serialization changes it: increment VERSION, and pin the new address here.
    assert_eq!(
        addr(&d).to_string(),
        "44c341e4f0e9d1f74b145c2678686615f33c73594579e44571313e589ba55425"
    );
}

#[test]
fn two_normal_forms_share_a_serialization_only_when_equal() {
    let mut rng = Rng::new(0x5e71);
    let forms: Vec<Def> = (0..RANDOM_INSTANCES / 2)
        .map(|_| canonicalize(&random(&mut rng)))
        .collect();
    let mut equal = 0;
    for a in &forms {
        for b in &forms {
            let same = serialize(a, &none) == serialize(b, &none);
            assert_eq!(same, a == b, "{a:?}\n{b:?}");
            equal += usize::from(same);
        }
    }
    // Beyond the diagonal, distinct random definitions met in one normal form.
    assert!(equal > forms.len(), "{equal}");
    assert_eq!(addr(&forms[0]).to_string().len(), 64);
}
