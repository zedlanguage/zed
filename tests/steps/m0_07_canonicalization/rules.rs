//! The rules: facet ordering and hints, the termination ranks, the independence of the
//! normal form from the order the rules are applied in, and a pinned address.

use std::sync::Arc;

use zed_kernel::term::Prim;
use zed_kernel::term::build::{lam, let_, lit, prim, var};
use zed_kernel::value::Value;
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::canon::{Def, Domain, Facet, RULES, canonicalize, ranks, serialize};
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
    let mut rng = Rng::new(zed_tests::seed::seed(
        "every_rule_decreases_its_rank_and_no_later_rule_raises_an_earlier_one",
    ));
    for _ in 0..RANDOM_INSTANCES / 4 {
        ranks_fall(random(&mut rng));
    }
    // A definition built so that each rule fires: the binder written `x` is not spelled as its
    // level, 0 (binders); one facet is a hint, and the binders rule adds a second, the
    // written name it records as a hint facet (hints); `units` before `doc` is out of order
    // (facets); and `0..=10` with every member a multiple of 3 is not in normal form, whose
    // ends are members, `0..=9` (domain).
    let mut d = def("d", lam(&["x"], var("x")));
    d.facets = vec![facet("units", "cent"), facet("doc", 1)];
    d.facets.push(Facet {
        hint: true,
        kind: "doc".into(),
        value: Value::str("a hint"),
    });
    d.domain = Some(Domain {
        ints: IntervalSet::of(0, 10),
        class: Congruence::new(3, 0),
        finite: FiniteSet::Top,
    });
    let fired = ranks_fall(d);
    assert!(fired.iter().all(|&n| n > 0), "each rule fires: {fired:?}");
}

/// Applies the rules to `d` one step at a time until none applies, asserting that each step
/// lowers its rule's rank and raises no earlier rule's; returns how often each rule fired.
fn ranks_fall(mut d: Def) -> [usize; 4] {
    let mut fired = [0usize; 4];
    loop {
        let before = ranks(&d);
        let Some(r) = RULES.iter().position(|r| (r.apply)(&mut d)) else {
            return fired;
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

/// The canonicalizer sorts the facets by each kind's rank among the kinds present, not by the
/// kinds' text (FAIL-ratio-facet-sort). Long lists of facets of kinds that are prefixes of one
/// another and whose first appearance is not their text order, with values of every scalar
/// kind and tuples, repeats and hints, end as the hint and facet rules applied one step at a
/// time leave them.
#[test]
fn many_facets_of_many_kinds_end_as_the_rules_leave_them() {
    let mut rng = Rng::new(zed_tests::seed::seed(
        "many_facets_of_many_kinds_end_as_the_rules_leave_them",
    ));
    let kinds = ["units", "unit", "u", "doc", "monotone", "units2", ""];
    for _ in 0..RANDOM_INSTANCES / 4 {
        let facets = (0..rng.below(40))
            .map(|_| {
                let i = rng.int(-2, 2);
                Facet {
                    hint: rng.below(4) == 0,
                    kind: Arc::from(rng.pick(&kinds)),
                    value: match rng.below(5) {
                        0 => Value::Int(i),
                        1 => Value::from(i > 0),
                        2 => Value::from(["a", "ab", "b"][i.unsigned_abs() as usize % 3]),
                        3 => Value::atom(["none", "inc"][i.unsigned_abs() as usize % 2]),
                        _ => Value::tuple(vec![Value::Int(i), Value::from("a")]),
                    },
                }
            })
            .collect::<Vec<_>>();
        facets_end_as_the_rules_leave_them(facets);
    }
    // A list built with a repeat: `u = 1` twice, not hints, so the facet rule meets the equal
    // neighbors once sorted and drops one, leaving one facet of the two kept.
    let dropped = facets_end_as_the_rules_leave_them(vec![facet("u", 1), facet("u", 1)]);
    assert!(dropped, "the repeated facet is dropped");
}

/// Asserts that the canonicalizer leaves `facets` as the rules applied one step at a time
/// leave them; returns whether it dropped a repeated non-hint facet.
fn facets_end_as_the_rules_leave_them(facets: Vec<Facet>) -> bool {
    let mut d = def("d", lit(0));
    d.facets = facets;
    let normal = canonicalize(&d);
    let mut stepped = d.clone();
    while RULES.iter().any(|r| (r.apply)(&mut stepped)) {}
    assert_eq!(normal.facets, stepped.facets, "{:?}", d.facets);
    let kept = d.facets.iter().filter(|f| !f.hint).count();
    normal.facets.len() < kept
}

#[test]
fn the_normal_form_does_not_depend_on_the_order_of_the_rules() {
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_normal_form_does_not_depend_on_the_order_of_the_rules",
    ));
    for _ in 0..RANDOM_INSTANCES / 4 {
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
fn the_address_is_pinned() {
    // The address of this definition (A106, 2026-11-20: no version number is hashed). A change
    // to a rule or to the serialization that reaches it changes it: pin the new address here.
    let d = balance("deposits", "withdrawals");
    assert_eq!(
        addr(&d).to_string(),
        "b42441440765f50183ade7d35a3b304090242b90c975073af55d3d94e688c269"
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
            let same = serialize(a, &none).expect("memory for the bytes")
                == serialize(b, &none).expect("memory for the bytes");
            assert_eq!(same, a == b, "{a:?}\n{b:?}");
            equal += usize::from(same);
        }
    }
    // Beyond the diagonal, distinct random definitions met in one normal form.
    assert!(equal > forms.len(), "{equal}");
    assert_eq!(addr(&forms[0]).to_string().len(), 64);
}
