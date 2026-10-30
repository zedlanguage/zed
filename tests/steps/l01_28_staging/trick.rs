//! The Trick: split a function on a parameter only when its domain is finite and small, and
//! the split function computes what the function does.

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Term, Value, World};
use zedc::stage::{BUILD_FUEL, Choice, Domain, SPLIT_CAP, split, trick};

use crate::l01_16_elaboration::{elab, with_prelude};

fn count(c: &Choice) -> usize {
    match c {
        Choice::Split(vs) => vs.len(),
        Choice::Keep(why) => panic!("kept: {why}"),
    }
}

#[test]
fn a_bounded_domain_is_split_and_an_unbounded_one_is_kept() {
    assert_eq!(
        count(&trick(&Domain::Ints(Some(0), Some(256)), SPLIT_CAP)),
        257
    );
    assert_eq!(
        count(&trick(&Domain::Ints(Some(1), Some(1024)), SPLIT_CAP)),
        1024
    );
    assert!(matches!(
        trick(&Domain::Ints(Some(0), Some(1024)), SPLIT_CAP),
        Choice::Keep(_)
    ));
    assert_eq!(
        trick(&Domain::Ints(Some(0), None), SPLIT_CAP),
        Choice::Keep("an unbounded integer domain is infinite".into())
    );
    assert_eq!(
        trick(&Domain::Ints(Some(0), Some(5000)), SPLIT_CAP),
        Choice::Keep("the domain [0..=5000] is 5001 values, over 1024".into())
    );
    assert!(matches!(
        trick(&Domain::Type(Type::int()), SPLIT_CAP),
        Choice::Keep(_)
    ));
    assert!(matches!(
        trick(&Domain::Type(Type::string()), SPLIT_CAP),
        Choice::Keep(_)
    ));
}

#[test]
fn a_finite_type_lists_its_values() {
    assert_eq!(
        trick(&Domain::Type(Type::bool()), SPLIT_CAP),
        Choice::Split(vec![Value::Bool(false), Value::Bool(true)])
    );
    let tiers = &Type::atom("gold") | &Type::atom("basic");
    assert_eq!(
        trick(&Domain::Type(tiers.clone()), SPLIT_CAP),
        Choice::Split(vec![Value::atom("basic"), Value::atom("gold")])
    );
    // A tuple of finite parts is their product.
    let pair = Type::tuple(vec![Type::bool(), tiers]);
    assert_eq!(count(&trick(&Domain::Type(pair.clone()), SPLIT_CAP)), 4);
    assert_eq!(count(&trick(&Domain::Type(pair.clone()), 4)), 4);
    assert!(matches!(trick(&Domain::Type(pair), 3), Choice::Keep(_)));
    // A type with a payload atom or a function is not listed.
    let payload = Type::atom_with("e", &Type::tuple(vec![Type::int()]));
    assert!(matches!(
        trick(&Domain::Type(payload), SPLIT_CAP),
        Choice::Keep(_)
    ));
}

/// A pricing rule: the tier decides the rate, and each tier's copy has its branch cut.
const PRICE: &str = "rate = 8;\n\
    price(tier, n: int) = if tier == #gold { n * rate } else { n * (rate + 2) };\n";

#[test]
fn a_split_function_computes_what_the_function_does() {
    let u = elab(PRICE).unwrap();
    let tiers = Domain::Type(&Type::atom("gold") | &Type::atom("basic"));
    let (lam, report) = split(&u, "price", 0, &tiers, BUILD_FUEL).unwrap();
    assert!(report.left.is_empty(), "{:?}", report.left);
    // Each tier's arm has its branch cut and its rate computed; the general body is last.
    assert_eq!(
        lam.to_string(),
        "(tier, n) -> match tier { #basic -> (n * 10), #gold -> (n * 8), _ -> if (tier == \
         #gold) { (n * 8) } else { (n * 10) } }"
    );
    let mut staged = u.clone();
    staged
        .defs
        .iter_mut()
        .find(|d| d.name == "price")
        .unwrap()
        .term = lam;
    for tier in ["gold", "basic"] {
        for n in [0, 3, -7] {
            let call = |unit: &zedc::elab::Unit| {
                let f = unit.get("price").unwrap();
                let t = Term::App(
                    std::sync::Arc::new(f),
                    vec![Term::Lit(Value::atom(tier)), Term::Lit(Value::Int(n))],
                );
                Evaluator::new(World::new()).run(&with_prelude(t)).unwrap()
            };
            assert_eq!(call(&staged), call(&u), "{tier} {n}");
        }
    }
}

#[test]
fn the_trick_keeps_a_function_on_an_infinite_domain() {
    let u = elab(PRICE).unwrap();
    let err = split(&u, "price", 1, &Domain::Ints(None, None), BUILD_FUEL).unwrap_err();
    assert_eq!(err, "an unbounded integer domain is infinite");
}
