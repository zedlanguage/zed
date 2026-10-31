//! The Trick: split a function on a parameter only when its domain is finite, and only on
//! the values of the domain the program's static calls pass it; the split function computes
//! what the function does.

use std::collections::BTreeSet;

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Term, Value, World};
use zedc::stage::{Choice, Domain, passed, split, trick};

use crate::l01_16_elaboration::{elab, with_prelude};

fn ints(vs: &[i64]) -> BTreeSet<Value> {
    vs.iter().copied().map(Value::Int).collect()
}

#[test]
fn a_finite_domain_is_split_on_the_values_passed_and_an_infinite_one_is_kept() {
    let d = Domain::Ints(Some(0), Some(256));
    assert_eq!(
        trick(&d, &ints(&[3, 300, 7, -1])),
        Choice::Split(vec![Value::Int(3), Value::Int(7)])
    );
    // No bound on the domain's size: only the values passed are split on.
    let wide = Domain::Ints(Some(0), Some(1 << 40));
    assert_eq!(
        trick(&wide, &ints(&[1 << 39])),
        Choice::Split(vec![Value::Int(1 << 39)])
    );
    assert_eq!(
        trick(&d, &ints(&[300])),
        Choice::Keep("no static call passes a value of the domain".into())
    );
    assert_eq!(
        trick(&Domain::Ints(Some(0), None), &ints(&[3])),
        Choice::Keep("an unbounded integer domain is infinite".into())
    );
    assert!(matches!(
        trick(&Domain::Type(Type::int()), &ints(&[3])),
        Choice::Keep(_)
    ));
    assert!(matches!(
        trick(&Domain::Type(Type::string()), &[Value::str("a")].into()),
        Choice::Keep(_)
    ));
}

#[test]
fn a_finite_type_is_split_on_its_members_passed() {
    let bools: BTreeSet<Value> = [Value::Bool(false), Value::Bool(true)].into();
    assert_eq!(
        trick(&Domain::Type(Type::bool()), &bools),
        Choice::Split(vec![Value::Bool(false), Value::Bool(true)])
    );
    let tiers = &Type::atom("gold") | &Type::atom("basic");
    let given: BTreeSet<Value> = [Value::atom("gold"), Value::atom("silver")].into();
    assert_eq!(
        trick(&Domain::Type(tiers.clone()), &given),
        Choice::Split(vec![Value::atom("gold")])
    );
    // A type with a payload atom or a function is not listed.
    let payload = Type::atom_with("e", &Type::tuple(vec![Type::int()]));
    assert!(matches!(
        trick(&Domain::Type(payload), &given),
        Choice::Keep(_)
    ));
}

/// A pricing rule: the tier decides the rate, and each tier's copy has its branch cut.
const PRICE: &str = "rate = 8;\n\
    price(tier, n: int) = if tier == #gold { n * rate } else { n * (rate + 2) };\n\
    total(m: int) = price(tier: #gold, n: m) + price(tier: #basic, n: 2 * m) + price(tier: #gold, n: 5);\n";

#[test]
fn a_split_function_computes_what_the_function_does() {
    let u = elab(PRICE).unwrap();
    let tiers = Domain::Type(&Type::atom("gold") | &Type::atom("basic"));
    let (lam, report) = split(&u, "price", 0, &tiers).unwrap();
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
fn the_values_passed_are_read_from_the_calls_once_mixed() {
    let u = elab(PRICE).unwrap();
    let tiers: BTreeSet<Value> = [Value::atom("basic"), Value::atom("gold")].into();
    assert_eq!(passed(&u, "price", 0), tiers);
    // `price(tier: #gold, n: 5)` is all build-stage, so the build computes it and leaves no
    // call; `n` is passed no other literal.
    assert_eq!(passed(&u, "price", 1), ints(&[]));
    // A call in a definition after mixing: `k` is a build-stage name.
    let u = elab("k = 2 + 2;\nf(x: int, y: int) = x + y;\nz(a: int) = f(x: k, y: a) + f(x: 4, y: a + 1) + f(x: a, y: a);\n").unwrap();
    assert_eq!(passed(&u, "f", 0), ints(&[4]));
    // One arm per value passed, however many calls pass it, and the general body last.
    let (lam, _) = split(&u, "f", 0, &Domain::Ints(Some(0), Some(1 << 40))).unwrap();
    let Term::Lam(_, body) = lam else { panic!() };
    let Term::Match(_, arms) = &*body else {
        panic!()
    };
    assert_eq!(arms.len(), 2);
}

#[test]
fn the_trick_keeps_a_function_on_an_infinite_domain() {
    let u = elab(PRICE).unwrap();
    let err = split(&u, "price", 1, &Domain::Ints(None, None)).unwrap_err();
    assert_eq!(err, "an unbounded integer domain is infinite");
}
