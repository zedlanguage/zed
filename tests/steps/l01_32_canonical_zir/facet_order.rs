//! The order facets are sorted by. The canonicalizer sorts an edge's facets once and drops a
//! facet equal to the one before it, so its normal form is unique only if a facet value's
//! [`Ord`] is a total order whose ties are exactly [`PartialEq`]: two values the order ties
//! but `==` tells apart would both stay, in whichever order the sort left them. These tests
//! check that on every kind of value a facet can hold, numbers at the ends of their widths and
//! in each form an exact number can take, and that two equal values give one address.

use std::cmp::Ordering;
use std::sync::Arc;

use num_bigint::{BigInt, BigUint};
use zed_kernel::types::Type;
use zed_kernel::{Family, Rat, Text, Value};
use zedc::canon::Facet;
use zedc::zir::canon::address;
use zedc::zir::{Edge, Region, RegionKind, Src};

/// `2^e` as an integer, written out.
fn two_to(e: u32) -> BigInt {
    BigInt::from(2).pow(e)
}

/// `2^e` kept as a power of 2, as `2 ^ e` evaluates.
fn two_pow(e: u32) -> Rat {
    Rat::int(BigInt::from(2))
        .pow(&BigUint::from(e))
        .expect("2^e is kept as a power")
}

/// One value of each kind and form, with values that are equal built more than one way.
fn values() -> Vec<Value> {
    let rat = |n: i64, d: i64| Value::rat(Rat::new(n.into(), d.into()).expect("d is not 0"));
    let one = Rat::int(BigInt::from(1));
    let mut vs = vec![
        Value::Bool(false),
        Value::Bool(true),
        // Integers, at the ends of the 64-bit range and past them, written out and kept as
        // powers of 2.
        Value::Int(0),
        Value::Int(-1),
        Value::Int(1),
        Value::Int(i64::MIN),
        Value::Int(i64::MAX),
        Value::int(BigInt::from(i64::MAX) + 1),
        Value::int(BigInt::from(i64::MIN) - 1),
        Value::int(two_to(100)),
        Value::integer(two_pow(100)),
        Value::int(-two_to(100)),
        Value::integer(two_pow(100).neg()),
        Value::int(two_to(64)),
        Value::integer(two_pow(64)),
        // Rationals: equal values reduced, kept as powers, and from a decimal literal.
        rat(1, 3),
        rat(2, 6),
        rat(1, 2),
        Value::rat(Rat::decimal("0.5").unwrap().expect("a decimal")),
        Value::rat(Rat::decimal("5e-1").unwrap().expect("a decimal")),
        rat(-1, 2),
        Value::rat(Rat::int(BigInt::from(3))),
        Value::rat(Rat::new(BigInt::from(1), two_to(100)).expect("2^100 is not 0")),
        Value::rat(one.div(&two_pow(100)).unwrap().expect("2^100 is not 0")),
        Value::rat(Rat::decimal("1e-30").unwrap().expect("a decimal")),
        Value::rat(Rat::new(BigInt::from(1), BigInt::from(10).pow(30)).expect("10^30 is not 0")),
        // Floats: both zeros, both infinities, NaN by two bit patterns, the ends of the
        // range, and a float equal in value to an integer and a rational.
        Value::float(0.0),
        Value::float(-0.0),
        Value::float(f64::INFINITY),
        Value::float(f64::NEG_INFINITY),
        Value::float(f64::NAN),
        Value::float(f64::from_bits(f64::NAN.to_bits() ^ 1)),
        Value::float(-f64::NAN),
        Value::float(f64::MAX),
        Value::float(f64::MIN),
        Value::float(f64::MIN_POSITIVE),
        Value::float(5e-324),
        Value::float(1.0),
        Value::float(0.5),
        Value::float(2f64.powi(100)),
        // Strings, written out and joined.
        Value::str(""),
        Value::str("m"),
        Value::str("ms"),
        Value::str("é"),
        Value::Str(Text::join(&"m".into(), &"s".into()).expect("a short string")),
        // Atoms: bare, with a tuple payload, with a struct payload whose fields are written
        // in either order.
        Value::atom("none"),
        Value::atom("some"),
        Value::atom_with("some", vec![Value::Int(1)]),
        Value::atom_with("some", vec![Value::float(1.0)]),
        Value::atom_with("some", vec![Value::float(-0.0)]),
        Value::atom_with("some", vec![Value::float(0.0)]),
        named(&[("code", Value::Int(3)), ("why", Value::str("disk"))]),
        named(&[("why", Value::str("disk")), ("code", Value::Int(3))]),
        named(&[("code", Value::Int(4)), ("why", Value::str("disk"))]),
        named(&[("code", Value::Int(3))]),
        // Tuples and keypaths, with a float inside, and one tuple shared.
        Value::tuple(Vec::new()),
        Value::tuple(vec![Value::Int(1), Value::float(-0.0)]),
        Value::tuple(vec![Value::Int(1), Value::float(0.0)]),
        Value::tuple(vec![Value::Int(1), Value::float(f64::NAN)]),
        Value::tuple(vec![Value::Int(1), Value::str("ms")]),
        Value::tuple(vec![Value::tuple(vec![Value::Int(1)]), Value::Int(2)]),
        Value::path(vec![Value::str("ann"), Value::Int(2)]),
        Value::path(vec![Value::str("ann")]),
        // Families: built in either order, by union, nested, and with a float value.
        Value::Family(Family::new()),
        Value::Family(Family::of([(1_i64, "a"), (2, "b")])),
        Value::Family(Family::of([(2_i64, "b"), (1, "a")])),
        Value::Family(
            Family::of([(1_i64, "a")])
                .union(&Family::of([(2_i64, "b")]))
                .expect("disjoint keys"),
        ),
        Value::Family(Family::of([(1_i64, "a")])),
        Value::Family(Family::of([(1_i64, "b")])),
        Value::Family(Family::of([(1_i64, Value::float(-0.0))])),
        Value::Family(Family::of([(1_i64, Value::float(0.0))])),
        Value::Family(Family::of([(
            1_i64,
            Value::Family(Family::of([(2_i64, "c")])),
        )])),
        Value::Family(Family::set([Value::str("m"), Value::str("s")])),
    ];
    // Copies that share their parts with the original.
    let shared: Vec<Value> = vs
        .iter()
        .filter(|v| matches!(v, Value::Tuple(_) | Value::Family(_) | Value::Atom(_)))
        .cloned()
        .collect();
    vs.extend(shared);
    vs
}

/// `#err(…)` with the fields `fields`, in the order given.
fn named(fields: &[(&str, Value)]) -> Value {
    let fields = fields.iter().map(|(k, v)| (Arc::from(*k), v.clone()));
    Value::atom_named("err", fields.collect()).expect("distinct field names")
}

#[test]
fn the_order_ties_exactly_the_equal_values() {
    let vs = values();
    let mut ties = 0;
    for a in &vs {
        for b in &vs {
            let o = a.cmp(b);
            assert_eq!(o == Ordering::Equal, a == b, "{a:?} against {b:?}: {o:?}");
            assert_eq!(b.cmp(a), o.reverse(), "{a:?} against {b:?}");
            assert_eq!(a.partial_cmp(b), Some(o), "{a:?} against {b:?}");
            ties += usize::from(o == Ordering::Equal);
        }
    }
    // Each value ties itself and its shared copy, and the values built more than one way tie
    // the other ways: so the list holds such pairs, and the test is not of distinct values only.
    assert!(ties > 2 * vs.len(), "{ties} ties among {} values", vs.len());
}

#[test]
fn values_equal_in_value_but_not_in_kind_or_bits_stay_apart() {
    let int = Value::Int(3);
    let rat = Value::rat(Rat::int(BigInt::from(3)));
    let float = Value::float(3.0);
    assert!(int < rat && rat < float);
    assert_ne!(Value::float(-0.0), Value::float(0.0));
    assert!(Value::float(-0.0) < Value::float(0.0));
    assert!(Value::Int(0) < Value::float(-0.0));
    // Every NaN is the one canonical NaN, after `+inf`.
    assert_eq!(Value::float(-f64::NAN), Value::float(f64::NAN));
    assert!(Value::float(f64::INFINITY) < Value::float(f64::NAN));
    // An integer kept as a power of 2 is the integer written out.
    assert_eq!(Value::integer(two_pow(100)), Value::int(two_to(100)));
    assert_eq!(
        Value::integer(two_pow(100)).cmp(&Value::int(two_to(100))),
        Ordering::Equal
    );
}

#[test]
fn the_order_is_transitive() {
    let vs = values();
    // Every triple, not a sample: the list is short enough.
    for a in &vs {
        for b in &vs {
            if a > b {
                continue;
            }
            for c in &vs {
                if b <= c {
                    assert!(a <= c, "{a:?} <= {b:?} <= {c:?}, but not {a:?} <= {c:?}");
                }
            }
        }
    }
    // A sort agrees with the pairwise order.
    let mut sorted = vs.clone();
    sorted.sort();
    assert!(sorted.windows(2).all(|w| w[0] <= w[1]));
}

/// A function region whose one argument is an `int` with the facets `facets`.
fn with_facets(facets: Vec<Facet>) -> Region {
    let mut arg = Edge::value(Type::int());
    if let Edge::Value(v) = &mut arg {
        v.facets = facets;
    }
    Region {
        kind: RegionKind::Function,
        args: vec![arg],
        nodes: Vec::new(),
        results: vec![Src::Arg(0)],
    }
}

/// A facet of kind `units` with the value `v`.
fn units(v: &Value) -> Facet {
    Facet {
        hint: false,
        kind: "units".into(),
        value: v.clone(),
    }
}

#[test]
fn equal_facet_values_give_one_address_and_different_ones_two() {
    let vs = values();
    for a in &vs {
        for b in &vs {
            let (one, two) = (with_facets(vec![units(a)]), with_facets(vec![units(b)]));
            assert_eq!(
                address(&one).expect("memory for the address")
                    == address(&two).expect("memory for the address"),
                a == b,
                "{a:?} against {b:?}"
            );
            // Two equal facets are one, whichever the sort leaves first.
            let both = with_facets(vec![units(a), units(b)]);
            assert_eq!(
                address(&both).expect("memory for the address")
                    == address(&one).expect("memory for the address"),
                a == b,
                "{a:?} against {b:?}"
            );
        }
    }
}
