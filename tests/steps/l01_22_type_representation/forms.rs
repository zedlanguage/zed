//! The printed forms of types: the universes, the scalar part's finite and cofinite sets,
//! tuple clauses, atoms and morphism bounds.

use zed_kernel::Value;
use zed_kernel::types::{Type, Universe};

fn s(t: &Type) -> String {
    t.to_string()
}

#[test]
fn the_extremes_and_the_base_types() {
    assert_eq!(s(&Type::top()), "_");
    assert_eq!(s(&Type::empty()), "(|)");
    assert_eq!(s(&(Type::int() | Type::string())), "(| int String)");
    assert_eq!(s(&(Type::int() & Type::string())), "(|)");
    let three = Type::lit(&Value::Int(3)).unwrap();
    assert_eq!(s(&(Type::int() - &three)), "(\\ int 3)");
    assert_eq!(
        s(&(three.clone() | Type::lit(&Value::Int(1)).unwrap())),
        "(| 1 3)"
    );
    assert_eq!(s(&(Type::int() - &(Type::int() - &three))), "3");
    assert_eq!(s(&Type::lit(&Value::Bool(true)).unwrap()), "true");
    assert_eq!(
        s(&(Type::bool() - &Type::lit(&Value::Bool(true)).unwrap())),
        "false"
    );
}

#[test]
fn complement_is_taken_within_each_universe() {
    // `!int` keeps every other scalar and every tuple, struct and morphism.
    assert_eq!(
        s(&!Type::int()),
        "(| bool rat f64 String #_ tuple struct morphism)"
    );
    let not_int = !Type::int();
    assert!(not_int.contains(&Value::Tuple(vec![Value::Int(1)])));
    assert!(not_int.contains(&Value::str("1")));
    assert!(not_int.functions());
    assert!(!not_int.contains(&Value::Int(1)));
    for u in [
        Universe::Scalar,
        Universe::Tuple,
        Universe::Struct,
        Universe::Morphism,
    ] {
        assert_eq!(Type::universe(u).part(u), Type::universe(u));
    }
    let all = [
        Universe::Scalar,
        Universe::Tuple,
        Universe::Struct,
        Universe::Morphism,
    ]
    .map(Type::universe)
    .into_iter()
    .fold(Type::empty(), |a, b| a | b);
    assert_eq!(all, Type::top());
}

#[test]
fn atoms_are_scalars_named_one_by_one() {
    let (a, b) = (Type::atom("a"), Type::atom("b"));
    assert_eq!(s(&(&a | &b)), "(| #a #b)");
    let atoms = Type::universe(Universe::Scalar)
        - &(Type::bool() | Type::int() | Type::rat() | Type::f64() | Type::string());
    assert_eq!(s(&atoms), "#_");
    assert_eq!(s(&(&atoms - &a)), "(\\ #_ #a)");
    let pair = Type::tuple(vec![Type::int(), Type::string()]);
    let with = Type::atom_with("ioError", &pair);
    assert_eq!(s(&with), "(#ioError (tuple int String))");
    assert!(with.contains(&Value::atom_with(
        "ioError",
        vec![Value::Int(2), Value::str("disk")]
    )));
    assert!(!with.contains(&Value::atom("ioError")));
    // A payload is a tuple or a struct: a scalar payload type contributes nothing.
    assert_eq!(Type::atom_with("a", &Type::int()), Type::empty());
}

#[test]
fn tuples_meet_componentwise_and_lengths_are_disjoint() {
    let p = |a: Type, b: Type| Type::tuple(vec![a, b]);
    let num = Type::int() | Type::f64();
    assert_eq!(
        p(num.clone(), Type::top()) & p(Type::int(), Type::string()),
        p(Type::int(), Type::string())
    );
    assert_eq!(
        p(Type::int(), Type::top()) & Type::tuple(vec![Type::top()]),
        Type::empty()
    );
    assert_eq!(
        p(Type::int(), Type::string()) & p(Type::string(), Type::top()),
        Type::empty()
    );
    assert_eq!(s(&Type::tuple(vec![])), "(tuple)");
    assert_eq!(
        s(&(Type::universe(Universe::Tuple) - &p(Type::int(), Type::int()))),
        "(& tuple (! (tuple int int)))"
    );
    // `(X & t) | (X & !t)` is `X`.
    let t = p(Type::int(), Type::int());
    let x = Type::tuple(vec![Type::bool()]);
    let tuples = Type::universe(Universe::Tuple);
    assert_eq!((&x - &t) | (&x & &t), Type::tuple(vec![Type::bool()]));
    assert_eq!((&tuples - &t) | t.clone(), tuples);
    // Two clauses merge only when the rest of them is equal: `(t & !u) | !t` is `!u` only
    // because `u` is within `t`, and `t | (u & !t)` is `t | u`.
    let tup = |v: Value| Value::Tuple(vec![v]);
    let one = Type::tuple(vec![Type::lit(&Value::Int(1)).unwrap()]);
    let (t, u) = (
        Type::tuple(vec![Type::int()]),
        Type::tuple(vec![Type::string()]),
    );
    for y in [(&t - &one) | (&tuples - &t), (&tuples - &t) | (&t - &one)] {
        assert!(!y.contains(&tup(Value::Int(1))), "{y}");
        assert!(y.contains(&tup(Value::Int(2))) && y.contains(&tup(Value::str("a"))));
    }
    // Both orders of the two clauses, which reach the two cases of the merge.
    for y in [&t | &(&u - &t), &u | &(&t - &u)] {
        assert!(y.contains(&tup(Value::Int(1))) && y.contains(&tup(Value::str("a"))));
        assert!(!y.contains(&tup(Value::Bool(true))), "{y}");
    }
}

#[test]
fn morphism_types_carry_two_domain_bounds() {
    let (k, v) = (Type::int(), Type::string());
    assert_eq!(s(&Type::exact(k.clone(), v.clone())), "(-> int String)");
    assert_eq!(s(&Type::partial(k.clone(), v.clone())), "(->? int String)");
    let ab = Type::atom("a") | Type::atom("b");
    assert_eq!(
        s(&Type::morphism(Type::atom("a"), ab, v.clone())),
        "(-> #a (| #a #b) String)"
    );
    // A run-time test can decide membership in every morphism or none, and in nothing
    // between.
    let f = Type::exact(k, v);
    assert!(!f.decidable());
    assert!(!(Type::int() | f.clone()).decidable());
    assert!(!Type::tuple(vec![f.clone()]).decidable());
    assert!((&f | &!&f).decidable() && (&f | &!&f).functions());
    assert!((&f & &!&f).decidable() && !(&f & &!&f).functions());
    assert!(Type::universe(Universe::Morphism).functions());
}
