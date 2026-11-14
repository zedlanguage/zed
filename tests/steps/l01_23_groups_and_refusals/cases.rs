//! The spec's subtyping examples, and identities of the algebra that the representation does
//! not make structural, decided as type equality: subtyping both ways.

use zed_kernel::Value;
use zed_kernel::types::{Type, Universe};

fn lit(v: Value) -> Type {
    Type::lit(&v).unwrap()
}

fn ints(ns: &[i64]) -> Type {
    ns.iter()
        .fold(Type::empty(), |t, n| t | lit(Value::Int(*n)))
}

fn strs(ss: &[&str]) -> Type {
    ss.iter().fold(Type::empty(), |t, s| t | lit(Value::str(s)))
}

#[test]
fn morphism_variance() {
    let (int, string) = (Type::int(), Type::string());
    // sec:type_language: `{"a","b"} -> int <: String ->? int`.
    let ab = Type::exact(strs(&["a", "b"]), int.clone());
    assert!(ab.subtype(&Type::partial(string.clone(), int.clone())));
    // A wider exact domain is not a subtype of a narrower one, nor the reverse.
    let small = ints(&[0, 1, 2]);
    let whole = Type::exact(int.clone(), int.clone());
    let part = Type::exact(small.clone(), int.clone());
    assert!(!whole.subtype(&part));
    assert!(!part.subtype(&whole));
    // Both are partial maps over `int`; a partial map is neither.
    let partial = Type::partial(int.clone(), int.clone());
    assert!(whole.subtype(&partial) && part.subtype(&partial));
    assert!(!partial.subtype(&whole));
    // Covariant in the value type.
    let to_small = Type::exact(int.clone(), small.clone());
    assert!(to_small.subtype(&whole) && !whole.subtype(&to_small));
    // An empty guarantee in the supertype places no requirement.
    let g = Type::morphism(small.clone(), int.clone(), int.clone());
    assert!(g.subtype(&partial) && !partial.subtype(&g));
    // A guarantee wider than the permission admits no morphism.
    assert!(Type::morphism(int.clone(), small.clone(), int.clone()).is_empty());
    // A key promised with no value to give it admits none; with no key promised, the empty
    // morphism remains, and it is in every partial map type.
    assert!(Type::exact(small.clone(), Type::empty()).is_empty());
    let none = Type::partial(int.clone(), Type::empty());
    assert!(!none.is_empty());
    assert!(none.subtype(&Type::partial(string.clone(), string.clone())));
    assert!(!none.subtype(&Type::exact(string.clone(), string)));
    // Every morphism type is in the morphism universe.
    assert!(whole.subtype(&Type::universe(Universe::Morphism)));
    assert!(!Type::universe(Universe::Morphism).subtype(&whole));
}

#[test]
fn flow_narrowing_is_set_arithmetic() {
    // sec:type_language: the false branch of `v is T` is at `old \ T`.
    let old = Type::int() | Type::string() | Type::atom("none");
    assert!((&old - &Type::int()).equiv(&(Type::string() | Type::atom("none"))));
    assert!((&old & &Type::int()).equiv(&Type::int()));
    // Narrowing by a type outside `old` leaves it, and no value is in both.
    assert!((&old - &Type::bool()).equiv(&old));
    assert!((&old & &Type::bool()).is_empty());
}

#[test]
fn tuple_identities() {
    let (a, b, c, d) = (
        Type::int(),
        Type::string() | ints(&[0]),
        ints(&[0, 1]),
        Type::atom("a") | Type::string(),
    );
    let t = Type::tuple;
    // Distributivity: a union in a component is a union of tuples.
    let joined = t(vec![&a | &b, c.clone()]);
    let split = t(vec![a.clone(), c.clone()]) | t(vec![b.clone(), c.clone()]);
    assert_ne!(joined, split, "the two forms are not one representation");
    assert!(joined.equiv(&split));
    // Tuples meet componentwise.
    let met = t(vec![a.clone(), b.clone()]) & t(vec![c.clone(), d.clone()]);
    assert!(met.equiv(&t(vec![&a & &c, &b & &d])));
    // The complement of a pair, among pairs, is a pair with some component outside.
    let pairs = t(vec![Type::top(), Type::top()]);
    let outside = t(vec![!&a, Type::top()]) | t(vec![Type::top(), !&b]);
    assert!((&pairs - &t(vec![a.clone(), b.clone()])).equiv(&outside));
    // A pair is covered by two pairs that split it in one component, not by two that split it
    // in different components.
    let square = t(vec![c.clone(), c.clone()]);
    let rows = t(vec![ints(&[0]), c.clone()]) | t(vec![ints(&[1]), c.clone()]);
    assert!(square.subtype(&rows));
    let corners = t(vec![ints(&[0]), ints(&[0])]) | t(vec![ints(&[1]), ints(&[1])]);
    assert!(!square.subtype(&corners));
    // A tuple with an empty component is empty, and tuples of two lengths are disjoint.
    assert!(t(vec![a.clone(), &a & &Type::string()]).is_empty());
    assert!((t(vec![a.clone()]) & t(vec![a.clone(), a.clone()])).is_empty());
}

#[test]
fn boolean_identities() {
    let (a, b, c) = (
        Type::int() | Type::tuple(vec![Type::string()]),
        ints(&[0]) | Type::tuple(vec![Type::top()]) | Type::atom("x"),
        Type::tuple(vec![Type::int()]) | Type::bool(),
    );
    // De Morgan, distributivity, absorption and the difference as a meet.
    assert!((!(&a | &b)).equiv(&(!&a & !&b)));
    assert!((!(&a & &b)).equiv(&(!&a | !&b)));
    assert!((&a & &(&b | &c)).equiv(&((&a & &b) | (&a & &c))));
    assert!((&a | &(&b & &c)).equiv(&((&a | &b) & (&a | &c))));
    assert!((&a | &(&a & &b)).equiv(&a));
    assert!((&a - &b).equiv(&(&a & &!&b)));
    // Order: the meet is below each side, the join above, and `_` and the empty type are the
    // ends.
    assert!((&a & &b).subtype(&a) && a.subtype(&(&a | &b)));
    assert!(Type::empty().subtype(&a) && a.subtype(&Type::top()));
    assert!(!Type::top().subtype(&a) && !a.is_empty());
    assert!((&a & &!&a).is_empty());
}

#[test]
fn atom_payloads() {
    let t = Type::tuple;
    let p = Type::atom_with("p", &t(vec![Type::int()]));
    let q = Type::atom_with("p", &t(vec![ints(&[0])]));
    assert!(q.subtype(&p) && !p.subtype(&q));
    // An atom whose payload type is empty has no value, but its bare atom remains.
    assert!(Type::atom_with("p", &t(vec![Type::empty()])).is_empty());
    assert!(!(Type::atom("p") | Type::atom_with("p", &Type::empty())).is_empty());
    // Payloads of one name split as tuples do.
    let split = Type::atom_with("p", &t(vec![ints(&[0])]))
        | Type::atom_with("p", &t(vec![Type::int() - &ints(&[0])]));
    assert!(split.equiv(&p));
}
