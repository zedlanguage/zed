//! The finite set of a product from its type (`store/product.rs`, the type facet of
//! `reduce_domains`; COMPLEXITY.md row S34). With no finite set yet, the values of a finite
//! type become the set. With a finite set already held, each member is kept only where the
//! type holds it, one membership test per member, and the type's values are not listed: a
//! name known to be one of three pairs keeps those pairs, although its type, a square of
//! literals, has many more values.

use std::collections::BTreeSet;
use std::sync::Arc;
use zed_kernel::Shared;

use zed_kernel::types::Type;
use zed_kernel::{Term, Value};
use zed_tests::scaling;
use zedc::store::lattice::FiniteSet;
use zedc::store::product::{Product, Scope};

fn int(i: usize) -> Value {
    Value::Int(i as i64)
}

fn pair(a: usize, b: usize) -> Value {
    Value::tuple(vec![int(a), int(b)])
}

/// The literals `0..n` as one type.
fn below(n: usize) -> Type {
    Type::union_all((0..n).map(|i| Type::lit(&int(i)).unwrap()))
}

/// The pairs of `0..n`: `n²` values.
fn square(n: usize) -> Type {
    Type::tuple(vec![below(n), below(n)])
}

/// The finite set of `p`, `None` for the top.
fn finite(p: &Product) -> Option<BTreeSet<Value>> {
    match &p.cell.finite.element {
        FiniteSet::Set(s) => Some(s.clone()),
        FiniteSet::Top => None,
    }
}

/// A name of type `ty` known to be one of `members`, bound in an empty scope, which reduces
/// its product; the product as the scope holds it.
fn bound(ty: &Type, members: &BTreeSet<Value>) -> Product {
    let mut p = Product::top();
    p.ty.element = ty.clone();
    p.cell.finite.element = FiniteSet::Set(members.clone());
    let mut s = Scope::new([]);
    let x: Arc<str> = "x".into();
    s.bind(&x, p, &Shared::new(Term::Lit(int(0))));
    s.get("x")
}

#[test]
fn a_finite_type_with_no_finite_set_gives_its_values() {
    // Three literals, one literal, none.
    let p = Product::of_type(below(3));
    assert_eq!(finite(&p), Some([int(0), int(1), int(2)].into()));
    let p = Product::of_type(below(1));
    assert_eq!(finite(&p), Some([int(0)].into()));
    // A type with no value has the empty set, and the product is empty.
    let p = Product::of_type(Type::empty());
    assert_eq!(finite(&p), Some(BTreeSet::new()));
    // Pairs, and a type of mixed universes: `true | false | 7 | (true, 1) | (false, 1)`.
    let p = Product::of_type(square(2));
    let want: BTreeSet<Value> = [pair(0, 0), pair(0, 1), pair(1, 0), pair(1, 1)].into();
    assert_eq!(finite(&p), Some(want));
    let mixed = &(&Type::bool() | &Type::lit(&int(7)).unwrap())
        | &Type::tuple(vec![Type::bool(), Type::lit(&int(1)).unwrap()]);
    let p = Product::of_type(mixed);
    assert_eq!(finite(&p).map(|s| s.len()), Some(5));
    // A type not known finite leaves the set at the top.
    assert_eq!(finite(&Product::of_type(Type::int())), None);
    assert_eq!(
        finite(&Product::of_type(Type::tuple(vec![
            Type::bool(),
            Type::int()
        ]))),
        None
    );
}

#[test]
fn a_finite_set_keeps_the_members_its_type_holds() {
    // A name of type `(0 | 1 | 2, 0 | 1 | 2)` known to be one of these values keeps the pairs
    // the type holds; `(0, 5)`, the pair of length three and the string go.
    let members: BTreeSet<Value> = [
        pair(0, 0),
        pair(2, 1),
        pair(0, 5),
        Value::tuple(vec![int(0), int(0), int(0)]),
        Value::Str("zero".into()),
    ]
    .into();
    let p = bound(&square(3), &members);
    assert_eq!(finite(&p), Some([pair(0, 0), pair(2, 1)].into()));
    assert!(p.contains(&pair(2, 1)));
    assert!(!p.contains(&pair(0, 5)));
    // One member the type holds stays the one value.
    let p = bound(&square(3), &[pair(1, 1)].into());
    assert_eq!(p.value(), Some(&pair(1, 1)));
    // No member the type holds: the set is empty and the product has no value.
    let p = bound(&square(3), &[pair(3, 3), Value::Bool(true)].into());
    assert_eq!(finite(&p), Some(BTreeSet::new()));
    // An empty set stays empty.
    let p = bound(&square(3), &BTreeSet::new());
    assert_eq!(finite(&p), Some(BTreeSet::new()));
    // A key path is held by the tuple type of its shape, as `Type::contains` and
    // `Product::contains` read it, so it stays, although `each_value` gives only tuples.
    let path = Value::path(vec![int(0), int(1)]);
    assert!(square(3).contains(&path));
    let p = bound(&square(3), &[path.clone()].into());
    assert_eq!(finite(&p), Some([path].into()));
    // A type not known finite leaves the set as it is, a member it does not hold included.
    let any_pair = Type::tuple(vec![Type::int(), Type::int()]);
    let p = bound(&any_pair, &[pair(0, 5), Value::Str("zero".into())].into());
    assert_eq!(
        finite(&p),
        Some([pair(0, 5), Value::Str("zero".into())].into())
    );
}

#[test]
fn a_finite_set_is_kept_against_a_type_with_more_values_than_can_be_listed() {
    // `t(0) = 0 | 1`, `t(i + 1) = (t(i), t(i))`: `t(48)` has 2^(2^48) values. A set of two
    // members, one in the type and one not, is narrowed by testing the two.
    let t = |d: usize| (0..d).fold(below(2), |t, _| Type::tuple(vec![t.clone(), t]));
    let first = t(48).each_value().unwrap().next().unwrap();
    let outside = Value::tuple(vec![first.clone(), int(0)]);
    let p = bound(&t(48), &[first.clone(), outside].into());
    assert_eq!(finite(&p), Some([first].into()));
}

#[test]
fn keeping_a_finite_set_against_its_type_scales_with_the_set() {
    // A set of `n` pairs `(i, i)` against the square of `0..n`, which has `n²` values: one
    // membership test per member, of order `n log n` with the set's own order. Listing the
    // type's values is of order `n²`.
    let built: std::collections::HashMap<usize, (Type, BTreeSet<Value>)> = [200, 1600]
        .into_iter()
        .map(|n| (n, (square(n), (0..n).map(|i| pair(i, i)).collect())))
        .collect();
    scaling::check_order(
        "a finite set of n pairs against a square of n literals",
        200,
        1,
        |n| {
            let (ty, members) = &built[&n];
            assert_eq!(finite(&bound(ty, members)).map(|s| s.len()), Some(n));
        },
    );
}

#[test]
fn the_values_of_a_finite_type_become_its_set_in_their_number() {
    // `(0 | … | n - 1, 0)` has `n` values, all of which the set holds.
    let built: std::collections::HashMap<usize, Type> = [200, 1600]
        .into_iter()
        .map(|n| (n, Type::tuple(vec![below(n), below(1)])))
        .collect();
    scaling::check_order(
        "the n values of a finite type made a finite set",
        200,
        1,
        |n| {
            let p = Product::of_type(built[&n].clone());
            assert_eq!(finite(&p).map(|s| s.len()), Some(n));
        },
    );
}
