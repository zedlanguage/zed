//! The finite set of a product from its type (`store/product.rs`, the type facet of
//! `reduce_domains`; COMPLEXITY.md row S34). With no finite set yet, the values of a finite
//! type become the set only when the type writes them as a list (`Type::values_listed`):
//! literals such as `1 | 2 | 3`, and tuple types each component of which is one value, such
//! as `(true, false) | (false, true)`. A named finite type, a tuple type with a component of
//! two or more values such as `(bool, bool)` or `t(48)`, stays a type: the finite set stays
//! the top, and the type answers each question about the name. With a finite set already
//! held, each member is kept only where the type holds it, one membership test per member,
//! and the type's values are not listed: a name known to be one of three pairs keeps those
//! pairs, although its type, a square of literals, has many more values.

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

/// The type of the one value `v`, a tuple written as the tuple of its components' types.
fn lit(v: &Value) -> Type {
    match v {
        Value::Tuple(xs) => Type::tuple(xs.iter().map(lit).collect()),
        _ => Type::lit(v).unwrap(),
    }
}

/// `t(0) = 0 | 1`, `t(i + 1) = (t(i), t(i))`: `2^(2^d)` values, `d + 1` distinct types.
fn t(d: usize) -> Type {
    (0..d).fold(below(2), |t, _| Type::tuple(vec![t.clone(), t]))
}

/// The tuple `(b_0, …, b_{k - 1})` of `k` bools, whose type has `2^k` values.
fn bools(k: usize) -> Type {
    Type::tuple(vec![Type::bool(); k])
}

#[test]
fn a_type_written_as_a_list_gives_its_values() {
    // Three literals, one literal, none.
    let p = Product::of_type(below(3));
    assert_eq!(finite(&p), Some([int(0), int(1), int(2)].into()));
    let p = Product::of_type(below(1));
    assert_eq!(finite(&p), Some([int(0)].into()));
    assert_eq!(p.value(), Some(&int(0)));
    // A type with no value has the empty set, and the product is empty.
    let p = Product::of_type(Type::empty());
    assert_eq!(finite(&p), Some(BTreeSet::new()));
    assert!(p.is_empty());
    // Written tuples of bools, `(true, false) | (false, true)`: one value per tuple written.
    let tf = Value::tuple(vec![Value::Bool(true), Value::Bool(false)]);
    let ft = Value::tuple(vec![Value::Bool(false), Value::Bool(true)]);
    let p = Product::of_type(&lit(&tf) | &lit(&ft));
    assert_eq!(finite(&p), Some([tf.clone(), ft.clone()].into()));
    // A tuple nested in a tuple, `(1, (#a, 2))`, is one value too, and fixes the name.
    let nested = Value::tuple(vec![int(1), Value::tuple(vec![Value::atom("a"), int(2)])]);
    let p = Product::of_type(lit(&nested));
    assert_eq!(p.value(), Some(&nested));
    // A type of mixed universes, all listed: `true | false | 7 | (true, 1) | (false, 1)`, the
    // last two written one by one.
    let mixed = &(&Type::bool() | &lit(&int(7)))
        | &(&lit(&Value::tuple(vec![Value::Bool(true), int(1)]))
            | &lit(&Value::tuple(vec![Value::Bool(false), int(1)])));
    let p = Product::of_type(mixed);
    assert_eq!(finite(&p).map(|s| s.len()), Some(5));
    // `bool` is the list `true | false`: the type does not keep whether it was named.
    let p = Product::of_type(Type::bool());
    assert_eq!(
        finite(&p),
        Some([Value::Bool(false), Value::Bool(true)].into())
    );
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
fn a_named_finite_type_stays_a_type() {
    // `(bool, bool)`, `(0 | 1, 0)` and the square of `0 | 1 | 2` are products: each has a
    // component of two or more values, so none is listed, and the set stays the top.
    for ty in [bools(2), Type::tuple(vec![below(2), below(1)]), square(3)] {
        let p = Product::of_type(ty.clone());
        assert_eq!(finite(&p), None, "{ty}");
        // The type answers membership: `(0, 0)` is a value of each, `(5, 5)` of none.
        let zero = match ty == bools(2) {
            true => Value::tuple(vec![Value::Bool(false), Value::Bool(false)]),
            false => pair(0, 0),
        };
        assert!(p.contains(&zero), "{ty}");
        assert!(!p.contains(&pair(5, 5)), "{ty}");
        assert!(!p.is_empty());
    }
    // A type mixing a written tuple with a product lists nothing: the product is not a list.
    let p = Product::of_type(&lit(&pair(7, 7)) | &square(2));
    assert_eq!(finite(&p), None);
    // One value written as a product, `(0 | 1, 0) - (1, 0)`, is not seen to be one value: the
    // name is not taken as static (the tradeoff at `reduce_domains`), though the type holds
    // exactly `(0, 0)`.
    let one = &Type::tuple(vec![below(2), below(1)]) - &lit(&pair(1, 0));
    let p = Product::of_type(one);
    assert!(p.contains(&pair(0, 0)));
    assert!(!p.contains(&pair(1, 0)));
    assert_eq!(p.value(), None);
}

#[test]
fn a_named_type_of_two_to_the_64_values_is_not_listed() {
    // A tuple of 64 bools, and `t(6)`, each with 2^64 values.
    for ty in [bools(64), t(6)] {
        let p = Product::of_type(ty.clone());
        assert_eq!(finite(&p), None);
        assert!(!p.is_empty());
        let first = ty.each_value().unwrap().next().unwrap();
        assert!(p.contains(&first));
    }
    // `t(48)`, with 2^(2^48) values, ends as quickly.
    assert_eq!(finite(&Product::of_type(t(48))), None);
}

#[test]
fn a_named_finite_type_reduces_in_time_linear_in_its_form() {
    // `t(d)` is written as `d + 1` types; the reduction reads each once. Listing its values,
    // `2^(2^d)` of them, does not end for `d` past 5.
    let built = scaling::inputs(200, t);
    scaling::check(
        "the reduction of a name of type t(d), d + 1 types written",
        200,
        |d| {
            assert_eq!(finite(&Product::of_type(built[&d].clone())), None);
        },
    );
}

#[test]
fn the_values_of_a_type_written_as_a_list_become_its_set_in_their_number() {
    // `(0, 0) | (1, 0) | … | (n - 1, 0)`: `n` tuples written, all of which the set holds.
    let built = scaling::inputs(200, |n| Type::union_all((0..n).map(|i| lit(&pair(i, 0)))));
    scaling::check(
        "the n values of n written tuples made a finite set",
        200,
        |n| {
            let p = Product::of_type(built[&n].clone());
            assert_eq!(finite(&p).map(|s| s.len()), Some(n));
        },
    );
}

#[test]
fn a_fact_on_a_listed_type_narrows_its_list_and_a_named_type_answers_from_the_type() {
    use zed_kernel::Prim;
    use zed_kernel::term::build::{lit as term, prim, var};
    let tf = Value::tuple(vec![Value::Bool(true), Value::Bool(false)]);
    let ft = Value::tuple(vec![Value::Bool(false), Value::Bool(true)]);
    let scope = |ty: Type, fact: Term| {
        Scope::new([("x".into(), Product::of_type(ty))]).assume(&fact, true, &Default::default())
    };
    let ne = prim(Prim::Ne, vec![var("x"), term(tf.clone())]);
    let eq = prim(Prim::Eq, vec![var("x"), term(tf.clone())]);
    // `x: (true, false) | (false, true)` with `x != (true, false)`: the list keeps `(false, true)`
    // alone, and `x` is static.
    let s = scope(&lit(&tf) | &lit(&ft), ne.clone());
    assert_eq!(s.get("x").value(), Some(&ft));
    // `x: (bool, bool)` with `x == (true, false)`: the equality gives the value.
    let s = scope(bools(2), eq);
    assert_eq!(s.get("x").value(), Some(&tf));
    // `x: (bool, bool)` with `x != (true, false)`: three values remain, none listed; `x` is
    // not static, and is not empty.
    let s = scope(bools(2), ne);
    assert!(!s.bottom);
    assert_eq!(s.get("x").value(), None);
    assert!(s.get("x").contains(&ft));
    // `x == (true, false)` after it is not reached: once `x` is fixed, the scope finds it
    // empty.
    let s2 = s.assume(
        &prim(Prim::Eq, vec![var("x"), term(tf.clone())]),
        true,
        &Default::default(),
    );
    assert!(s2.bottom);
    // The other three values excluded in turn too: the type cannot take a tuple out, since a key
    // path of its shape is in the tuple type and differs from it, and no list is held, so the
    // scope is not found empty (the tradeoff at `reduce_domains`). With the type's values
    // listed it was.
    let all = [(true, true), (false, true), (false, false)]
        .map(|(a, b)| Value::tuple(vec![Value::Bool(a), Value::Bool(b)]));
    let s3 = all.iter().fold(s, |s, v| {
        s.assume(
            &prim(Prim::Ne, vec![var("x"), term(v.clone())]),
            true,
            &Default::default(),
        )
    });
    assert!(!s3.bottom);
    // `x: (true, false) | (false, true)` with `x == (true, true)`: no listed value is left.
    let tt = Value::tuple(vec![Value::Bool(true), Value::Bool(true)]);
    let s = scope(
        &lit(&tf) | &lit(&ft),
        prim(Prim::Eq, vec![var("x"), term(tt)]),
    );
    assert!(s.bottom);
}

#[test]
fn a_program_on_a_tuple_of_bools_is_accepted_and_its_arms_read_the_type() {
    use zedc::store::product::arms;
    let src = "ok = (x) -> if x == (true, false) { 1 } else { 2 };";
    if let Err(ds) = &*zedc::query::Db::new().front(src) {
        panic!("{src}: rejected: {ds:?}");
    }
    let (_, body) = zed_tests::step_helpers::l01_25_preimage_catalog::function(src);
    let ft = Value::tuple(vec![Value::Bool(false), Value::Bool(true)]);
    let tt = Value::tuple(vec![Value::Bool(true), Value::Bool(true)]);
    let of = |ty: Type| arms(&body, &Scope::new([("x".into(), Product::of_type(ty))]));
    // The program writes `(true, false)` as a tuple built of two literals, which the equality
    // with a literal (`Scope::assume`) does not read, so neither arm narrows `x` (a gap of its
    // own, follow-up TUPLE-eq-lit). `x: (bool, bool)`, a named type: both arms are reached,
    // and `x` keeps its type and no list, whatever the number of its values.
    let a = of(bools(2));
    for outcome in [true, false] {
        let arm = super::arm(&a, "==", outcome);
        assert!(arm.reachable());
        let x = arm.scope.get("x");
        assert_eq!(finite(&x), None);
        assert!(x.contains(&tt) && !x.is_empty());
    }
    // `x: (true, true) | (false, true)`, written as a list: each arm keeps the two values.
    let a = of(&lit(&tt) | &lit(&ft));
    for outcome in [true, false] {
        let x = super::arm(&a, "==", outcome).scope.get("x");
        assert_eq!(finite(&x), Some([ft.clone(), tt.clone()].into()));
    }
}
