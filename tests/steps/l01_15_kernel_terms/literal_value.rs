//! [`Term::literal_value`] (TUPLE-eq-lit): the value of a literal, or of a tuple built of
//! literals at any depth, and nothing for a term that holds anything else.

use zed_kernel::term::build::{lit, prim, var};
use zed_kernel::{Prim, Term, Value};

fn tuple(items: Vec<Term>) -> Term {
    prim(Prim::Tuple, items)
}

#[test]
fn a_tuple_of_literals_at_any_depth_has_the_value_of_its_literals() {
    assert_eq!(lit(3i64).literal_value(), Some(Value::Int(3)));
    assert_eq!(tuple(vec![]).literal_value(), Some(Value::tuple(vec![])));
    let flat = tuple(vec![lit(true), lit(false)]);
    assert_eq!(
        flat.literal_value(),
        Some(Value::tuple(vec![Value::Bool(true), Value::Bool(false)]))
    );
    // `((true, ()), 2, (false,))`: nested on the first, the last and an empty place.
    let nested = tuple(vec![
        tuple(vec![lit(true), tuple(vec![])]),
        lit(2i64),
        tuple(vec![lit(false)]),
    ]);
    let want = Value::tuple(vec![
        Value::tuple(vec![Value::Bool(true), Value::tuple(vec![])]),
        Value::Int(2),
        Value::tuple(vec![Value::Bool(false)]),
    ]);
    assert_eq!(nested.literal_value(), Some(want));
}

#[test]
fn a_tuple_holding_anything_but_a_literal_has_no_literal_value() {
    assert_eq!(var("x").literal_value(), None);
    assert_eq!(tuple(vec![lit(1i64), var("x")]).literal_value(), None);
    let deep = tuple(vec![lit(1i64), tuple(vec![tuple(vec![var("x")]), lit(2i64)])]);
    assert_eq!(deep.literal_value(), None);
    let neg = prim(Prim::Neg, vec![lit(1i64)]);
    assert_eq!(tuple(vec![neg]).literal_value(), None);
}

#[test]
fn a_tuple_of_literals_nested_deep_is_read_without_recursion() {
    // `((… (1,) …,),)` 2,000 deep: the read keeps its own stack, so the depth costs no frames.
    let n = 2_000;
    let t = (0..n).fold(lit(1i64), |t, _| tuple(vec![t]));
    let want = (0..n).fold(Value::Int(1), |v, _| Value::tuple(vec![v]));
    assert_eq!(t.literal_value(), Some(want));
}
