//! Meets of morphism types as the printer writes them (`Printer::folded`, `Printer::meet_text`
//! and `Printer::meet_of_literals` in `zed-kernel` `types/print.rs`): one case for each way
//! `meet_text` ends, and a meet joined to a part that is no meet of literals.

use zed_kernel::Value;
use zed_kernel::types::{Refusal, Type, Verdict};

fn lit(i: i64) -> Type {
    Type::lit(&Value::Int(i)).unwrap()
}

/// `lower .. upper -> value`.
fn arrow(lower: Type, upper: Type, value: Type) -> Type {
    Type::morphism(lower, upper, value)
}

/// `_ ->? value`, any domain.
fn any(value: Type) -> Type {
    arrow(Type::empty(), Type::top(), value)
}

fn printed(t: &Type) -> String {
    t.surface().to_string()
}

#[test]
fn a_meet_of_morphism_types_is_written_as_one_arrow_where_the_kernel_decides_its_bounds() {
    let (int, b, never) = (Type::int(), Type::bool(), Type::empty());
    let one = lit(1);
    // The lower bound `int | bool` lies outside the upper bound `int & bool`: no domain lies
    // between them, and the meet is empty.
    let exact =
        &arrow(int.clone(), int.clone(), one.clone()) & &arrow(b.clone(), b.clone(), one.clone());
    assert_eq!(printed(&exact), "Never");
    // Bounds `Never .. _`, both named by a literal, and the upper not within the lower: both
    // bounds are written, and the value `int & bool` is empty.
    assert_eq!(
        printed(&(&any(int.clone()) & &any(b.clone()))),
        "_ ->? Never"
    );
    // The upper bound `_ & int` is within the lower bound `int`: one type, written once.
    let one_set = &arrow(int.clone(), Type::top(), one.clone())
        & &arrow(never.clone(), int.clone(), one.clone());
    assert_eq!(printed(&one_set), "int -> 1");
    // The value `(1 | 2) & (2 | 3)`, which is `2`, holds no other type, so it can close no
    // cycle of texts: one arrow (row FAIL-print-meet-unnamed-bound).
    let unnamed = &any(&lit(1) | &lit(2)) & &any(&lit(2) | &lit(3));
    assert_eq!(printed(&unnamed), "_ ->? 2");
    // The lower bound `int | bool` is named by no literal but holds no other type, and the
    // upper bound `_` is not within it: one arrow, both bounds written.
    let lower_unnamed =
        &arrow(int.clone(), Type::top(), one.clone()) & &arrow(b.clone(), Type::top(), one.clone());
    assert_eq!(printed(&lower_unnamed), "(int | bool) .. _ -> 1");
    // A meet of four literals whose upper bound `int & bool` is empty and within the lower
    // bound `Never`: one list, written as one arrow.
    let four = &(&any(lit(1)) & &arrow(never.clone(), int.clone(), lit(1)))
        & &(&any(&lit(1) | &lit(2)) & &arrow(never.clone(), b.clone(), lit(1)));
    assert_eq!(printed(&four), "Never ->? 1");
}

/// A meet of literals met with an exclusive or of two others is an `&` node whose second
/// operand is no meet of literals (`meet_of_literals` false of it): the node is written with
/// its connective, the meet in it folded to one arrow.
#[test]
fn a_meet_joined_to_an_exclusive_or_keeps_its_connective() {
    let (int, b, never) = (Type::int(), Type::bool(), Type::empty());
    let meet = &arrow(never.clone(), int, lit(1)) & &arrow(never, b, lit(1));
    let x = |p: &Type, q: &Type| &(p - q) | &(q - p);
    let t = &meet & &x(&any(lit(2)), &any(lit(3)));
    assert_eq!(
        printed(&t),
        r"(Never ->? 1) & (((_ ->? 2) \ (_ ->? 3)) | ((_ ->? 3) \ (_ ->? 2)))"
    );
}

/// Bounds the kernel refuses to compare, the random 3-CNF of `refusal_cost`: `meet_text` gives
/// up, and the meet is written with its connective, not as `a .. b -> int`.
#[test]
fn a_meet_whose_bounds_are_refused_keeps_its_connective() {
    let (a, b) = super::refusal_cost::r3(16, 7);
    Type::forget_emptiness();
    assert_eq!(
        a.subtype_verdict(&b),
        Verdict::Refused(Refusal::SharedCells(0))
    );
    let int = Type::int();
    let t = &arrow(a, Type::top(), int.clone()) & &arrow(Type::empty(), b, int);
    let text = printed(&t);
    assert!(text.contains(" -> int) & ("), "{text}");
}
