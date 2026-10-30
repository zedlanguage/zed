//! Loose atoms, the failure channel: `else` defaults them, the pattern form handles the one it
//! names, and they flow through the operators unchanged.

use crate::l01_16_elaboration::value;
use crate::l01_26_type_resolution::{sig, type_errors};

/// A lookup's result: a value, a missing row, or a stored NULL.
const LOOKUP: &str = "positional x: int | #notFound | #none";

#[test]
fn else_defaults_every_loose_atom() {
    let t = format!("f({LOOKUP}) = x else 0;\n");
    assert_eq!(sig(&t, "f"), "(int | #none | #notFound) -> int");
    let run = format!("{t}a = f(#none);\nb = f(#notFound);\nc = f(4);\n");
    assert_eq!(value(&run, "a"), "0");
    assert_eq!(value(&run, "b"), "0");
    assert_eq!(value(&run, "c"), "4");
}

#[test]
fn the_pattern_form_handles_the_atom_it_names_and_keeps_the_rest() {
    let t = format!("f({LOOKUP}) = x else #notFound -> -1;\n");
    assert_eq!(sig(&t, "f"), "(int | #none | #notFound) -> int | #none");
    let run = format!("{t}a = f(#none);\nb = f(#notFound);\nc = f(4);\n");
    assert_eq!(value(&run, "a"), "#none");
    assert_eq!(value(&run, "b"), "-1");
    assert_eq!(value(&run, "c"), "4");
    // Two patterns in turn handle both, and the result is the plain number.
    let both = format!("f({LOOKUP}) = (x else #notFound -> -1) else #none -> 0;\n");
    assert_eq!(sig(&both, "f"), "(int | #none | #notFound) -> int");
    // A pattern naming an atom the value cannot hold handles nothing.
    let other = format!("f({LOOKUP}) = x else #empty -> 0;\n");
    assert_eq!(
        sig(&other, "f"),
        "(int | #none | #notFound) -> int | #none | #notFound"
    );
}

#[test]
fn the_three_absences_stay_three_facts() {
    // Through an operator each absence flows unchanged, and two at once merge into `#errs`.
    assert_eq!(
        sig(
            "f(positional x: int | #notFound, positional y: int | #none) = x + y;\n",
            "f"
        ),
        "(int | #notFound, int | #none) -> int | #errs(_) | #none | #notFound"
    );
    let run = "f(positional x: int | #notFound, positional y: int | #none) = x + y;\n\
               a = f(#notFound, 1);\nb = f(1, #none);\nc = f(#notFound, #none);\n";
    assert_eq!(value(run, "a"), "#notFound");
    assert_eq!(value(run, "b"), "#none");
    assert_eq!(value(run, "c"), "#errs({#none, #notFound})");
}

#[test]
fn a_loose_atom_flows_through_safe_navigation() {
    let t = "f(positional x: int | #notFound) = x?.abs;\n";
    assert_eq!(sig(t, "f"), "(int | #notFound) -> int | #notFound");
    assert!(type_errors(t).is_empty());
    let run = format!("{t}a = f(#notFound);\nb = f(-3);\n");
    assert_eq!(value(&run, "a"), "#notFound");
    assert_eq!(value(&run, "b"), "3");
}

#[test]
fn a_declared_function_does_not_take_an_atom_its_type_omits() {
    assert_eq!(
        type_errors(
            "g(positional n: int) = n + 1;\n\
             f(positional x: int | #notFound) = g(x);\n"
        ),
        ["`g` does not take (#notFound) [g(x)]"]
    );
}
