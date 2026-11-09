//! Loose atoms, the failure channel: `else` defaults them, the pattern form handles the one it
//! names, and they flow through the operators unchanged.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

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
        "(int | #notFound, int | #none) -> int | #none | #notFound | #errs(#none | #notFound ->? #none | #notFound)"
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
fn a_loose_atom_passes_through_a_declared_function_whose_type_omits_it() {
    // Rule 6: the atom selects no arrow of `g` and is the call's value; `g`'s body never sees it.
    let t = "g(positional n: int) = n + 1;\n\
             f(positional x: int | #notFound) = g(x);\n";
    assert!(type_errors(t).is_empty());
    assert_eq!(sig(t, "f"), "(int | #notFound) -> int | #notFound");
    let run = format!("{t}a = f(#notFound);\nb = f(2);\n");
    assert_eq!(value(&run, "a"), "#notFound");
    assert_eq!(value(&run, "b"), "3");
}

#[test]
fn a_loose_atom_passes_through_a_generic_function_bounded_to_carriers() {
    // Rule 6 at an inferred parameter: `add` is `(T, T) -> T for T in int | f64 | rat`, a
    // bound that holds no atom, so `#nf` selects no arrow and is the call's value.
    let t = "add(positional a, positional b) = a + b;\n\
             h(positional y: int | #nf) = add(y, 1);\n";
    assert!(type_errors(t).is_empty());
    assert_eq!(sig(t, "h"), "(int | #nf) -> int | #nf");
    let run = format!("{t}a = h(#nf);\nb = h(2);\n");
    assert_eq!(value(&run, "a"), "#nf");
    assert_eq!(value(&run, "b"), "3");
}

#[test]
fn a_call_takes_the_arrow_of_a_generic_function_that_takes_its_atoms() {
    // `r` handles the atoms of `x` and lets them reach its result, so it has two arrows; the
    // first, whose `T` is bounded to carriers, takes no atom, and a call passing `#nf` takes
    // the second.
    let t = "r(positional x, positional d) = if (x else d) == d { d } else { x + d };\n\
             h(positional y: int | #nf) = r(y, 1);\n";
    assert!(type_errors(t).is_empty());
    assert_eq!(
        sig(t, "r"),
        "((T, T) -> T) & ((#_ | T, T) -> #_ | T) for T in int | f64 | rat"
    );
    assert_eq!(sig(t, "h"), "(int | #nf) -> int | #_");
    let run = format!("{t}a = h(#nf);\nb = h(2);\n");
    assert_eq!(value(&run, "a"), "1");
    assert_eq!(value(&run, "b"), "3");
}

#[test]
fn a_loose_atom_enters_a_parameter_whose_bound_may_take_other_values() {
    // `k`'s parameter may take other values, so its type `_` holds every atom (DESIGN.md
    // L1.26) and `#nf` is not passed by: it enters `k`, whose need `size(a)` refuses it.
    let t = "size(positional v: int | (int, int)) = 1;\n\
             k(positional a) = (size(a), a);\n";
    let bad = format!("{t}h(positional y: int | #nf) = k(y);\n");
    assert_eq!(
        type_errors(&bad),
        [
            "`k` does not take (int | #nf): these are the types of its arguments here, and `k` has no arrow that takes them all [k(y)]",
            "`size` does not take #nf, which is not int | (int, int): `size` takes only values of int | (int, int) [k(y)]"
        ]
    );
    let ok = format!("{t}h(positional y: int) = k(y);\nb = h(2);\n");
    assert!(type_errors(&ok).is_empty());
    assert_eq!(value(&ok, "b"), "(1, 2)");
}

#[test]
fn a_loose_atom_enters_the_first_arrow_at_a_parameter_that_may_take_other_values() {
    // `x`'s atoms reach the result, so `r` has two arrows; `v` may take other values, so in
    // both arrows its type holds every atom and `#nf` enters it, where `size` refuses it. The
    // first arrow takes the call, as its other parameter takes the plain `1`.
    let t = "size(positional v: int | (int, int)) = 1;\n\
             r(positional x, positional v) = if (x else 0) == 0 { size(v) } else { x + size(v) };\n";
    assert_eq!(
        sig(t, "r"),
        "((int, _) -> int) & ((int | #_, _) -> int | #_)"
    );
    let bad = format!("{t}h(positional y: int | #nf) = r(1, y);\n");
    assert_eq!(
        type_errors(&bad),
        [
            "`r` does not take (1, int | #nf): these are the types of its arguments here, and `r` has no arrow that takes them all [r(1, y)]",
            "`size` does not take #nf, which is not int | (int, int): `size` takes only values of int | (int, int) [r(1, y)]"
        ]
    );
    let ok = format!("{t}h(positional y: int | #nf) = r(y, 2);\na = h(#nf);\nb = h(2);\n");
    assert!(type_errors(&ok).is_empty());
    assert_eq!(value(&ok, "a"), "1");
    assert_eq!(value(&ok, "b"), "3");
}

/// Item PRINT-fmt-audit: the repair that tests the value with `is` writes the parameter's type
/// as `is` reads it, a function type in parentheses. Before, it was
/// `if v is (int) -> int { … }`, which reads as `(v is (int)) -> int`.
#[test]
fn the_is_repair_writes_a_function_type_in_parentheses() {
    let t = "ap(positional g: (int) -> int) = g(1);\n";
    let bad = format!("{t}k(positional a) = (ap(a), a);\nh(positional y: int | #nf) = k(y);\n");
    let out = match zedc::run::load(bad.as_bytes()) {
        Ok(_) => panic!("accepted:\n{bad}"),
        Err(e) => e,
    };
    assert!(
        out.contains(
            "repair: test the value with `is` first, as `if v is ((int) -> int) { … }`, or \
             handle the values that are not (int) -> int with `else` or `match`"
        ),
        "{out}"
    );
    assert!(
        out.contains("repair: pass `ap` a value of (int) -> int"),
        "{out}"
    );
    // The repair, applied, is accepted, and the type it names reads back as written.
    let ok = format!(
        "{t}k(positional a) = if a is ((int) -> int) {{ ap(a) }} else {{ 0 }};\n\
         h(positional y: int | #nf) = k(y);\n"
    );
    assert!(type_errors(&ok).is_empty(), "{:?}", type_errors(&ok));
    let back = zedc::check::read::parse_type("(int) -> int").unwrap();
    assert_eq!(back.to_string(), "(int) -> int");
}
