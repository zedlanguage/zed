//! The menus of DESIGN.md sec:diagnostics, "A `/` of integer literals" and "The value a fix
//! names", and the values its fixes give: each expected text is that of DESIGN.md, cited by
//! section and passage above it (item SPEC-no-verbatim: the spec is not copied here). An
//! operation on literals alone at the top level takes the carrier of what it meets, so one
//! literal with a carrier is enough, and the menu writes the carrier at the first literal of
//! the value, or at the decimal it rejects.

use super::fixes::{checked, pairs};
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// The first sentence of the one rejection of `src`, without the ` [text]` the helper adds and
/// without the menu.
fn first(src: &str) -> String {
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{src}: {errors:?}");
    let message = errors[0].rsplit_once(" [").unwrap().0;
    message.lines().next().unwrap().to_string()
}

#[test]
fn one_carrier_reaches_both_sides_of_a_division() {
    // DESIGN.md sec:diagnostics, "A `/` of integer literals": "in `q = (1.0f64 + 2) / (3 + 4)`
    // the `2` takes `f64` from `1.0f64`, so `1.0f64 + 2` is an `f64`; `/` takes two operands of
    // one carrier, so `3 + 4`, which meets only the `/`, takes `f64` too. Neither side is typed
    // on its own as an `int` before it meets the `/` [...] So `q = (1 + 2) / (3.0f64 + 4)`
    // checks the same way and gives the same value, and so does
    // `q = (1.0f64 + 2) / (3.0f64 + 4)`". Step L1.26b: "`q = (f64(1) + 2) / (3 + 4)` [...] are
    // `0.42857142857142855`; `q = (1r + 2) / (3 + 4)` is `3r/7r`".
    for src in [
        "q = (1.0f64 + 2) / (3 + 4);\n",
        "q = (1 + 2) / (3.0f64 + 4);\n",
        "q = (1.0f64 + 2) / (3.0f64 + 4);\n",
        "q = (f64(1) + 2) / (3 + 4);\n",
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "q"), "0.42857142857142855", "{src}");
    }
    assert_eq!(value("q = (1r + 2) / (3 + 4);\n", "q"), "3r/7r");
    // Step L1.26b: "`y = 0.5f64 * (1 + 2)` is `1.5`".
    assert_eq!(value("y = 0.5f64 * (1 + 2);\n", "y"), "1.5");
    assert_eq!(value("y = (1 + 2) * 0.5f64;\n", "y"), "1.5");
    // A carrier from a name reaches the operation as one from a literal does.
    assert_eq!(value("x = 1.5f64;\ny = x * (1 + 2);\n", "y"), "4.5");
    assert_eq!(value("x = 1r;\ny = (1 + 2) / (x + 6);\n", "y"), "3r/7r");
    // Deeper operations on literals alone, either side, and a comparison.
    assert_eq!(
        value("y = ((1 + 2) * (3 - 4)) / (2.0f64 * (1 + 1));\n", "y"),
        "-0.75"
    );
    assert_eq!(value("y = -(1 + 2) * 0.5f64;\n", "y"), "-1.5");
    assert_eq!(value("y = (1 + 2) < 0.5f64;\n", "y"), "false");
    assert_eq!(value("y = (1 + 2) == 3.0f64;\n", "y"), "true");
    assert_eq!(value("y = (1 + 2) == 3r;\n", "y"), "true");
}

#[test]
fn where_nothing_gives_a_carrier_an_operation_on_literals_stays_an_int() {
    // "an operation on literals alone is an `int` only where nothing at all gives it a
    // carrier": with no carrier anywhere it is an `int`, and a `/` of such operations is
    // rejected.
    assert_eq!(value("y = (1 + 2) * 3;\n", "y"), "9");
    assert_eq!(value("y = (1 + 2) < (3 - 4);\n", "y"), "false");
    assert_eq!(type_errors("q = (1 + 2) / (3 + 4);\n").len(), 1);
    // A literal that is no `f64` exactly is rejected where the operation takes `f64`.
    let errors = type_errors("y = (9007199254740993 + 1) * 0.5f64;\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("9007199254740993"), "{errors:?}");
}

#[test]
fn a_division_of_operations_on_integer_literals_writes_one_carrier() {
    // DESIGN.md sec:diagnostics, "A `/` of integer literals": "the menu writes the carrier at
    // the first literal of the value"; the message's first line and its three fixes that write a
    // literal are those of the passage's `text` fence.
    //
    // The two fixes that declare a type, `q: f64 = ...` and `q: rat = ...`, are in
    // `fixes_declare_a_type`, deferred to plan row LIT-menu-design-gaps in
    // wt/scratch/deferred-tests/LIT-menu-design-gaps.rs.
    let src = "q = (1 + 2) / (3 + 4);\n";
    assert_eq!(
        first(src),
        "Nothing gives the integer literals a carrier, and `/` has none at `int`: `q = (1 + 2) / \
         (3 + 4)`. Try `q = (1.0f64 + 2) / (3 + 4)` instead."
    );
    assert_eq!(
        checked(src),
        pairs(&[
            ("q = (1.0f64 + 2) / (3 + 4);", "q is 0.42857142857142855"),
            ("q = (1r + 2) / (3 + 4);", "q is 3r/7r"),
            ("q = (f64(1) + 2) / (3 + 4);", "q is 0.42857142857142855"),
        ])
    );
}

#[test]
fn a_decimal_before_an_operation_on_literals_takes_the_carrier() {
    // Step L1.26b: "`y = 0.5f64 * (1 + 2)` is `1.5`": the suffix on the decimal reaches `1 + 2`,
    // so the fix writes it there, and the binder's value is an operation on literals alone, so
    // the fix names it ("The value a fix names": "In `y = 2.5 + 1`, by contrast, the binder's
    // value is an operation on literals alone, and the same fixes read
    // `y = 2.5f64 + 1;    y is 3.5` and `y = 2.5r + 1;    y is 7r/2r`").
    assert_eq!(
        checked("y = 0.5 * (1 + 2);\n"),
        pairs(&[
            ("y = 0.5f64 * (1 + 2);", "y is 1.5"),
            ("y = 0.5r * (1 + 2);", "y is 3r/2r"),
        ])
    );
    assert_eq!(
        checked("y = (1 + 2) * 0.5;\n"),
        pairs(&[
            ("y = (1 + 2) * 0.5f64;", "y is 1.5"),
            ("y = (1 + 2) * 0.5r;", "y is 3r/2r"),
        ])
    );
    assert_eq!(
        checked("y = 2.5 + 1;\n"),
        pairs(&[
            ("y = 2.5f64 + 1;", "y is 3.5"),
            ("y = 2.5r + 1;", "y is 7r/2r")
        ])
    );
    assert_eq!(
        checked("y = (1 + 2) < 0.5;\n"),
        pairs(&[
            ("y = (1 + 2) < 0.5f64;", "y is false"),
            ("y = (1 + 2) < 0.5r;", "y is false"),
        ])
    );
}

#[test]
fn a_comparison_of_literal_tuples_names_the_binder() {
    // DESIGN.md sec:diagnostics, "The value a fix names": "Where the binder's value is the
    // literal, or an operation on literals alone, the checker works that value out by
    // arithmetic on the numbers the program writes, and names it with the binder: [...]
    // `y is true` for `y = 1 == 1.0f64`." A comparison of two tuples of literals is such a
    // value: each pair of components takes one carrier.
    assert_eq!(
        checked("y = (1, (2, 3)) == (1.0, (2r, 3));\n"),
        pairs(&[
            ("y = (1, (2, 3)) == (1.0f64, (2r, 3));", "y is true"),
            ("y = (1, (2, 3)) == (1.0r, (2r, 3));", "y is true"),
        ])
    );
    assert_eq!(
        checked("y = (1, (2, 3)) != (1.0, (2r, 4));\n"),
        pairs(&[
            ("y = (1, (2, 3)) != (1.0f64, (2r, 4));", "y is true"),
            ("y = (1, (2, 3)) != (1.0r, (2r, 4));", "y is true"),
        ])
    );
    assert_eq!(
        checked("y = (0.5, 1) == (1.0f64, 0.5);\n"),
        pairs(&[
            ("y = (0.5, 1) == (1.0f64, 0.5f64);", "y is false"),
            ("y = (0.5, 1) == (1.0f64, 0.5r);", "y is false"),
        ])
    );
    // A pair of operations on integer literals stays an `int`.
    assert_eq!(
        checked("y = (0.5, 1 + 1) == (1.0, 2 * 1);\n"),
        pairs(&[
            ("y = (0.5f64, 1 + 1) == (1.0, 2 * 1);", "y is false"),
            ("y = (0.5r, 1 + 1) == (1.0, 2 * 1);", "y is false"),
        ])
    );
    // The scalar comparison of the passage.
    assert_eq!(
        checked("y = 1 == 1.0;\n"),
        pairs(&[
            ("y = 1 == 1.0f64;", "y is true"),
            ("y = 1 == 1.0r;", "y is true")
        ])
    );
}

#[test]
fn a_cast_of_a_decimal_names_the_literal() {
    // `f64(0.5)`: a cast fixes no carrier for its argument, so the bare decimal is rejected.
    // The binder's value is a call, of the prelude's `f64`, so by "The value a fix names" the
    // fix names the literal ("Where the literal stands anywhere else, as an argument of a call
    // [...] the fix names the value the literal itself then is").
    assert_eq!(
        checked("y = f64(0.5);\n"),
        pairs(&[
            ("y = f64(0.5f64);", "the literal is then the f64 0.5"),
            ("y = f64(0.5r);", "the literal is then exactly 0.5, a rat"),
        ])
    );
    assert_eq!(value("y = f64(0.5r);\n", "y"), "0.5");
    // DESIGN.md sec:domains: "A cast `f64(9007199254740993r)` is never offered [...] since the
    // integer has no exact `f64`, so the cast gives `#inexact` for its one input and is
    // rejected as an operation that always fails". `0.1r` has no exact `f64` either, so
    // `f64(0.1r)` is not offered; at `rat` each fix casts exactly.
    assert_eq!(
        checked("y = f64(0.1);\n"),
        pairs(&[("y = f64(0.1f64);", "the literal is then the f64 0.1")])
    );
    assert_eq!(
        checked("y = f64(-0.1);\n"),
        pairs(&[("y = f64(-0.1f64);", "the literal is then the f64 -0.1")])
    );
    assert_eq!(
        checked("y = rat(0.1);\n"),
        pairs(&[
            ("y = rat(0.1f64);", "the literal is then the f64 0.1"),
            ("y = rat(0.1r);", "the literal is then exactly 0.1, a rat"),
        ])
    );
    assert_eq!(value("y = rat(0.1r);\n", "y"), "1r/10r");
}
