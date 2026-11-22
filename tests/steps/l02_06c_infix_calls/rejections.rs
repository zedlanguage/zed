//! An arithmetic operator written without parentheses in an operand of an infix call is
//! rejected where the text has two readings (DESIGN.md tier 6, the row "Arithmetic operator
//! written without parentheses in an operand of an infix call"): at the right edge of the left
//! operand, a binary operator or a prefix `-` or `!`; at the left edge of the right operand, a
//! binary operator. Each rejection names the operator, writes both readings and the call each
//! is, and offers both as repairs. A qualified name between the tildes is rejected with the
//! call written out.

use zed_tests::step_helpers::l01_10_lambdas_types_else_tuples::sx;

use crate::front;

/// The unit with `x = <e>;` on its line 2, after a function `plus` on line 1.
fn rejected(e: &str) -> String {
    front(&format!(
        "plus(positional a: int, positional b: int) = a + b;\nx = {e};\n"
    ))
}

/// The rejection of `x = <e>;` is placed at `at` on line 2, names `op`, and repairs to `first`
/// and `second`, where `first` is offered in the headline; the first note gives the calls.
fn two_readings(e: &str, at: usize, op: &str, first: &str, second: &str, calls: &str) {
    assert_eq!(
        rejected(e),
        format!(
            "2:{at} Infix call next to `{op}`: `{e}`. Try `{first}` instead.\
             ; the two readings give different calls: {calls}\
             ; repair: `{first}`; repair: `{second}`"
        ),
        "{e}"
    );
}

#[test]
fn a_binary_operator_opening_the_right_operand() {
    two_readings(
        "3 ~plus~ 4 * 2",
        16,
        "*",
        "(3 ~plus~ 4) * 2",
        "3 ~plus~ (4 * 2)",
        "`(3 ~plus~ 4) * 2` is `plus(3, 4) * 2`, and `3 ~plus~ (4 * 2)` is `plus(3, 4 * 2)`",
    );
    two_readings(
        "2 ~plus~ 3 div 2",
        16,
        "div",
        "(2 ~plus~ 3) div 2",
        "2 ~plus~ (3 div 2)",
        "`(2 ~plus~ 3) div 2` is `plus(2, 3) div 2`, and `2 ~plus~ (3 div 2)` is \
         `plus(2, 3 div 2)`",
    );
    // The operator next to the call is the innermost one on the edge: `*`, not `+`.
    two_readings(
        "2 ~plus~ 3 * 4 + 1",
        16,
        "*",
        "(2 ~plus~ 3) * 4 + 1",
        "2 ~plus~ (3 * 4 + 1)",
        "`(2 ~plus~ 3) * 4 + 1` is `plus(2, 3) * 4 + 1`, and `2 ~plus~ (3 * 4 + 1)` is \
         `plus(2, 3 * 4 + 1)`",
    );
    // A prefix operator before the binary one is part of the right operand in both readings.
    two_readings(
        "2 ~plus~ -3^2",
        16,
        "^",
        "(2 ~plus~ -3)^2",
        "2 ~plus~ (-3^2)",
        "`(2 ~plus~ -3)^2` is `plus(2, -3)^2`, and `2 ~plus~ (-3^2)` is `plus(2, -3^2)`",
    );
}

#[test]
fn an_operator_closing_the_left_operand() {
    two_readings(
        "1 + 2 ~plus~ 4",
        7,
        "+",
        "(1 + 2) ~plus~ 4",
        "1 + (2 ~plus~ 4)",
        "`(1 + 2) ~plus~ 4` is `plus(1 + 2, 4)`, and `1 + (2 ~plus~ 4)` is `1 + plus(2, 4)`",
    );
    two_readings(
        "2^3 ~plus~ 1",
        6,
        "^",
        "(2^3) ~plus~ 1",
        "2^(3 ~plus~ 1)",
        "`(2^3) ~plus~ 1` is `plus(2^3, 1)`, and `2^(3 ~plus~ 1)` is `2^plus(3, 1)`",
    );
    two_readings(
        "-3 ~plus~ 4",
        5,
        "-",
        "(-3) ~plus~ 4",
        "-(3 ~plus~ 4)",
        "`(-3) ~plus~ 4` is `plus(-3, 4)`, and `-(3 ~plus~ 4)` is `-plus(3, 4)`",
    );
    two_readings(
        "1 + -2 ~plus~ 3",
        9,
        "-",
        "(1 + -2) ~plus~ 3",
        "1 + -(2 ~plus~ 3)",
        "`(1 + -2) ~plus~ 3` is `plus(1 + -2, 3)`, and `1 + -(2 ~plus~ 3)` is \
         `1 + -plus(2, 3)`",
    );
    let not = sx("!p ~f~ q");
    assert!(
        not.starts_with("error: Infix call next to `!`: `!p ~f~ q`. Try `(!p) ~f~ q` instead."),
        "{not}"
    );
}

/// Each operand form of the module comment, as an expression, and the call the rejection
/// names: in a chain, the one the operator is next to.
#[test]
fn every_edge() {
    for (e, op, call) in [
        ("p ~scale~ k * 2", "*", "p ~scale~ k * 2"),
        ("p ~f~ k / 2", "/", "p ~f~ k / 2"),
        ("p ~f~ k mod 2", "mod", "p ~f~ k mod 2"),
        ("p ~f~ k + 2", "+", "p ~f~ k + 2"),
        ("p ~f~ k - 2", "-", "p ~f~ k - 2"),
        ("p ~f~ k ++ q", "++", "p ~f~ k ++ q"),
        ("p ~f~ k^2", "^", "p ~f~ k^2"),
        ("p ~f~ -k^2", "^", "p ~f~ -k^2"),
        ("a + b ~f~ c", "+", "a + b ~f~ c"),
        ("a * b ~f~ c", "*", "a * b ~f~ c"),
        ("-p ~plus~ v", "-", "-p ~plus~ v"),
        ("!p ~f~ q", "!", "!p ~f~ q"),
        ("a ~f~ b ~g~ c * 2", "*", "a ~f~ b ~g~ c * 2"),
        ("a ~f~ b * 2 ~g~ c", "*", "a ~f~ b * 2"),
    ] {
        let got = sx(e);
        assert!(
            got.starts_with(&format!("error: Infix call next to `{op}`: `{call}`.")),
            "{e}: {got}"
        );
    }
}

/// Each form of the grammar below tier 6 at an operand's inner edge (the proof at
/// `two_readings`, plan row PROOF-infix-edge-walk): a suffix, a call, an index, a member, a
/// tuple, a block-ended `if` or `match`, an annotation that runs to the end of the right operand,
/// give one reading; an operator over such a form still gives two.
#[test]
fn each_form_at_an_inner_edge() {
    for e in [
        "p.q ~f~ r[0]",
        "g(a) ~f~ (b, c)",
        "p::len ~f~ q?.r",
        "if t { a } else { b } ~f~ if t { a } else { b }",
        "match t { 1 -> a, _ -> b } ~f~ k",
    ] {
        let got = sx(e);
        assert!(got.starts_with('('), "{e}: {got}");
    }
    for (e, op) in [
        ("p ~f~ if t { a } else { b } + 2", "+"),
        ("g(a) * 2 ~f~ k", "*"),
        ("p ~f~ r[0] ^ 2", "^"),
    ] {
        let got = sx(e);
        assert!(
            got.starts_with(&format!("error: Infix call next to `{op}`")),
            "{e}: {got}"
        );
    }
}

/// Parentheses take the second reading away, on either side.
#[test]
fn parentheses_leave_one_reading() {
    for e in [
        "(p ~scale~ k) * 2",
        "p ~scale~ (k * 2)",
        "(a + b) ~f~ c",
        "a + (b ~f~ c)",
        "(-p) ~plus~ v",
        "-(p ~plus~ v)",
        "p ~f~ (-k^2)",
        "(a^b) ~f~ c",
        "p ~scale~ -1",
        "p ~f~ !q",
        "p ~f~ -(-1)",
    ] {
        let got = sx(e);
        assert!(got.starts_with('('), "{e}: {got}");
    }
}

#[test]
fn a_qualified_name() {
    assert_eq!(
        rejected("3 ~geometry.plus~ 4"),
        "2:7 Qualified name in an infix call: `3 ~geometry.plus~ 4`. Try \
         `geometry.plus(3, 4)` instead.; an infix call names its function by a plain name; a \
         qualified function is called in the ordinary way; repair: `geometry.plus(3, 4)`"
    );
}
