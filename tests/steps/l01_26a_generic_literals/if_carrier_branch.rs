//! FAIL-check-if-carrier-branch-literal-at-rat (found by TEST-complete-literals). DESIGN.md
//! L1.26a: "where one branch is a literal and the other has a carrier, the literal branch is
//! fixed as it would be alone, `int` where nothing fixes an integer literal, and the union rule
//! applies", with the test sentence "`h(if b { r } else { 0.1 })` with `h(positional z: rat)`
//! is `1r/10r` where `b` is false". The `if` was rejected at a `rat` use where its other
//! branch was a `rat` name bound to a literal or a `rat` literal: such a branch lists a number,
//! and only a branch that listed none was read at a carrier.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

fn values(src: &str, want: &[(&str, &str)]) {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    for (name, v) in want {
        assert_eq!(value(src, name), *v, "{src}\n`{name}`");
    }
}

fn rejected(src: &str) {
    assert!(!type_errors(src).is_empty(), "{src}");
}

const H: &str = "h(positional z: rat) = z;\nh64(positional z: f64) = z;\n";

#[test]
fn an_if_with_one_literal_branch_and_one_rat_branch_is_taken_at_rat() {
    // Controls, accepted before the fix: a `rat` parameter as the other branch, and two
    // literal branches.
    values(
        &format!("{H}g(positional y: rat) = h(if false {{ y }} else {{ 0.1 }});\na = g(1r);\n"),
        &[("a", "1r/10r")],
    );
    values(
        &format!("{H}a = h(if false {{ 1r }} else {{ 0.1r }});\n"),
        &[("a", "1r/10r")],
    );
    // Rejected before the fix.
    values(
        &format!(
            "{H}y = 1r;\na = h(if false {{ y }} else {{ 0.1 }});\nb = h(if true {{ y }} else {{ 0.1 }});\n"
        ),
        &[("a", "1r/10r"), ("b", "1r")],
    );
    values(
        &format!(
            "{H}y = 1r;\ng(positional c: bool) = h(if c {{ y }} else {{ 0.1 }});\na = g(false);\nb = g(true);\n"
        ),
        &[("a", "1r/10r"), ("b", "1r")],
    );
    values(
        &format!("{H}a = h(if false {{ 1r }} else {{ 1 }});\n"),
        &[("a", "1r")],
    );
    values(
        &format!(
            "{H}g(positional c: bool) = h(if c {{ 1r }} else {{ 2 }});\na = g(false);\nb = g(true);\n"
        ),
        &[("a", "2r"), ("b", "1r")],
    );
    values(
        "a = (if false { 1r } else { 0.1 }) + 1r;\n",
        &[("a", "11r/10r")],
    );
    // A nested `if`, and a float name beside an integer literal at its own carrier.
    values(
        &format!(
            "{H}y = 1r;\ng(positional c: bool, positional d: bool) = h(if c {{ y }} else {{ if d {{ 0.5 }} else {{ 3 }} }});\na = g(false, true);\nb = g(false, false);\n"
        ),
        &[("a", "1r/2r"), ("b", "3r")],
    );
    values(
        &format!(
            "{H}y = 0.5f64;\ng(positional c: bool) = h64(if c {{ y }} else {{ 1 }});\na = g(false);\nb = g(true);\n"
        ),
        &[("a", "1.0"), ("b", "0.5")],
    );
}

#[test]
fn a_branch_fixed_at_another_carrier_is_still_rejected() {
    // The condition is a parameter: `if false` drops its dead branch before the call is checked.
    let g = |name: &str, other: &str, lit: &str| {
        format!("g(positional c: bool) = {name}(if c {{ {other} }} else {{ {lit} }});\n")
    };
    // A name bound to an `int` is fixed at `int`; reading it at `rat` or `f64` would convert it.
    rejected(&format!("{H}y = 1;\n{}", g("h", "y", "0.1")));
    rejected(&format!("{H}y = 1;\n{}", g("h64", "y", "0.5")));
    // An `f64` name at `rat`, and a `rat` name or literal at `f64`, keep their carriers.
    rejected(&format!("{H}y = 0.5f64;\n{}", g("h", "y", "0.1")));
    rejected(&format!("{H}y = 1r;\n{}", g("h64", "y", "1")));
    rejected(&format!("{H}{}", g("h64", "1r", "1")));
    // A name alone is not read.
    rejected(&format!("{H}y = 1;\na = h(y);\n"));
    rejected(&format!("{H}y = 1;\na = h64(y);\n"));
}
