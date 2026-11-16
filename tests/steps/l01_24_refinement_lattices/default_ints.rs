//! Row TEST-default-ints-from-calls: a call that leaves out a ranged parameter is accepted
//! when the ints the checker records for its default all lie in the range (row
//! RANGE-default-in-range). That is sound only if the recorded ints hold every value the
//! default can take. Each default here is built from a call of a function with a known
//! result range, from an `if` and from names, once inside the parameter's range and once
//! partly outside it; a default whose value lies outside the range must never be accepted.
//! A `match` is not compiled at this step (row TEST-default-ints-match).

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

/// `h` gives `y + 1` for `y` in `0..=3`, so its result lies in `1..=4`.
const H: &str = "h(y: int[0..=3]) = y + 1;\n";

/// The program with `g(x: <param> = <default>) = x;` and a call `r = g();` that leaves `x`
/// out.
fn program(param: &str, default: &str) -> String {
    format!("{H}g(x: {param} = {default}) = x;\nr = g();\n")
}

/// The call is accepted, and the value it gives, the default, lies in `lo..=hi`.
fn accepted(param: &str, default: &str, lo: i128, hi: i128) {
    let text = program(param, default);
    assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    let r: i128 = value(&text, "r")
        .parse()
        .unwrap_or_else(|_| panic!("{text}"));
    assert!((lo..=hi).contains(&r), "{text}\nr = {r}");
}

/// The call is refused as one that leaves out `x`.
fn refused(param: &str, default: &str) {
    let text = program(param, default);
    let errors = type_errors(&text);
    assert!(
        errors.iter().any(|e| e.contains("`g()` leaves out `x`")),
        "{text}\n{errors:#?}"
    );
}

#[test]
fn a_default_from_a_call_with_a_known_result_range() {
    // `h(y: 2)` is 3, and `h`'s result lies in 1..=4, inside 0..=9.
    accepted("int[0..=9]", "h(y: 2)", 0, 9);
    // `h(y: 2)` is 3, outside 0..=2; `h`'s result range 1..=4 is partly outside it.
    refused("int[0..=2]", "h(y: 2)");
    // `h(y: 0)` is 1, inside 0..=2, but the checker reads the call by `h`'s range alone, which
    // is partly outside: the call is refused as one it cannot show in the range.
    refused("int[0..=2]", "h(y: 0)");
}

#[test]
fn a_default_from_an_if() {
    accepted("int[0..=3]", "if true { 1 } else { 2 }", 0, 3);
    // The value is 5, outside 0..=3.
    refused("int[0..=3]", "if false { 1 } else { 5 }");
    // The value is 1, inside, but the other branch is outside.
    refused("int[0..=3]", "if true { 1 } else { 5 }");
    // Branches that are calls of `h`: 1..=4 in all.
    accepted("int[0..=4]", "if true { h(y: 0) } else { h(y: 3) }", 0, 4);
    refused("int[0..=3]", "if false { h(y: 0) } else { h(y: 3) }");
}

/// A default that reads names: another parameter declared with a range, which each call
/// passes in that range; a top-level binder, which has one value; and a parameter with no
/// range, which may be any int.
#[test]
fn a_default_that_reads_names() {
    let two = |head: &str, call: &str| format!("{H}{head} = x;\nr = {call};\n");
    for (text, want) in [
        (two("g(y: int[0..=3], x: int[0..=3] = y)", "g(y: 2)"), "2"),
        (
            two("g(y: int[0..=3], x: int[1..=4] = h(y: y))", "g(y: 3)"),
            "4",
        ),
        (two("n = 2;\ng(x: int[0..=3] = n)", "g()"), "2"),
    ] {
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        assert_eq!(value(&text, "r"), want, "{text}");
    }
    for text in [
        // `y` may be 3, outside 0..=2.
        two("g(y: int[0..=3], x: int[0..=2] = y)", "g(y: 1)"),
        // `y` has no range, so it may be any int.
        two("g(y: int, x: int[0..=3] = y)", "g(y: 1)"),
        // `n` is 5.
        two("n = 5;\ng(x: int[0..=3] = n)", "g()"),
    ] {
        let errors = type_errors(&text);
        assert!(
            errors.iter().any(|e| e.contains("leaves out `x`")),
            "{text}\n{errors:#?}"
        );
    }
}

/// A `match` is compiled from step L2.4; until then a default that is one is refused for the
/// `match` itself, so no call reads it. Row TEST-default-ints-match holds the tests of a
/// default from a `match`, inside and partly outside the range, for when it is compiled.
#[test]
fn a_default_from_a_match_is_not_compiled_yet() {
    let text = program("int[0..=3]", "match 2 { 2 -> 1, _ -> 3 }");
    let stmts = zed_tests::deep::statements(&text);
    let errors = zedc::resolve::resolve(&stmts).expect_err(&text);
    assert!(
        errors
            .iter()
            .any(|e| e.message.contains("a `match` is part of the Zed language")),
        "{text}\n{errors:#?}"
    );
}
