//! Step L6.6b, the placement of `break;`: it ends the innermost `loop` or `for` whose body
//! holds it, at any depth of that body, in a nested block, a branch of an `if` or an arm of a
//! `match` (DESIGN.md sec:generations, "`break;`", and the table of sec:grammar: "legal
//! anywhere inside a `loop` or `for` body including a nested `if` or `match` arm"). A lambda, a
//! function or a method has a body of its own, which is not the loop's, so a `break;` there has
//! no loop to end, as has one with no loop around it; each is refused with the row "`break`
//! outside the body of a loop or a `for`".

use super::sx;
use zedc::ast::unit;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;

/// The refusal of `text` by the builder: its row, the text at its span, its message, and each
/// note as `text [the text at its span]`.
fn refusal(text: &str) -> (Option<Row>, String, String, Vec<String>) {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    let e = unit(text, &tokens, &tree).expect_err(text);
    let at = |s: zedc::lex::Span| text[s.start..s.end].to_string();
    let notes = e
        .notes
        .iter()
        .map(|n| format!("{} [{}]", n.text, at(n.span)))
        .collect();
    (e.row, at(e.span), e.message.clone(), notes)
}

#[track_caller]
fn refused(text: &str, message: &str, notes: &[&str]) {
    let (row, at, got, got_notes) = refusal(text);
    assert_eq!(row, Some(Row::BreakOutsideLoop), "{text}");
    assert_eq!(at, "break;", "{text}");
    assert_eq!(got, message, "{text}");
    assert_eq!(got_notes, notes, "{text}");
}

/// A `break;` in a loop's or a `for`'s body, at any depth, builds; one in a loop that a lambda
/// in another loop holds ends the inner loop.
#[test]
fn a_break_in_the_body_of_a_loop_or_a_for_builds() {
    for text in [
        "f(c) = loop { if c { break; }; };",
        "f(c) = loop { { x = 1; if c { break; }; }; };",
        "f(c) = loop t { x = match t { 0 -> { break; }, _ -> t }; };",
        "f(xs) = for x in xs { if x > 0 { break; }; x };",
        "f(c) = loop { if c { y = 1; break; } else if !c { break; }; };",
        "f(c) = loop { g = x -> loop { break; }; };",
        "f(c) = loop { loop { break; }; break; };",
    ] {
        assert!(
            !sx(text).starts_with("error") && sx(text) != "syntax",
            "{text}: {}",
            sx(text)
        );
    }
}

#[test]
fn a_break_in_a_lambda_in_a_loop_is_refused() {
    let text = "f(n) = loop { g = x -> { break; }; };";
    refused(
        text,
        "Invalid use of `break;` in the lambda `g`: it ends only a loop whose own body holds it.",
        &[
            "`x -> { break; }` is the lambda `g`, declared in the loop's body; its body is not the \
             loop's [x -> { break; }]",
            "the loop around the lambda `g`, which a `break;` ends only from the loop's own body \
             [loop { g = x -> { break; }; }]",
            "repair: return a result that the loop's body tests, as `done = g(…); if done { \
             break; };` [break;]",
            "repair: move the `break;` out of the lambda `g`, into the loop's body [break;]",
        ],
    );
    // A lambda bound to no name is named by its kind.
    let (row, _, message, _) = refusal("f(xs) = loop { h(x -> { break; }); };");
    assert_eq!(row, Some(Row::BreakOutsideLoop));
    assert_eq!(
        message,
        "Invalid use of `break;` in a lambda: it ends only a loop whose own body holds it."
    );
}

#[test]
fn a_break_in_a_function_or_a_method_declared_in_a_loop_is_refused() {
    let (row, _, message, notes) = refusal("f(n) = loop { g(x) = { break; }; };");
    assert_eq!(row, Some(Row::BreakOutsideLoop));
    assert_eq!(
        message,
        "Invalid use of `break;` in the function `g`: it ends only a loop whose own body holds it."
    );
    assert_eq!(
        notes.last().map(String::as_str),
        Some("repair: move the `break;` out of the function `g`, into the loop's body [break;]")
    );
    let (row, _, message, _) = refusal("f(n) = loop { T.m(x) = { break; }; };");
    assert_eq!(row, Some(Row::BreakOutsideLoop));
    assert_eq!(
        message,
        "Invalid use of `break;` in the method `T.m`: it ends only a loop whose own body holds it."
    );
}

#[test]
fn a_break_with_no_loop_around_it_is_refused() {
    refused(
        "f(x) = { break; };",
        "Invalid use of `break;` outside a loop: the function `f` has no `loop` or `for` around it.",
        &[
            "`f(x) = { break; };` is the function `f`, with no `loop` or `for` around the \
             `break;` inside it [f(x) = { break; };]",
            "repair: `return e;`, which ends the function `f` with the value `e` [break;]",
        ],
    );
    // At the top level a `break;` is a statement out of place, the row DESIGN.md
    // sec:diagnostics lists it under (TOP-statements-reject, l01_29 top_statements.rs).
    assert_eq!(refusal("break;").0, Some(Row::TopLevelStatement));
}

/// `f(n) = loop t0 { if t0 > 1 { break; }; loop t1 { … }; };`, `n` loops nested, each
/// with a `break;` in an `if` statement: the walk that finds each `break;`'s loop (`stop_of`)
/// runs once.
pub(super) fn nested_breaks(n: usize) -> String {
    let opens: String = (0..n)
        .map(|i| format!("loop t{i} {{ if t{i} > 1 {{ break; }}; "))
        .collect();
    format!("f(n) = {opens}{};\n", " };".repeat(n - 1) + " }")
}

/// `f(n) = loop { { x = 1; { x = 1; … if n > 1 { break; }; } } ; };`, `n` blocks nested in one
/// another's exports in statement position, the innermost ending with an `if` statement and
/// exporting nothing: the walk that marks the paths of a statement (`on_path`) runs once.
pub(super) fn nested_exports(n: usize) -> String {
    format!(
        "f(n) = loop {{ {}if n > 1 {{ break; }};{}; }};\n",
        "{ x = 1; ".repeat(n),
        " }".repeat(n)
    )
}

/// Each shape builds at small sizes; `bench/breaks.rs` holds the ratio of the times at `n`
/// and `8n`.
#[test]
fn the_scaling_shapes_build_at_small_sizes() {
    for n in [1, 2, 9] {
        for text in [nested_breaks(n), nested_exports(n)] {
            let got = sx(&text);
            assert!(
                !got.starts_with("error") && got != "syntax",
                "{text}: {got}"
            );
        }
    }
}
