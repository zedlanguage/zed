//! `=` written in a condition where `==` was meant (DESIGN.md sec:lexical, the `x = e` row of
//! the operator table; row "`=` written in a condition where `==` was meant" of
//! sec:diagnostics; item PITFALL-assign-in-condition): `=` binds a name and can only be used as a
//! statement, so `if x = 3 {` stops the parse. The error is reported at the `=`, shows the
//! condition as written, and offers it with `==`, its parentheses kept, when the declaration then
//! parses. An `=` outside a condition stays a syntax error.

use zedc::rejection::Row;

use super::push_or_less::{parses, program, refusal};
use zed_tests::step_helpers::l01_29_diagnostics::rejected;

/// The note on what `=` is.
const BINDS: &str =
    "`=` binds a name and can only be used as a statement; `==` compares two values";

/// Checks that `src` is refused at the `=` of `written` with `written` in the headline and,
/// when the declaration then parses, `repaired` offered.
fn refused(src: &str, written: &str, repaired: Option<&str>) {
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::BindingInCondition), "{src}");
    let at = src.find(written).unwrap() + written.find(" = ").unwrap() + 1;
    assert_eq!((e.span.start, e.span.end), (at, at + 1), "{src}");
    let mut message = format!("Invalid use of `=` in a condition: `{written}`.");
    let mut notes = vec![BINDS.to_string()];
    if let Some(r) = repaired {
        message += &format!(" Try `{r}` instead.");
        notes.push(format!("repair: `{r}`"));
    }
    assert_eq!(e.message, message, "{src}");
    let got: Vec<&str> = e.notes.iter().map(|n| n.text.as_str()).collect();
    assert_eq!(got, notes, "{src}");
    if let Some(r) = repaired {
        let fixed = src.replacen(written, r, 1);
        assert!(parses(&fixed), "{fixed}");
    }
}

/// Zed already rejects the program, since `x = 3` is not an expression; the headline should say
/// why and offer `==`.
#[test]
fn a_binding_where_a_condition_stands_offers_equality() {
    for (src, want) in [
        (
            "main(m: MainArgs) {\n  x = (m.stdin[0] else \"\").len;\n  m.stdout <- if x = 3 { \"y\" } else { \"n\" };\n}\n",
            "Try `if x == 3 {",
        ),
        (
            "main(m: MainArgs) {\n  x = (m.stdin[0] else \"\").len;\n  m.stdout <- if (x = 3) { \"y\" } else { \"n\" };\n}\n",
            "Try `if (x == 3) {",
        ),
    ] {
        let e = rejected(src);
        assert!(e.lines().next().unwrap().contains(want), "{e}");
    }
}

/// The head of an `if`, its parentheses kept, the condition of an `until` and a guard after
/// `where`, each up to the token that ends it.
#[test]
fn the_condition_is_shown_from_its_keyword_to_the_token_that_ends_it() {
    refused(
        &program("  m.stdout <- if x = 3 { \"y\" } else { \"n\" };\n"),
        "if x = 3 {",
        Some("if x == 3 {"),
    );
    refused(
        &program("  m.stdout <- if (x = 3) { \"y\" } else { \"n\" };\n"),
        "if (x = 3) {",
        Some("if (x == 3) {"),
    );
    refused(
        &program("  m.stdout <- if x = 3 && x > 1 { \"y\" } else { \"n\" };\n"),
        "if x = 3 && x > 1 {",
        Some("if x == 3 && x > 1 {"),
    );
    refused(
        &program("  n = 0;\n  loop {\n    n = n + 1;\n    until n = 3;\n  };\n  m.stdout <- n;\n"),
        "until n = 3;",
        Some("until n == 3;"),
    );
    refused(
        &program("  m.stdout <- match x { n where n = 3 -> \"y\", _ -> \"n\" };\n"),
        "where n = 3 ->",
        Some("where n == 3 ->"),
    );
}

/// The repair is offered only when the declaration then parses.
#[test]
fn no_repair_is_offered_when_the_declaration_still_does_not_parse() {
    refused(
        &program("  m.stdout <- if x = 3 { \"y\" } else { \"n\" ;\n"),
        "if x = 3 {",
        None,
    );
}

/// An `=` outside a condition is a syntax error, and a binding statement and a comparison are
/// taken.
#[test]
fn a_binding_outside_a_condition_is_a_syntax_error() {
    let src = program("  m.stdout <- (x = 3);\n");
    assert_eq!(refusal(&src).row, Some(Row::SyntaxError), "{src}");
    for src in [
        program("  y = 3;\n  m.stdout <- y;\n"),
        program("  m.stdout <- if x == 3 { \"y\" } else { \"n\" };\n"),
    ] {
        assert!(parses(&src), "{src}");
    }
}

/// `n` bindings before `if x = 3 {`.
pub(super) fn bindings_before_a_binding(n: usize) -> String {
    let lines: String = (0..n).map(|i| format!("  a{i} = {i};\n")).collect();
    program(&format!(
        "{lines}  m.stdout <- if x = 3 {{ \"y\" }} else {{ \"n\" }};\n"
    ))
}

/// The binding is found after many statements. The time is held linear in
/// `bench/conditions.rs`.
#[test]
fn the_binding_is_found_after_many_statements() {
    for n in [1, 2, 9] {
        let e = refusal(&bindings_before_a_binding(n));
        assert_eq!(e.row, Some(Row::BindingInCondition));
    }
}

/// The repair is judged by its own declaration: an error in a later declaration does not
/// withhold it, though the unit with it still does not parse.
#[test]
fn an_error_in_a_later_declaration_does_not_withhold_the_repair() {
    let src = format!(
        "{}g = (1;\n",
        program("  m.stdout <- if x = 3 { \"y\" } else { \"n\" };\n")
    );
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::BindingInCondition), "{src}");
    assert!(
        e.message.ends_with(" Try `if x == 3 {` instead."),
        "{}",
        e.message
    );
    assert!(!parses(&src.replacen("x = 3", "x == 3", 1)), "{src}");
}
