//! `<-` written where a comparison with a negative operand was meant (DESIGN.md sec:lexical,
//! the `<-` row of the operator table; row "`<-` written where a comparison with a negative
//! operand was meant" of sec:diagnostics; item PITFALL-push-vs-less): `<-` is one token, a
//! push, so `if x<-1 {` stops the parse. The error is reported at the `<-`, shows the condition
//! as written, and offers it with `< -` when the declaration then parses. A push that `< -`
//! does not repair stays a syntax error.

use zedc::ast::Error;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;
use zedc::run::load;

/// The rendered diagnostics of the rejected program `src`.
fn rejected(src: &str) -> String {
    match load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e,
    }
}

/// The error the unit `src` is refused with by the parser.
pub(super) fn refusal(src: &str) -> Error {
    let tokens = lex(src).unwrap();
    Error::of_parse(src, parse(src, &tokens, "Unit", TOP).expect_err(src))
}

/// Whether the parser takes the unit `src`.
pub(super) fn parses(src: &str) -> bool {
    parse(src, &lex(src).unwrap(), "Unit", TOP).is_ok()
}

/// `main` with `x` bound and the lines `body`.
pub(super) fn program(body: &str) -> String {
    format!("main(m: MainArgs) {{\n  x = (m.stdin[0] else \"\").len;\n{body}}}\n")
}

/// The note on what `<-` is.
const PUSH: &str = "`<-` pushes a value into a port, an accumulator or the next generation, and can only be \
                    used as a statement; `x < -1`, with a space, compares `x` with a negative number";

/// Checks that `src` is refused at the `<-` of `written`, with the condition `written` in the headline
/// and, when the declaration then parses, `repaired` offered.
fn refused(src: &str, written: &str, repaired: Option<&str>) {
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::PushWhereLessMeant), "{src}");
    let at = src.find(written).unwrap() + written.find("<-").unwrap();
    assert_eq!((e.span.start, e.span.end), (at, at + 2), "{src}");
    let mut message = format!("Invalid use of the push operator `<-` in a condition: `{written}`.");
    let mut notes = vec![PUSH.to_string()];
    if let Some(r) = repaired {
        message += &format!(" Try `{r}` instead.");
        notes.push(format!("repair: `{r}`"));
    }
    assert_eq!(e.message, message, "{src}");
    let got: Vec<&str> = e.notes.iter().map(|n| n.text.as_str()).collect();
    assert_eq!(got, notes, "{src}");
    for n in &e.notes {
        assert_eq!(n.span, e.span, "{src}");
    }
    if let Some(r) = repaired {
        let fixed = src.replacen(written, r, 1);
        assert!(parses(&fixed), "{fixed}");
    }
}

/// Where a push cannot stand and a comparison with a negated operand can, the headline names
/// the comparison as the repair, written in full.
#[test]
fn a_push_where_a_comparison_stands_offers_the_comparison() {
    let src = "main(m: MainArgs) {\n  x = (m.stdin[0] else \"\").len;\n  m.stdout <- if x<-1 { \"a\" } else { \"b\" };\n}\n";
    let e = rejected(src);
    let headline = e.lines().next().unwrap();
    assert!(headline.contains("Try `if x < -1 {"), "{e}");
    assert!(e.contains("`<-` pushes a value"), "{e}");
}

/// The head of an `if`, the condition of a `while` and a guard after `where`, each up to the
/// token that ends it.
#[test]
fn the_condition_is_shown_from_its_keyword_to_the_token_that_ends_it() {
    refused(
        &program("  m.stdout <- if x<-1 { \"a\" } else { \"b\" };\n"),
        "if x<-1 {",
        Some("if x < -1 {"),
    );
    refused(
        &program("  m.stdout <- if (x<-1) { \"a\" } else { \"b\" };\n"),
        "if (x<-1) {",
        Some("if (x < -1) {"),
    );
    refused(
        &program("  m.stdout <- if x > 0 && x<-1 { \"a\" } else { \"b\" };\n"),
        "if x > 0 && x<-1 {",
        Some("if x > 0 && x < -1 {"),
    );
    refused(
        &program("  n = 0;\n  loop {\n    n = n + 1;\n    while n<-1;\n  };\n  m.stdout <- n;\n"),
        "while n<-1;",
        Some("while n < -1;"),
    );
    refused(
        &program("  m.stdout <- match x { n where n<-1 -> \"y\", _ -> \"n\" };\n"),
        "where n<-1 ->",
        Some("where n < -1 ->"),
    );
}

/// The repair is offered only when the declaration then parses: here a `}` is missing later,
/// so the headline shows the condition and offers nothing.
#[test]
fn no_repair_is_offered_when_the_declaration_still_does_not_parse() {
    refused(
        &program("  m.stdout <- if x<-1 { \"a\" } else { \"b\" ;\n"),
        "if x<-1 {",
        None,
    );
}

/// A push where `< -` does not get the parse further is a syntax error, and a push statement
/// and a comparison written with a space are taken.
#[test]
fn a_push_that_no_comparison_repairs_is_a_syntax_error() {
    let src = program("  y = <- 1;\n  m.stdout <- y;\n");
    assert_eq!(refusal(&src).row, Some(Row::SyntaxError), "{src}");
    for src in [
        program("  m.stdout <- 1;\n"),
        program("  m.stdout <- if x < -1 { \"a\" } else { \"b\" };\n"),
    ] {
        assert!(parses(&src), "{src}");
    }
}

/// `n` bindings before `if x<-1 {`.
pub(super) fn bindings_before_a_push(n: usize) -> String {
    let lines: String = (0..n).map(|i| format!("  a{i} = {i};\n")).collect();
    program(&format!(
        "{lines}  m.stdout <- if x<-1 {{ \"a\" }} else {{ \"b\" }};\n"
    ))
}

/// A condition of `n` terms ending in `x<-1`.
pub(super) fn terms_before_a_push(n: usize) -> String {
    let terms: String = (0..n).map(|i| format!("x > {i} && ")).collect();
    program(&format!(
        "  m.stdout <- if {terms}x<-1 {{ \"a\" }} else {{ \"b\" }};\n"
    ))
}

/// The push is found after many statements and at the end of a long condition. The time each
/// takes is held linear in `bench/conditions.rs`.
#[test]
fn the_push_is_found_after_many_statements_and_in_a_long_condition() {
    for n in [1, 2, 9] {
        let e = refusal(&bindings_before_a_push(n));
        assert_eq!(e.row, Some(Row::PushWhereLessMeant));
        let e = refusal(&terms_before_a_push(n));
        assert_eq!(e.row, Some(Row::PushWhereLessMeant));
        assert!(e.message.contains("Try `if x > 0 && "), "{}", e.message);
    }
}

/// The repair is judged by its own declaration: an error in a later declaration does not
/// withhold it, though the unit with it still does not parse.
#[test]
fn an_error_in_a_later_declaration_does_not_withhold_the_repair() {
    let src = format!(
        "{}g = (1;\n",
        program("  m.stdout <- if x<-1 { \"a\" } else { \"b\" };\n")
    );
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::PushWhereLessMeant), "{src}");
    assert!(
        e.message.ends_with(" Try `if x < -1 {` instead."),
        "{}",
        e.message
    );
    assert!(!parses(&src.replacen("x<-1", "x < -1", 1)), "{src}");
}

/// Outside a condition a push is allowed and no comparison was meant: a push statement whose
/// target is malformed stays a syntax error at the `<-` (plan row
/// FAIL-pitfall-rows-statement-push-near-miss: it got this row, offering
/// `m.stdout::bytes::len < -"a";`, a comparison with a negated string).
#[test]
fn a_malformed_push_statement_is_a_syntax_error() {
    for (body, at) in [
        ("  m.stdout::bytes::len <- \"a\";\n", "m.stdout::bytes::len <-"),
        ("  m::stdout.bytes <- \"a\";\n", "m::stdout.bytes <-"),
        ("  m.stdout::bytes::len <- x;\n", "m.stdout::bytes::len <-"),
    ] {
        let src = program(body);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::SyntaxError), "{src}\n{}", e.message);
        let at = src.find(at).unwrap() + at.len() - 2;
        assert_eq!(e.span.start, at, "{src}");
        assert_eq!(e.message, "Syntax error at `<-`.", "{src}");
    }
}

/// `-` negates a number, never a string or an atom: in a condition, `<-` before a string or an
/// atom literal is refused in the row, with no comparison offered.
#[test]
fn no_comparison_is_offered_with_a_negated_string_or_atom() {
    refused(
        &program("  m.stdout <- if x<-\"a\" { \"a\" } else { \"b\" };\n"),
        "if x<-\"a\" {",
        None,
    );
    refused(
        &program("  m.stdout <- if x<-#a { \"a\" } else { \"b\" };\n"),
        "if x<-#a {",
        None,
    );
}
