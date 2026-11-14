//! Row "An `initial` value that reads the loop" (DESIGN.md sec:generations): the value of an
//! `initial` statement is computed once, before the first step, so it reads only names given a
//! value before the loop. The read is found in every kind of expression and statement the value
//! can hold; and a name the value binds itself, read inside the binder's scope, is no read of the
//! loop (sec:lexical, step L1.14: shadowing, the scope of a block, a lambda, a `for` binder, a
//! `match` arm and an `else` pattern). A read of the loop's name outside such a scope, in a value
//! that binds the same name elsewhere, is not found yet: FAIL-initial-reads-shadowed.

use zedc::ast::unit;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;

/// The loop whose `initial x` statement has the value `value`, with `t` its step index and `xs`
/// and `r0` names bound before it.
pub(super) fn with_value(value: &str) -> String {
    format!(
        "xs = [1, 2];\nr0 = {{ a: 1 }};\nr = loop t {{\n  while t < 3;\n  initial x = {value};\n  \
         x' = x + 1;\n}};\n"
    )
}

/// The row the unit is refused with and the text it is reported at, or `None` when it builds.
pub(super) fn row_at(text: &str) -> Option<(Option<Row>, String)> {
    let tokens = lex(text).unwrap();
    let Ok(tree) = parse(text, &tokens, "Unit", TOP) else {
        return Some((None, "does not parse".to_string()));
    };
    match unit(text, &tokens, &tree) {
        Ok(_) => None,
        Err(e) => Some((e.row, text[e.span.start..e.span.end].to_string())),
    }
}

#[test]
fn a_read_of_the_step_index_is_found_in_every_kind_of_expression() {
    let values = [
        "\"n${t}\"",
        "-t",
        "(t is int)",
        "r0.a + t",
        "xs::len + t",
        "xs[t]",
        "(t in xs)",
        "(xs >< ((a, b) -> a + t))",
        "(t >< max)",
        "t else 0",
        "xs[0] else #e -> t",
        "f(t)",
        "f(y: t)",
        "(t, 1)",
        "[t]",
        "{t}",
        "{1 -> t}",
        "{t -> 1}",
        "t..<5",
        "t..=5",
        "t..",
        "(for y in xs { y + t })",
        "(for y in xs where y < t { y })",
        "(y -> y + t)(1)",
        "((y = t) -> y)()",
        "{ y = t; y }",
        "{ local y = t; y }",
        "{ y, z = (t, 1); y }",
        "{ d[i in 0..<3] = i + t; d[0] }",
        "{ d[i in 0..<t] = i; d[0] }",
        "{ f(y) = y + t; f(1) }",
        "{ f(y = t) = y; f() }",
        "{ f(t + 1); 1 }",
        "{ @a y = t; y }",
        "match t { _ -> 1 }",
        "match 1 { _ -> t }",
        "match 1 { y where y < t -> 1, _ -> 0 }",
        "{ a: t }",
        "r0 with { a = t }",
        "if t > 0 { 1 } else { 2 }",
        "if true { t } else { 2 }",
        "if true { 1 } else { t }",
        "xs*.f(t)",
    ];
    let mut wrong = Vec::new();
    for v in values {
        let text = with_value(v);
        let got = row_at(&text);
        if got != Some((Some(Row::InitialReadsLoop), "t".to_string())) {
            wrong.push(format!("initial x = {v};\n  got {got:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_name_the_value_binds_and_reads_in_its_scope_is_no_read_of_the_loop() {
    let values = [
        "(t -> t + 1)(1)",
        "{ t = 1; t }",
        "(for t in xs { t })",
        "match 1 { t -> t }",
        "xs[0] else #e(t) -> t",
    ];
    let mut wrong = Vec::new();
    for v in values {
        let text = with_value(v);
        match row_at(&text) {
            None => {}
            Some((row, at)) if row == Some(Row::InitialReadsLoop) || row.is_none() => {
                wrong.push(format!("initial x = {v};\n  refused as {row:?} at `{at}`"))
            }
            Some(_) => {}
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
