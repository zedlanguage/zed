//! FAIL-initial-reads-shadowed (TEST-complete-parse, author P189): a read of the loop in an
//! `initial` value, outside the scope of a binder of the same name inside that value, is a read
//! of the loop (DESIGN.md sec:generations, row "An `initial` value that reads the loop";
//! sec:lexical, step L1.14, the scopes of a block, a lambda, a `for` binder, a `match` arm and
//! an `else` pattern). The builder kept one set of the names bound anywhere in the value and
//! skipped every read of them, so `t + (t -> t)(1)` built.

use super::initial::{Parsed, parsed};
use super::initial_reads::{row_at, with_value};
use zedc::ast::unit;
use zedc::rejection::Row;

/// The values of `values` the builder does not refuse with the row at a read of `t`.
fn not_found(values: &[&str]) -> Vec<String> {
    let mut wrong = Vec::new();
    for v in values {
        let text = with_value(v);
        let got = row_at(&text);
        let want = Some((Some(Row::InitialReadsLoop), "t".to_string()));
        if got != want {
            wrong.push(format!("initial x = {v};\n  got {got:?}"));
        }
    }
    wrong
}

#[test]
fn a_read_of_the_loop_outside_the_scope_of_a_binder_of_its_name_is_found() {
    let wrong = not_found(&[
        "t + (t -> t)(1)",
        "(t -> t)(1) + t",
        "t + { t = 1; t }",
        "(for t in xs { t }) ++ [t]",
        "t + match 1 { t -> t }",
        "(xs[0] else #e(t) -> t) + t",
    ]);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn each_binder_scopes_over_its_own_part_only() {
    // A `for` source, a block binding's own value and the statements before it, a later
    // parameter's name in an earlier default, another arm of the `match`, a function's
    // parameter after its body, an indexed definition's key in its key set: each reads the
    // loop's `t`.
    let wrong = not_found(&[
        "(for t in [t] { t })",
        "{ t = t; t }",
        "{ y = t; t = 1; y }",
        "((y = t, t = 2) -> y)()",
        "{ f(y = t, t = 2) = y; f() }",
        "match 1 { t -> 1, _ -> t }",
        "match 1 { 0 -> t, t -> t }",
        "{ f(t) = t; f(1) + t }",
        "{ d[t in 0..<t] = t; d[0] }",
        "(xs[0] else #e(t) -> 1) + t",
        "(t, (t -> t)(1))",
    ]);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_read_in_the_scope_of_a_binder_of_its_name_is_no_read_of_the_loop() {
    // A `for` guard, a later parameter's default, a guard of the arm that binds the name, a
    // function's own parameter, an indexed definition's key in its value, a name bound by an
    // earlier statement of the block: each reads the binder, not the loop.
    let values = [
        "(for t in xs where t > 0 { t })",
        "((t = 1, y = t) -> y)()",
        "match 1 { t where t > 0 -> t, _ -> 0 }",
        "{ f(t) = t; f(1) }",
        "{ d[t in 0..<3] = t; d[0] }",
        "{ t = 1; f(y = t) = y; f() }",
        "{ t = 1; y = { t }; y }",
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

/// The loop whose `initial x` value is a tuple of `n` lambdas, `n` at least 1, that each bind
/// and read `t`, then a read of the loop's `t`: `((t -> t)(1), …, t)`.
pub(super) fn many_binders(n: usize) -> String {
    let mut value = String::from("(");
    for _ in 0..n {
        value.push_str("(t -> t)(1), ");
    }
    value.push_str("t)");
    with_value(&value)
}

/// Asserts the unit `p` refused with row "An `initial` value that reads the loop" at `t`, the
/// last part of the tuple.
pub(super) fn last_read_found(p: &Parsed) {
    let (text, tokens, tree) = p;
    let e = unit(text, tokens, tree).unwrap_err();
    assert_eq!(e.row, Some(Row::InitialReadsLoop));
    assert_eq!(Some(e.span.start), text.find("t);"));
}

/// The read after `n` binders of its name is found at small sizes; the time is held in
/// `bench/initial.rs`.
#[test]
fn a_read_after_many_binders_of_its_name_is_found_at_small_sizes() {
    for n in [1, 2, 9] {
        last_read_found(&parsed(many_binders(n)));
    }
}
