//! Row "Pattern built with an operator, written bare" (DESIGN.md sec:diagnostics, step L2.7b):
//! an or-pattern, a range or an `is`-pattern stands in parentheses that hold it alone, so one
//! written bare, wherever it stands (the arm, an alternative, a tuple part, a field, a payload
//! with other parts, an `else` tail's payload), is refused at the pattern, with the arm written
//! with it in parentheses. Where parentheses would not make the arm parse, the plain syntax error
//! stands instead.

use zedc::rejection::Row;

use super::refusal;

/// Checks that `src` is refused at `pattern` as written bare, as `what`, with the arm `repair`.
#[track_caller]
fn refused(src: &str, pattern: &str, what: &str, repair: &str) {
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::BareOperatorPattern), "{src}: {e}");
    assert_eq!(&src[e.span.start..e.span.end], pattern, "{src}");
    assert_eq!(
        e.message,
        format!("`{pattern}` is {what}; write it in parentheses. Try `{repair}` instead."),
        "{src}"
    );
    let notes: Vec<&str> = e.notes.iter().map(|n| n.text.as_str()).collect();
    assert!(
        notes.contains(&format!("repair: `{repair}`").as_str()),
        "{src}: {notes:?}"
    );
}

#[test]
fn the_three_forms_written_bare_as_the_arm_are_refused_with_their_repairs() {
    // The repairs of the row in DESIGN.md, in its words.
    refused(
        "f(c) = match c { #red | #green -> 1, #blue -> 2 };\n",
        "#red | #green",
        "an or-pattern",
        "(#red | #green) -> 1",
    );
    refused(
        "f(v) = match v { 0..=9 -> #digit, _ -> #other };\n",
        "0..=9",
        "a range pattern",
        "(0..=9) -> #digit",
    );
    refused(
        "f(v) = match v { n is int -> n, _ -> 0 };\n",
        "n is int",
        "an `is`-pattern",
        "(n is int) -> n",
    );
    refused(
        "f(v) = match v { 1.. -> 1, _ -> 0 };\n",
        "1..",
        "a range pattern",
        "(1..) -> 1",
    );
    // The type of an `is`-pattern takes the union after it.
    refused(
        "f(v) = match v { is int | bool -> 1, _ -> 2 };\n",
        "is int | bool",
        "an `is`-pattern",
        "(is int | bool) -> 1",
    );
    refused(
        "f(v) = match v { n is int | #none -> 0, _ -> 1 };\n",
        "n is int | #none",
        "an `is`-pattern",
        "(n is int | #none) -> 0",
    );
    // A guard stays with its arm.
    refused(
        "f(v) = match v { n is int where n > 0 -> n, _ -> 0 };\n",
        "n is int",
        "an `is`-pattern",
        "(n is int) where n > 0 -> n",
    );
}

#[test]
fn a_bare_pattern_inside_another_is_refused_where_it_stands() {
    refused(
        "f(t) = match t { (#a | #b, x) -> x };\n",
        "#a | #b",
        "an or-pattern",
        "((#a | #b), x) -> x",
    );
    refused(
        "f(v) = match v { #p(0..=9, y) -> 1, _ -> 0 };\n",
        "0..=9",
        "a range pattern",
        "#p((0..=9), y) -> 1",
    );
    refused(
        "f(v) = match v { Box(v: #a | #b) -> 2, _ -> 0 };\n",
        "#a | #b",
        "an or-pattern",
        "Box(v: (#a | #b)) -> 2",
    );
    refused(
        "f(v) = match v { (#a | n is int) -> 0, _ -> 1 };\n",
        "n is int",
        "an `is`-pattern",
        "(#a | (n is int)) -> 0",
    );
    refused(
        "f(v) = match v { (0..=9 | #a) -> 0, _ -> 1 };\n",
        "0..=9",
        "a range pattern",
        "((0..=9) | #a) -> 0",
    );
    // A later arm, after arms that parse.
    refused(
        "f(v) = match v { #a -> 0, (#b | #c) -> 1, x is int -> 2, _ -> 3 };\n",
        "x is int",
        "an `is`-pattern",
        "(x is int) -> 2",
    );
}

#[test]
fn a_bare_pattern_in_an_else_payload_is_refused_at_the_pattern() {
    // The payload parses as an expression, so the parse stops at the `->`.
    refused(
        "f(r) = r else #ok(v: n is int) -> 0;\n",
        "n is int",
        "an `is`-pattern",
        "#ok(v: (n is int)) -> 0",
    );
    refused(
        "f(r) = r else #p(#a | #b, x) -> 0;\n",
        "#a | #b",
        "an or-pattern",
        "#p((#a | #b), x) -> 0",
    );
}

/// Where parentheses alone do not make the arm parse, the row is not given: an `else` tail takes
/// an atom pattern only, and `1..5` is no range pattern.
#[test]
fn where_parentheses_would_not_parse_the_plain_error_stands() {
    for src in [
        "f(r) = r else n is int -> 0;\n",
        "f(r) = r else (#a | #b) -> 0;\n",
        "f(r) = r else (#ok(x) | #err(y)) -> 0;\n",
        "f(v) = match v { #p(a: 1..5) where a > 2 -> 1, _ -> 0 };\n",
        "f(v) = match v { n is -> 1 };\n",
        "f(v) = match v { | #a -> 1 };\n",
    ] {
        let e = refusal(src);
        assert_ne!(e.row, Some(Row::BareOperatorPattern), "{src}: {e}");
    }
}
