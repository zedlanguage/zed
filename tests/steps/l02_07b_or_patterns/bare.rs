//! Row "Pattern built with an operator, written bare" (DESIGN.md sec:diagnostics, step L2.7b):
//! an or-pattern, a range or an `is`-pattern stands in parentheses that hold it alone, so one
//! written bare, wherever it stands (the arm, an alternative, a tuple part, a field, a payload
//! with other parts, an `else` tail's payload), is refused at the pattern, with the arm written
//! with it in parentheses. Where parentheses would not make the arm parse, the plain syntax error
//! stands instead.

use zedc::rejection::Row;

use super::{build, refusal};

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

/// An `else` tail takes one atom pattern (`ElseTail` in DESIGN.md sec:grammar;
/// zed/grammar/cases.txt refuses `x else (#a | #b) -> d`), so an or-pattern there, bare or in
/// parentheses, is refused at the pattern with the `match` the tail stands for: `e else P -> d` is
/// `match e { P -> d, x -> x }` (sec:grammar, the desugaring of `ElseTail`). Before this clause the
/// bare form was refused as a union written bare as a key, with a repair that does not parse
/// either, and the form in parentheses with the plain syntax error.
#[test]
fn an_or_pattern_after_else_is_refused_with_the_match_it_stands_for() {
    #[track_caller]
    fn refused(src: &str, pattern: &str, repair: &str) {
        let e = refusal(src);
        assert_eq!(e.row, None, "{src}: {e}");
        assert_eq!(&src[e.span.start..e.span.end], pattern, "{src}");
        assert_eq!(
            e.message,
            format!(
                "An `else` tail takes one atom pattern, and `{pattern}` is an or-pattern. Try \
                 `{repair}` instead."
            ),
            "{src}"
        );
        let notes: Vec<&str> = e.notes.iter().map(|n| n.text.as_str()).collect();
        assert!(
            notes.contains(&format!("repair: `{repair}`").as_str()),
            "{src}: {notes:?}"
        );
    }
    refused(
        "f(r) = r else #a | #b -> 0;\n",
        "#a | #b",
        "match r { (#a | #b) -> 0, x -> x }",
    );
    refused(
        "f(r) = r else (#a | #b) -> 0;\n",
        "#a | #b",
        "match r { (#a | #b) -> 0, x -> x }",
    );
    refused(
        "f(r) = r else #ok(x) | #err(x) -> x;\n",
        "#ok(x) | #err(x)",
        "match r { (#ok(x) | #err(x)) -> x, x -> x }",
    );
    // The operand runs back over the operators that bind tighter than `else` and over the
    // `else` tails before it; a later tail stays after the `match`.
    refused(
        "f(a, r) = a + r else #c -> 1 else #a | #b -> 0 else #d -> 2;\n",
        "#a | #b",
        "match a + r else #c -> 1 { (#a | #b) -> 0, x -> x }",
    );
    // In a lambda and in a `match` arm, the operand stops at the arrow before it.
    refused(
        "g = (r) -> r else #a | #b -> 0;\n",
        "#a | #b",
        "match r { (#a | #b) -> 0, x -> x }",
    );
    refused(
        "f(v, r) = match v { #a -> r else (#a | #b) -> 0, _ -> 1 };\n",
        "#a | #b",
        "match r { (#a | #b) -> 0, x -> x }",
    );
    // Three of the programs above with the repair in place: each parses.
    for fixed in [
        "f(r) = match r { (#a | #b) -> 0, x -> x };\n",
        "f(a, r) = match a + r else #c -> 1 { (#a | #b) -> 0, x -> x } else #d -> 2;\n",
        "f(v, r) = match v { #a -> match r { (#a | #b) -> 0, x -> x }, _ -> 1 };\n",
    ] {
        build(fixed);
    }
}

/// Where parentheses alone do not make the arm parse, the row is not given: `1..5` is no range
/// pattern, and an `else` tail takes an atom pattern only (an or-pattern there has its own message,
/// tested above).
#[test]
fn where_parentheses_would_not_parse_the_plain_error_stands() {
    for src in [
        "f(r) = r else n is int -> 0;\n",
        "f(v) = match v { #p(a: 1..5) where a > 2 -> 1, _ -> 0 };\n",
        "f(v) = match v { n is -> 1 };\n",
        "f(v) = match v { | #a -> 1 };\n",
    ] {
        let e = refusal(src);
        assert_ne!(e.row, Some(Row::BareOperatorPattern), "{src}: {e}");
    }
}
