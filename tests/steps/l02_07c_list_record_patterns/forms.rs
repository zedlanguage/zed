//! Each pattern of DESIGN.md step L2.7c builds, formats to itself and binds its names; the forms
//! the grammar leaves out (a rest not written last, a rest with no name, two rests, a field with
//! no colon) do not parse.

use zed_tests::not_yet;

use super::{fmt, resolution_errors, sx};

/// Checks that each `(text, tree)` builds to `tree`.
#[track_caller]
fn trees(cases: &[(&str, &str)]) {
    zed_tests::tables::check(cases, sx);
}

#[test]
fn a_list_pattern_builds_with_its_entries_and_rest_in_order() {
    trees(&[
        (
            "f(v) = match v { [] -> 0, [a] -> a, [a, b, ..rest] -> b, [..rest] -> 1 };",
            "(def f (v) = (match v (-> [] 0) (-> [a] a) (-> [a, b, ..rest] b) (-> [..rest] 1)))",
        ),
        // A trailing comma is the grammar's; it builds the same list.
        (
            "f(v) = match v { [a, (b, c),] -> a, [#x, ..r,] -> 0 };",
            "(def f (v) = (match v (-> [a, (b, c)] a) (-> [#x, ..r] 0)))",
        ),
        // Nested in each other and in the other patterns.
        (
            "f(v) = match v { [[a, ..r], ..s] -> a, ([h, ..t], #b(x: [y])) -> h };",
            "(def f (v) = (match v (-> [[a, ..r], ..s] a) (-> ([h, ..t], #b(x: [y])) h)))",
        ),
    ]);
}

#[test]
fn a_record_pattern_builds_with_its_fields_in_order() {
    trees(&[
        (
            "f(p) = match p { {x:, y: 0} -> x, {x: [h, ..t],} -> h };",
            "(def f (p) = (match p (-> {x:, y: 0} x) (-> {x: [h, ..t]} h)))",
        ),
        (
            "f(p) = match p { {a: {b:}} -> b, ({c: (#d | #e)}, _) -> 0 };",
            "(def f (p) = (match p (-> {a: {b:}} b) (-> ({c: (| #d #e)}, _) 0)))",
        ),
    ]);
}

#[test]
fn the_forms_the_grammar_leaves_out_do_not_parse() {
    for text in [
        // DESIGN.md step L2.7c: the rest is written last.
        "f(v) = match v { [.., last] -> last };",
        "f(v) = match v { [..r, last] -> last };",
        // The rest has a name, and there is one.
        "f(v) = match v { [a, ..] -> a };",
        "f(v) = match v { [a, ..r, ..s] -> a };",
        "f(v) = match v { [,] -> 0 };",
        // A field of a record pattern is written with its colon.
        "f(p) = match p { {x} -> x };",
        "f(p) = match p { {x:, y} -> x };",
    ] {
        assert_eq!(sx(text), "syntax", "{text}");
    }
}

#[test]
fn each_prints_back_as_written() {
    for text in [
        "x = match v {\n  [] -> 0,\n  [a] -> a,\n  [a, b, ..rest] -> b,\n  [..rest] -> 1,\n};\n",
        "x = match v {\n  [[a, ..r], ..s] -> a,\n  ([h, ..t], #b(x: [y])) -> h,\n};\n",
        "x = match p {\n  {x:, y: 0} -> x,\n  {a: {b:}} -> b,\n  {c: (#d | #e)} -> 0,\n};\n",
    ] {
        assert_eq!(fmt(text), text);
    }
    // The trailing commas go.
    assert_eq!(
        fmt("x = match v {\n  [a, ..r,] -> a,\n  {x:,} -> x,\n};\n"),
        "x = match v {\n  [a, ..r] -> a,\n  {x:} -> x,\n};\n"
    );
}

/// The rest, the entries and the fields written `f:` bind, so no name is reported as not
/// defined. In a `match` the `match` itself is reported as a form not compiled yet, and its
/// patterns are not reported again; the pattern of an `else` is reported, each list and record
/// pattern at its own span.
#[test]
fn the_names_of_each_are_bound() {
    let text =
        "f(v) = match v { [a, [b], ..rest] -> a + b + rest, {x:, y: (q,)} -> x + q, _ -> 0 };\n";
    let errors = resolution_errors(text);
    let messages: Vec<&str> = errors.iter().map(|e| e.message.as_str()).collect();
    assert_eq!(messages, [not_yet("a `match`")], "{text}");
    // An `else` takes an atom pattern (grammar rule ElseTail), so the patterns are its payload.
    for (text, what, at) in [
        (
            "f(v) = v else #ok(e: [a, [b], ..rest]) -> a + b + rest;\n",
            "a list pattern `[a, ..rest]`",
            "[a, [b], ..rest]",
        ),
        (
            "f(v) = v else #ok(e: [a, [b], ..rest]) -> a + b + rest;\n",
            "a list pattern `[a, ..rest]`",
            "[b]",
        ),
        (
            "f(p) = p else #ok(r: {x:, y: (q,)}) -> x + q;\n",
            "a record pattern `{x: p}`",
            "{x:, y: (q,)}",
        ),
    ] {
        let errors = resolution_errors(text);
        let messages: Vec<&str> = errors.iter().map(|e| e.message.as_str()).collect();
        assert!(
            !messages.iter().any(|m| m.contains("is not defined")),
            "{text}: {messages:?}"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.message == not_yet(what) && &text[e.span.start..e.span.end] == at),
            "{at}: {messages:?}"
        );
    }
    // Bound in the arm alone: a use after the match is not.
    let errors = resolution_errors("f(v) = match v { [..rest] -> 0, _ -> 0 } + rest;\n");
    assert!(
        errors
            .iter()
            .any(|e| e.message.starts_with("`rest` is not defined.")),
        "{:?}",
        errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}
