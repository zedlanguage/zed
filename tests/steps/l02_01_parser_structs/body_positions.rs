//! Row "Display in body position" (DESIGN.md sec:diagnostics) at each form whose brace is a
//! block whatever it contains (sec:lexical: a signature, `if`, `else`, `loop`, `for`, a match
//! arm's `->`, a lambda's `->`, and `proof`), with each kind of display and each repair of the
//! block reading: a set of one entry is the block whose value is that entry, a set of several
//! the block whose value is their tuple, a record or a map a block of statements. The messages
//! of the three kinds, written out whole, are tested in l01_29_diagnostics/body_display.rs. A
//! `law` with its `proof` is refused as a later form before its body is read, so `proof` is not
//! tested here.

use zedc::ast::{Error, unit};
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;

/// The error the unit `text` is refused with; it must parse.
fn refusal(text: &str) -> Error {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP)
        .unwrap_or_else(|e| panic!("{text:?} does not parse: {e}"));
    match unit(text, &tokens, &tree) {
        Ok(_) => panic!("{text:?} builds"),
        Err(e) => e,
    }
}

#[test]
fn each_form_whose_brace_is_a_block_is_named() {
    // (unit, the form the message names)
    let cases = [
        ("f() { 1, 2 }", "a signature"),
        ("v = if c { 1, 2 } else { 3 };", "the head of an `if`"),
        ("v = if c { 3 } else { 1, 2 };", "the `else` of an `if`"),
        ("v = r else { 1, 2 };", "a fallback's `else`"),
        ("v = x -> { 1, 2 };", "a lambda's `->`"),
        ("v = match x { _ -> { 1, 2 } };", "a match arm's `->`"),
        ("v = for x in xs { 1, 2 };", "the head of a `for`"),
        ("v = loop { 1, 2 };", "`loop`"),
    ];
    let mut wrong = Vec::new();
    for (text, form) in cases {
        let e = refusal(text);
        let want = format!("a set display in body position: the brace after {form} is a block");
        if e.row != Some(Row::DisplayInBody) || !e.message.starts_with(&want) {
            wrong.push(format!("{text}\n  {:?}: {}", e.row, e.message));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn each_kind_of_display_gets_its_repair() {
    // (unit, kind, the block repair)
    let cases = [
        (
            "v = r else { 1, };",
            "set",
            "repair: `{ 1 }`, the block whose value is `1`",
        ),
        (
            "v = r else { 1, 2, 3 };",
            "set",
            "repair: `{ (1, 2, 3) }`, the block whose value is the tuple",
        ),
        (
            "v = r else { x: 1 };",
            "record",
            "repair: a block, its statements ended by `;`",
        ),
        (
            "v = r else { 1 -> 2, 3 -> 4 };",
            "map",
            "repair: a block, its statements ended by `;`",
        ),
    ];
    let mut wrong = Vec::new();
    for (text, kind, repair) in cases {
        let e = refusal(text);
        let head = format!("a {kind} display in body position");
        let has_repair = e.notes.iter().any(|n| n.text.starts_with(repair));
        let has_display = e.notes.iter().any(|n| {
            n.text
                .ends_with(&format!("the {kind} display in parentheses"))
        });
        if e.row != Some(Row::DisplayInBody)
            || !e.message.starts_with(&head)
            || !has_repair
            || !has_display
        {
            let notes: Vec<&str> = e.notes.iter().map(|n| n.text.as_str()).collect();
            wrong.push(format!("{text}\n  {}\n  {notes:?}", e.message));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The part that reads as a display: a top-level comma, or the record field when there is none.
#[test]
fn the_part_that_reads_as_a_display_is_named() {
    let e = refusal("v = r else { x: 1 };");
    assert!(
        e.notes
            .iter()
            .any(|n| n.text == "`x: 1` is a record field, `name: value`, not an expression"),
        "{:?}",
        e.notes
    );
    let e = refusal("v = r else { x: 1, y: 2 };");
    assert!(
        e.notes
            .iter()
            .any(|n| n.text.starts_with("a comma at the top level of the brace")),
        "{:?}",
        e.notes
    );
}
