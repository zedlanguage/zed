//! A display in body position (DESIGN.md sec:diagnostics, row "Display in body position", and
//! the brace rules of sec:lexical): a brace after a signature, `if`, `else`, `loop`, `for`, a
//! match arm's `->` or a lambda's `->` is a block whatever it contains. A brace there that
//! reads as a display, through a top-level comma, a field `name: e`, an entry `k -> v`, or a
//! lone unparenthesized lambda `{ k -> v }`, is rejected with the form whose body it is, the
//! part that reads as a display, and both repairs: the display in parentheses and the block
//! with its value grouped.

use zedc::ast::{Error, unit};
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;

use super::rejected;

/// The syntax tree of the unit `text`, or its error.
fn built(text: &str) -> Result<(), Error> {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP)
        .unwrap_or_else(|e| panic!("{text:?} does not parse: {e}"));
    unit(text, &tokens, &tree).map(|_| ())
}

/// Whether the unit `text` is rejected by the row "Display in body position".
fn display_in_body(text: &str) -> bool {
    built(text)
        .err()
        .is_some_and(|e| e.row == Some(Row::DisplayInBody))
}

/// A ledger's edit for each transaction, the arm of `#open` written as corpus program 19 first
/// wrote it: a block whose value is a lambda, where a one-entry map was meant.
const LEDGER: &str = "\
type Tx = #open(id: String) | #deposit(id: String, amt: int);

edits(positional tx) = match tx {
  #open(id:) -> { id -> #insert(0) },
  #deposit(id:, amt:) -> ({ id -> #update(b -> b + amt) }),
};
";

#[test]
fn a_ledger_arm_whose_brace_holds_one_entry_is_rejected_with_both_readings() {
    let out = rejected(LEDGER);
    assert_eq!(out, "4:17: a brace after a match arm's `->` whose one content is the lambda `id -> #insert(0)`: a \
brace there is a block, so this is a block whose value is that lambda, while `{ id -> #insert(0) }` reads as a \
one-entry map; write the reading you mean
  [1] 4:14: the brace follows a match arm's `->`, so it is a block whatever it contains (sec:lexical)
      4 |   #open(id:) -> { id -> #insert(0) },
        |              ^^ [1]
        |                 ^^^^^^^^^^^^^^^^^^^^ [3, 4]
        |                   ^^^^^^^^^^^^^^^^ [2]
  [2] 4:19: `id -> #insert(0)` reads as a map entry `key -> value`; in a block it is a lambda, and the block's value
  [3] 4:17: repair: `({ id -> #insert(0) })`, the map display in parentheses
  [4] 4:17: repair: `{ (id -> #insert(0)) }`, the block whose value is the lambda");
}

#[test]
fn a_fallback_whose_default_is_a_set_is_rejected_with_both_readings() {
    let out = rejected("tags(positional s) = s.split(\",\") else { \"none\", \"all\" };\n");
    assert_eq!(out, "1:40: a set display in body position: the brace after a fallback's `else` is a block whatever \
it contains, and `{ \"none\", \"all\" }` reads as a set display; write the reading you mean
  [1] 1:35: the brace follows a fallback's `else`, so it is a block whatever it contains (sec:lexical)
      1 | tags(positional s) = s.split(\",\") else { \"none\", \"all\" };
        |                                   ^^^^ [1]     ^ [2]
        |                                        ^^^^^^^^^^^^^^^^^ [3, 4]
  [2] 1:48: a comma at the top level of the brace separates the entries of a display; a block separates its statements with `;`
  [3] 1:40: repair: `({ \"none\", \"all\" })`, the set display in parentheses
  [4] 1:40: repair: `{ (\"none\", \"all\") }`, the block whose value is the tuple");
}

#[test]
fn a_function_body_written_as_a_record_is_rejected() {
    let out = rejected("origin() { x: 0.0, y: 0.0 }\n");
    assert_eq!(out, "1:10: a record display in body position: the brace after a signature is a block whatever it \
contains, and `{ x: 0.0, y: 0.0 }` reads as a record display; write the reading you mean
  [1] 1:8: the brace follows a signature, so it is a block whatever it contains (sec:lexical)
      1 | origin() { x: 0.0, y: 0.0 }
        |        ^ [1]     ^ [2]
        |          ^^^^^^^^^^^^^^^^^^ [3, 4]
  [2] 1:18: a comma at the top level of the brace separates the entries of a display; a block separates its statements with `;`
  [3] 1:10: repair: `({ x: 0.0, y: 0.0 })`, the record display in parentheses
  [4] 1:10: repair: a block, its statements ended by `;` and its value one expression written last; an entry `name: value` or `key -> value` is not an expression");
}

#[test]
fn each_body_position_rejects_a_display_and_a_lone_lambda() {
    // Each body position, with `@` where the brace goes.
    let positions = [
        ("signature", "f(x) @\n"),
        ("method", "Point.f(x) @\n"),
        ("if", "f(x) = if x > 0 @ else { 0 };\n"),
        ("else", "f(x) = if x > 0 { 0 } else @;\n"),
        (
            "else if",
            "f(x) = if x > 0 { 0 } else if x < 0 { 1 } else @;\n",
        ),
        ("fallback", "f(x) = x else @;\n"),
        ("atom fallback", "f(x) = x else #none -> @;\n"),
        ("loop", "f(x) = loop @;\n"),
        ("labeled loop", "f(x) = loop t @;\n"),
        ("for", "f(xs) = for x in xs @;\n"),
        ("for where", "f(xs) = for x in xs where x > 0 @;\n"),
        ("match arm", "f(x) = match x { #a -> @, _ -> 0 };\n"),
        (
            "guarded arm",
            "f(x) = match x { n where n > 0 -> @, _ -> 0 };\n",
        ),
        ("lambda", "f(xs) = xs.map(x -> @);\n"),
        (
            "lambda with parameters",
            "f(xs) = xs.reduce((a, b) -> @);\n",
        ),
    ];
    // Displays: a set, a map, a record, a set with a trailing comma, a one-entry map whose key
    // is not a name, a one-field record, and the lone lambdas.
    let braces = [
        "{ 1, 2 }",
        "{ \"a\" -> 1, \"b\" -> 2 }",
        "{ x: 1, y: 2 }",
        "{ x, }",
        "{ \"a\" -> 1 }",
        "{ x: 1 }",
        "{ k -> 0 }",
        "{ (a, b) -> a }",
        "{ k -> v -> v }",
    ];
    let mut wrong = Vec::new();
    for (pos, text) in positions {
        for brace in braces {
            let src = text.replace('@', brace);
            if !display_in_body(&src) {
                wrong.push(format!("{pos}: {src:?} is not rejected: {:?}", built(&src)));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_parenthesized_display_or_a_real_block_is_accepted_in_each_body_position() {
    let positions = [
        "f(x) @\n",
        "f(x) = if x > 0 @ else { 0 };\n",
        "f(x) = if x > 0 { 0 } else @;\n",
        "f(x) = x else @;\n",
        "f(x) = x else #none -> @;\n",
        "f(x) = loop @;\n",
        "f(xs) = for x in xs @;\n",
        "f(x) = match x { #a -> @, _ -> 0 };\n",
        "f(xs) = xs.map(x -> @);\n",
    ];
    // A display in parentheses; a block with a `;`; a block of one expression that is not a
    // display; a block whose value is a lambda in parentheses or a tuple; a block that binds a
    // lambda and returns it; a display nested in a block; a brace after a display entry's
    // arrow, which its own contents classify.
    let braces = [
        "{ ({ 1, 2 }) }",
        "{ ({ k -> 0 }) }",
        "{ y = 1; y }",
        "{ x + 1 }",
        "{ (k -> 0) }",
        "{ (1, 2) }",
        "{ g = k -> 0; g }",
        "{ y = { 1, 2 }; y }",
        "{ { \"a\" -> {} } }",
    ];
    let mut wrong = Vec::new();
    for text in positions {
        for brace in braces {
            let src = text.replace('@', brace);
            if let Err(e) = built(&src) {
                wrong.push(format!("{src:?} is rejected: {e}"));
            }
        }
    }
    // Where an expression may stand in place of the brace, the display in parentheses alone.
    for src in [
        "f(x) = x else ({ 1, 2 });\n",
        "f(x) = x else #none -> ({ x: 1 });\n",
        "f(x) = match x { #a -> ({ k -> 0 }), _ -> ({}) };\n",
        "f(xs) = xs.map(x -> ({ x }));\n",
        "f(xs) = xs.map(x -> ({ x -> 1 }));\n",
    ] {
        if let Err(e) = built(src) {
            wrong.push(format!("{src:?} is rejected: {e}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_display_outside_body_position_is_not_rejected() {
    for src in [
        "s = { 1, 2 };\n",
        "m = { k -> 0 };\n",
        "r = { x: 1, y: 2 };\n",
        "f(x) = g({ 1, 2 }, { k -> 0 });\n",
        "f(x) = if x in { 1, 2 } { 1 } else { 0 };\n",
        "f(x) = { \"a\" -> { 1, 2 } };\n",
        "f(x) = [{ 1 }, { k -> 0 }];\n",
    ] {
        if let Err(e) = built(src) {
            panic!("{src:?} is rejected: {e}");
        }
    }
}
