//! Edges of the parser's recovery (step L1.29d): the note on a bracket still open names the token
//! the parse stopped at, written as the program writes it, unless that text holds a line break
//! or backticks of its own; and a grammar whose `Unit` does not end in `END` (read with
//! `parse_with`) is recovered declaration by declaration too.

use zedc::ast::unit_all_errors;
use zedc::lex::lex;
use zedc::parse::{Error, Grammar, TOP, parse, parse_unit, parse_with};

fn error(text: &str) -> Error {
    let tokens = lex(text).unwrap();
    parse(text, &tokens, "Unit", TOP).expect_err(text)
}

/// The note on the open bracket of each unit.
#[test]
fn an_open_bracket_names_where_the_parse_stops() {
    let cases = [
        ("x = (1 2;", "`(` opens here and is still open at `2`"),
        (
            "x = (1 \"a`b\";",
            "`(` opens here and is still open where the parse stops",
        ),
        (
            "x = (1 \"a`b`c\";",
            "`(` opens here and is still open where the parse stops",
        ),
        (
            "x = (1 \"\"\"\n  ab\n  \"\"\";",
            "`(` opens here and is still open where the parse stops",
        ),
    ];
    for (text, want) in cases {
        let e = error(text);
        let notes: Vec<&str> = e.recovery.notes.iter().map(|n| n.1.as_str()).collect();
        assert!(notes.contains(&want), "{text:?}\n{notes:?}");
    }
}

/// `Unit = Item*` with no `END`: the declaration with a second `a` is refused there, `;`
/// expected, and repaired by the `;` inserted or the `a` deleted; it defines no name.
#[test]
fn a_unit_rule_with_no_end_is_recovered_too() {
    let g = Grammar::read(&["Unit = Item* L1\nItem = 'a' ';' L1\nExpr = 'a' L1\n"]).unwrap();
    let text = "a; a a;";
    let tokens = lex(text).unwrap();
    let e = parse_with(&g, text, &tokens, "Unit", 1).expect_err(text);
    assert_eq!((e.span.start, e.span.end), (5, 6));
    assert_eq!(e.expected, ["';'"]);
    assert_eq!(e.recovery.notes[0].1, "the declaration begins here");
    let repairs: Vec<&str> = e.recovery.repairs.iter().map(|r| r.1.as_str()).collect();
    assert_eq!(repairs, ["a; a; a;", "a; a ;"]);
    assert!(e.recovery.defines.is_empty());
    let text = "a;";
    let tokens = lex(text).unwrap();
    assert!(parse_with(&g, text, &tokens, "Unit", 1).is_ok());
}

/// A declaration that parses, `f(…) = x + "${x}".len;`, whose second line begins at the first
/// column, followed on that line by a token that fails, `)`: the failing declaration begins at
/// that line (`begins_at`), inside the one that parsed. The one that parsed is then part of the
/// failing one, so its string hole is skipped with it, and the hole of `h` below is built from
/// its own tree. Before the fix the declaration of `f` was kept with its hole while the builder
/// skipped the hole's token, so the holes were counted against the wrong trees and the build
/// stopped at "a hole's expression is taken once" (proofdoc3a, 2026-11-20).
#[test]
fn a_declaration_kept_up_to_a_failing_line_inside_it_is_skipped_with_it() {
    let text =
        "f(positional x: int) = x +\n\"${x}\".len; )\n\nh(positional y: int) = \"${y * 2}\";\n";
    let tokens = lex(text).unwrap();
    let (tree, errors) = parse_unit(text, &tokens, TOP);
    assert_eq!(errors.len(), 1, "{errors:?}");
    // The 15 tokens of the first two lines, from `f` to `)`.
    assert_eq!(tree.skipped, vec![0..15_usize]);
    // `f` once from the declaration parsed alone and once as the declaration dropped; the
    // front end reads the names as a set (`front::Broken::defines`).
    assert!(errors[0].recovery.defines.iter().all(|n| n == "f"));
    assert!(!errors[0].recovery.defines.is_empty());
    let stmts = unit_all_errors(text, &tokens, &tree).unwrap();
    let shown = format!("{stmts:?}");
    assert_eq!(stmts.len(), 1, "{shown}");
    assert!(
        shown.contains("\"y\"") && !shown.contains("\"x\""),
        "{shown}"
    );
}
