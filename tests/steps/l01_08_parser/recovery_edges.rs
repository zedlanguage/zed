//! Edges of the parser's recovery (step L1.29d): the note on a bracket still open names the token
//! the parse stopped at, written as the program writes it, unless that text holds a line break
//! or backticks of its own; and a grammar whose `Unit` does not end in `END` (read with
//! `parse_with`) is recovered declaration by declaration too.

use zedc::lex::lex;
use zedc::parse::{Error, Grammar, TOP, parse, parse_with};

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
