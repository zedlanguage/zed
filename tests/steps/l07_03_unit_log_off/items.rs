//! The unit item as syntax: it parses from layer L7, ahead of the reading of `@log` as an
//! annotation of the statement `(#off);`, builds, and formats back to its text.

use zedc::format::format;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

use super::build;

/// The statements of `text`, one s-expression per line.
fn shown(text: &str) -> String {
    let stmts = build(text);
    let lines: Vec<String> = stmts.iter().map(|s| s.to_string()).collect();
    lines.join("\n")
}

#[test]
fn the_unit_item_builds_apart_from_the_declarations() {
    assert_eq!(
        shown("@log(#off);\n\nmain(stdin: Lines) -> (stdout: Lines) {\n  stdout <- \"hi\";\n}\n"),
        "(unit (@log #off))\n\
         (def main ((stdin: Lines)) (-> (stdout: Lines)) (block (push stdout (str \"hi\"))))"
    );
    // `@log(#off)` before a definition annotates that definition, not the unit.
    assert_eq!(
        shown("@log(#off)\nquiet(x) = x;"),
        "(annotated (@log #off) (def quiet (x) = x))"
    );
    // Any annotation followed by `;` alone is the unit item; resolution says which are.
    assert_eq!(shown("@strict;"), "(unit @strict)");
    assert_eq!(shown("@log(#on);"), "(unit (@log #on))");
    assert_eq!(shown("@log;"), "(unit @log)");
}

#[test]
fn below_layer_l7_the_text_is_not_the_unit_item() {
    let text = "@log(#off);";
    let tokens = lex(text).unwrap();
    let names = |ring: u32| {
        let tree = parse(text, &tokens, "Unit", ring).unwrap();
        (0..tree.nodes.len())
            .map(|n| tree.name(n).to_string())
            .collect::<Vec<_>>()
    };
    assert!(names(7).contains(&"UnitAnnot".to_string()));
    assert!(names(TOP).contains(&"UnitAnnot".to_string()));
    // At L6 an expression statement exists, and `@log` annotates `(#off);`; resolution then
    // refuses `@log` as an annotation of layer L7.
    let six = names(6);
    assert!(!six.contains(&"UnitAnnot".to_string()));
    assert!(six.contains(&"Annotated".to_string()));
    // Below L6 the text does not parse at all.
    assert!(parse(text, &tokens, "Unit", 5).is_err());
}

#[test]
fn the_unit_item_formats_to_its_text() {
    let cases = [
        ("@log( #off ) ;\nf(x)=x;", "@log(#off);\nf(x) = x;\n"),
        (
            "// No log lines from this unit.\n@log(#off);\n\nf(x) = x;\n",
            "// No log lines from this unit.\n@log(#off);\n\nf(x) = x;\n",
        ),
        ("@strict ;", "@strict;\n"),
    ];
    for (text, want) in cases {
        let tokens = lex(text).unwrap();
        let stmts = build(text);
        assert_eq!(format(text, &tokens, &stmts), want, "formatting {text:?}");
    }
}

#[test]
fn the_unit_item_needs_its_semicolon() {
    for text in ["@log(#off)", "@log(#off)\n", "@log(#off) @strict;"] {
        let tokens = lex(text).unwrap();
        assert!(
            parse(text, &tokens, "Unit", TOP).is_err(),
            "{text:?} parses"
        );
    }
}
