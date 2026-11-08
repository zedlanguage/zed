//! The unit item as syntax: it parses from layer L7, and an annotation followed by `;` is never
//! an annotation of a statement at any layer; it builds and formats back to its text.

use zedc::ast::unit;
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
         (def main ((stdin: Lines)) (-> (stdout: Lines)) (block (<- stdout (str \"hi\"))))"
    );
    // `@log(#off)` before a definition annotates that definition, not the unit.
    assert_eq!(
        shown("@log(#off)\nquiet(x) = x;"),
        "(annotated (@log #off) (def quiet (x) = x))"
    );
    // Any annotation followed by `;` alone is the unit item; resolution says which are.
    assert_eq!(shown("@exact;"), "(unit @exact)");
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
    // An annotation followed by `;` is never `@log` on the statement `(#off);`, at any layer,
    // so a unit's tree does not change between layers: below L7 the text does not parse.
    for ring in 1..7 {
        assert!(
            parse(text, &tokens, "Unit", ring).is_err(),
            "parses at L{ring}"
        );
    }
}

#[test]
fn an_annotation_before_a_parenthesized_statement_keeps_its_reading() {
    // `@fused` annotates `(a + b).map(f);`, at L6 as at every layer above it.
    let text = "@fused (a + b).map(f);";
    let tokens = lex(text).unwrap();
    let at = |ring: u32| {
        let tree = parse(text, &tokens, "Unit", ring).unwrap();
        unit(text, &tokens, &tree).unwrap()[0].to_string()
    };
    assert_eq!(at(6), at(TOP));
    assert_eq!(at(6), "(annotated @fused (do (call (. (+ a b) map) f)))");
    // `@fused (a + b);` is the unit item, which resolution refuses for `@fused`.
    assert_eq!(shown("@fused (a + b);"), "(unit (@fused (+ a b)))");
    assert!(
        parse(
            "@fused (a + b);",
            &lex("@fused (a + b);").unwrap(),
            "Unit",
            6
        )
        .is_err()
    );
}

#[test]
fn the_unit_item_formats_to_its_text() {
    let cases = [
        ("@log( #off ) ;\nf(x)=x;", "@log(#off);\nf(x) = x;\n"),
        (
            "// No log lines from this unit.\n@log(#off);\n\nf(x) = x;\n",
            "// No log lines from this unit.\n@log(#off);\n\nf(x) = x;\n",
        ),
        ("@exact ;", "@exact;\n"),
    ];
    for (text, want) in cases {
        let tokens = lex(text).unwrap();
        let stmts = build(text);
        assert_eq!(format(text, &tokens, &stmts), want, "formatting {text:?}");
    }
}

#[test]
fn the_unit_item_needs_its_semicolon() {
    for text in ["@log(#off)", "@log(#off)\n", "@log(#off) @exact;"] {
        let tokens = lex(text).unwrap();
        assert!(
            parse(text, &tokens, "Unit", TOP).is_err(),
            "{text:?} parses"
        );
    }
}
