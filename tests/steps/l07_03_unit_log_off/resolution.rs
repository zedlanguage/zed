//! Resolution accepts `@log(#off);` at a unit's top level and records where it is; it refuses
//! each other unit item with its reason.

use zedc::lex::Span;

use super::resolved;

#[test]
fn the_unit_item_is_recorded_on_the_resolution() {
    let text = "/// Doubles.\ntwice(x) = 2 * x;\n\n@log(#off);\n";
    let r = resolved(text).unwrap();
    let start = text.find("@log").unwrap();
    assert_eq!(
        r.log_off,
        Some(Span {
            start,
            end: start + "@log(#off);".len()
        })
    );
    // The doc comment still documents `twice`, and the unit item is no declaration.
    assert!(r.decls.contains(&text.find("twice").unwrap()));
    assert!(!r.decls.contains(&start));
    assert_eq!(resolved("twice(x) = 2 * x;").unwrap().log_off, None);
}

#[test]
fn every_other_unit_item_is_refused_with_its_reason() {
    let cases: &[(&str, &str)] = &[
        (
            "@log(#on);\nf(x) = x;",
            "1:1: the unit item `@log` takes the one argument `#off`, as in `@log(#off);`, \
             which drops the lines of every body in the unit",
        ),
        (
            "@log(#off, #on);\nf(x) = x;",
            "1:1: the unit item `@log` takes the one argument `#off`, as in `@log(#off);`, \
             which drops the lines of every body in the unit",
        ),
        (
            "@log(mode: #off);\nf(x) = x;",
            "1:1: the unit item `@log` takes the one argument `#off`, as in `@log(#off);`, \
             which drops the lines of every body in the unit",
        ),
        (
            "@log();\nf(x) = x;",
            "1:1: the unit item `@log` takes the one argument `#off`, as in `@log(#off);`, \
             which drops the lines of every body in the unit",
        ),
        (
            "@log;\nf(x) = x;",
            "1:1: `@log;` is not a unit item: `@log` writes a line at each evaluation of the \
             definition or statement it annotates, and the unit item `@log(#off);` drops the \
             lines of every body in the unit",
        ),
        (
            "f(x) {\n  @log(#off);\n  x\n}",
            "2:3: `@log(#off);` is an item of a unit and stands at its top level, not in a \
             block; write `@log(#off)` before a function's declaration to drop the lines of \
             its body",
        ),
        (
            "@memoized;\nf(x) = x;",
            "1:1: `@memoized` annotates a declaration and is not a unit item; write it before \
             the declaration it annotates",
        ),
        (
            "@fused (a + b);\nf(x) = x;",
            "1:1: `@fused` annotates a declaration and is not a unit item; write it before \
             the declaration it annotates",
        ),
        ("@strict;\nf(x) = x;", "1:1: `@strict` is not an annotation"),
        ("@quiet;\nf(x) = x;", "1:1: `@quiet` is not an annotation"),
    ];
    for &(text, want) in cases {
        assert_eq!(resolved(text).unwrap_err(), [want], "resolving {text:?}");
    }
}

#[test]
fn a_unit_has_the_item_once() {
    let text = "@log(#off);\nf(x) = x;\n@log(#off);\n";
    assert_eq!(
        resolved(text).unwrap_err(),
        ["3:1: the unit has `@log(#off);` twice; note 1:1: the first `@log(#off);`"]
    );
}
