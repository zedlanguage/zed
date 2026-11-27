//! The array, set and map displays are of layer L1 (DESIGN.md step L1.16; plan row
//! LAYER-audit-open, item F, decided F1): a value L1 prints, as the set in `#errs({#a, #b})`
//! of step L1.18, must parse at the layer that prints it, since printed types are syntax.

use zedc::ast::unit;
use zedc::lex::lex;
use zedc::parse::parse;

use super::value;

/// The statements of `text` parsed at ring L1, one s-expression per line, or `syntax`.
fn sx_at_l1(text: &str) -> String {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Unit", 1) {
        Err(_) => "syntax".into(),
        Ok(tree) => unit(text, &tokens, &tree)
            .unwrap_or_else(|e| panic!("{text}: {e}"))
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

#[test]
fn each_display_parses_at_l1_as_a_display_and_gives_its_family() {
    for (text, want) in [
        ("f(x) = [1, 2];", "(def f (x) = (array 1 2))"),
        ("f(x) = [];", "(def f (x) = (array))"),
        ("f(x) = { 1, x };", "(def f (x) = (set 1 x))"),
        // One member: at L1 this was a block giving `x` before the displays moved down.
        ("f(x) = { x };", "(def f (x) = (set x))"),
        (
            "f(x) = { 1 -> \"a\", x -> \"b\" };",
            "(def f (x) = (map (-> 1 (str \"a\")) (-> x (str \"b\"))))",
        ),
        ("f(x) = {};", "(def f (x) = (map))"),
        // Only the record display `{ n: e }` keeps layer L2 (Display#0).
        ("f(x) = { a: 1 };", "syntax"),
    ] {
        assert_eq!(sx_at_l1(text), want, "{text}");
    }
    assert_eq!(value("xs = [1, 2];\n", "xs"), "{0 -> 1, 1 -> 2}");
    // A family mapping each key to itself prints by its members, as `#errs` prints its set.
    assert_eq!(value("s = {#a, #b};\n", "s"), "{#a, #b}");
    assert_eq!(value("m = {1 -> 2};\n", "m"), "{1 -> 2}");
    assert_eq!(value("e = {};\n", "e"), "{}");
}
