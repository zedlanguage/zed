//! A form the parser reads and this zedc does not support is named for what it is: only `><`
//! reduces (sec:reduction); a sort key in a remap's pattern is of step L8.1; `with f(…)` and
//! `without f(…)` attach and drop a facet (sec:facets); `m[day: 1]` is a named slice
//! (sec:level_names).

use zedc::ast::build;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// The message for the expression `text`, and the text its span covers.
fn later(text: &str) -> (String, &str) {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Expr", TOP).unwrap();
    let e = build(text, &tokens, &tree).unwrap_err();
    (e.message, &text[e.span.start..e.span.end])
}

#[test]
fn each_form_is_named_for_what_it_is() {
    for (text, message, at) in [
        // A remap builds (tests/steps/l08_01_remap_run); a sort key in its pattern is of L8.1.
        (
            "m into (desc s -> n -> s)",
            zed_tests::not_yet!("the sort key `desc s`"),
            "desc s",
        ),
        (
            "x with units(\"m\")",
            zed_tests::not_yet!("the facet attachment `with units(\"m\")`"),
            "with units(\"m\")",
        ),
        (
            "x without units(\"m\")",
            zed_tests::not_yet!("the facet removal `without units(\"m\")`"),
            "without units(\"m\")",
        ),
        (
            "m[day: 1]",
            zed_tests::not_yet!("the named slice `day: 1`"),
            "day: 1",
        ),
        (
            "x >< f unordered",
            zed_tests::not_yet!("the reduction order `unordered`"),
            "unordered",
        ),
    ] {
        assert_eq!(later(text), (message.to_string(), at), "{text}");
    }
}
