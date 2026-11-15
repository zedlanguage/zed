//! Helpers of the source-level remap tests: the `sales` map of sec:level_names, and checks
//! that compare a definition's value with a display the spec writes, or a rejection's text
//! with the spec's message.

use zed_tests::step_helpers::l01_16_elaboration::{errors, value};

/// `sales` of DESIGN.md sec:level_names without its declared type `Sales`, whose level names
/// need step L7.1b: the values and the levels are the same. The tests that read the names
/// wait in /home/luke/Work/wt/failing-tests (rows L7.1b, L8.2b, L8.2c).
pub const SALES: &str = "sales = { \"east\" -> [{ \"B7\" -> 5 }], \"west\" -> [{ \"A12\" -> 3, \"B7\" -> 1 }, { \"A12\" -> 2 }] };\n";

/// `src` with `sales` declared before it.
pub fn with_sales(src: &str) -> String {
    format!("{SALES}{src}")
}

/// The value of `got` in `src` is the value of `want`, a display the spec writes, and is not
/// an evaluation error.
pub fn same(src: &str, got: &str, want: &str) {
    let g = value(src, got);
    assert!(!g.starts_with("error"), "{src}\n{got} = {g}");
    assert_eq!(g, value(src, want), "{src}");
}

/// The value of `name` in `src`, printed, is `want`.
pub fn prints(src: &str, name: &str, want: &str) {
    assert_eq!(value(src, name), want, "{src}");
}

/// The errors of `src`, from name resolution where it rejects the unit, else from the checker
/// and the elaborator, each as `message menu [text]`.
pub fn all_errors(src: &str) -> Vec<String> {
    let tokens = zedc::lex::lex_fence(src).unwrap();
    let tree = zedc::parse::parse(src, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(src, &tokens, &tree).unwrap();
    match zedc::resolve::resolve_text(&stmts, Some(src)) {
        Err(es) => es
            .iter()
            .map(|e| {
                format!(
                    "{}{} [{}]",
                    e.message,
                    e.menu,
                    &src[e.span.start..e.span.end]
                )
            })
            .collect(),
        Ok(_) => errors(src),
    }
}

/// `src` is rejected, and the text of its errors holds each of `needles`.
pub fn rejected(src: &str, needles: &[&str]) {
    let es = all_errors(src).join("\n");
    for n in needles {
        assert!(es.contains(n), "{src}\nmissing {n:?} in:\n{es}");
    }
}

/// `src` does not parse: the grammar of sec:grammar has no rule that reads it.
pub fn does_not_parse(src: &str) {
    let tokens = zedc::lex::lex_fence(src).unwrap();
    let tree = zedc::parse::parse(src, &tokens, "Unit", zedc::parse::TOP);
    assert!(tree.is_err(), "{src}: parsed");
}
