//! Writing the text of nested atom patterns, and of lambdas nested in their parameters'
//! defaults, is of order n in its length (DESIGN.md Part G): the benchmark of `scaling.rs`,
//! whose test writes each text at small sizes.

use zed_tests::scaling;

use crate::scaling::{nested, texts_hold};

#[test]
fn the_text_of_nested_patterns_and_lambdas_scales() {
    let built = scaling::inputs(250, nested);
    scaling::check(
        "the text of nested patterns and lambdas, by depth",
        250,
        |n| {
            let (pattern, lambda) = &built[&n];
            texts_hold(pattern, lambda, n);
        },
    );
}
