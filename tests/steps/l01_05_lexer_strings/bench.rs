//! The lexing of strings at the rule of low complexity (DESIGN.md Part G): the benchmarks of
//! this step, run by `tools/run_tests.sh --bench`. `scaling.rs` makes each of their checks at
//! small sizes.

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::lex::lex;

use super::parts;
use super::scaling::{lines, nested, one_line_holes};

#[test]
fn a_long_indented_string_scales() {
    // Each character was tested against every line's cut of indentation.
    scaling::check("a \"\"\" string of n lines", 1000, |n| {
        assert_eq!(parts(&lines(n)).len(), 2 * n);
    });
}

#[test]
fn nested_holes_scale() {
    // Each hole was scanned for its `}` once for each hole around it, and its text searched
    // for a line break as many times.
    let texts: HashMap<usize, String> = [2_000, 16_000]
        .into_iter()
        .map(|d| (d, nested(d)))
        .collect();
    scaling::check("a string with holes nested d deep", 2_000, |d| {
        assert_eq!(lex(&texts[&d]).unwrap().len(), 1);
    });
}

#[test]
fn one_line_holes_with_comments_and_strings_scale() {
    // Each block comment and inner string is checked for a line break by a search in the
    // text's line breaks, not by a pass over them.
    let texts: HashMap<usize, String> = [4_000, 32_000]
        .into_iter()
        .map(|n| (n, one_line_holes(n)))
        .collect();
    scaling::check_order("n lines of one-line strings with holes", 4_000, 1, |n| {
        assert_eq!(lex(&texts[&n]).unwrap().len(), n);
    });
}
