//! The formatter at the rule of low complexity (DESIGN.md Part G).

use std::collections::HashMap;

use zed_tests::scaling;

/// `f(c) = if c { if c { … { a = 1; a } … } else { 0 } } else { 0 };`, nested `depth` deep.
fn nested(depth: usize) -> String {
    format!(
        "f(c) = {}{{ a = 1; a }}{};\n",
        "if c { ".repeat(depth) + "if c ",
        " else { 0 }".to_string() + &" } else { 0 }".repeat(depth),
    )
}

#[test]
fn nested_one_statement_blocks_scale() {
    // A block of one statement written on several lines was rendered once to try one line and
    // again on its own lines, so `d` such blocks nested cost `2^d` renders (8 s at `d = 20`).
    // Each level is indented, so the text itself has `d²` characters.
    let units: HashMap<usize, String> = [100, 800].into_iter().map(|d| (d, nested(d))).collect();
    scaling::check_order("nested one-statement blocks, by depth", 100, 2, |d| {
        zedc::format::format_source(units[&d].as_bytes()).unwrap();
    });
    let out = zedc::format::format_source(nested(1).as_bytes()).unwrap();
    assert_eq!(
        out,
        "f(c) = if c {\n  if c {\n    a = 1;\n    a\n  } else { 0 }\n} else { 0 };\n"
    );
}

/// `n` statements, each with four comments on their own lines before it and one after it.
fn commented(n: usize) -> String {
    (0..n)
        .map(|i| format!("// a\n// b\n// c\n// d\na{i} = {i}; // a{i}\n"))
        .collect()
}

#[test]
fn many_comments_scale() {
    // Each statement's comments were found by a scan over every comment of the unit.
    scaling::check("statements with comments, by count", 500, |n| {
        zedc::format::format_source(commented(n).as_bytes()).unwrap();
    });
    let out = zedc::format::format_source(commented(2).as_bytes()).unwrap();
    assert_eq!(out, commented(2));
}

/// `n` statements, each a call with a sort key and two comments inside, which move to its end,
/// then a blank line, a leading comment, another blank line and the next statement.
fn moved(n: usize) -> String {
    (0..n)
        .map(|i| format!("a{i} = sort(xs, // by\n  desc x -> x, // key\n  {i});\n\n// next\n\n"))
        .collect()
}

#[test]
fn moved_comments_with_blank_lines_scale() {
    // Each blank line is found by a scan of the text between two neighboring comments, or a
    // comment and its statement, so the scans cover disjoint ranges.
    let units: HashMap<usize, String> = [500, 4000].into_iter().map(|n| (n, moved(n))).collect();
    scaling::check_order("moved comments with blank lines, by count", 500, 1, |n| {
        zedc::format::format_source(units[&n].as_bytes()).unwrap();
    });
    let out = zedc::format::format_source(moved(1).as_bytes()).unwrap();
    assert_eq!(
        out,
        "a0 = sort(xs, desc x -> x, 0); // by\n// key\n\n// next\n"
    );
}
