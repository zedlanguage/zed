//! The formatter at the rule of low complexity (DESIGN.md Part G): the benchmarks of
//! `scaling.rs`, whose test formats each of their units at small sizes.

use zed_tests::scaling;

use crate::scaling::{commented, formats, mixed, moved, nested, rejects};

#[test]
fn nested_one_statement_blocks_scale() {
    // A block of one statement written on several lines was rendered once to try one line and
    // again on its own lines, so `d` such blocks nested cost `2^d` renders (8 s at `d = 20`).
    // Each level is indented, so the text itself has `d²` characters.
    let units = scaling::inputs(100, nested);
    scaling::check_order("nested one-statement blocks, by depth", 100, 2, |d| {
        formats(&units[&d]);
    });
}

#[test]
fn many_comments_scale() {
    // Each statement's comments were found by a scan over every comment of the unit.
    let units = scaling::inputs(500, commented);
    scaling::check("statements with comments, by count", 500, |n| {
        formats(&units[&n]);
    });
}

#[test]
fn moved_comments_with_blank_lines_scale() {
    // Each blank line is found by a scan of the text between two neighboring comments, or a
    // comment and its statement, so the scans cover disjoint ranges.
    let units = scaling::inputs(500, moved);
    scaling::check_order("moved comments with blank lines, by count", 500, 1, |n| {
        formats(&units[&n]);
    });
}

#[test]
fn a_unit_with_many_syntax_errors_is_reported_in_time_linear_in_them() {
    // `zedc fmt` prints every error of the syntax, each with its step and the source line it
    // stands on, as `zedc run` does (FIX-fmt-parse-notes); each error is written once into the
    // report, so n errors print O(n) characters.
    let units = scaling::inputs(500, mixed);
    scaling::check_order("a unit's syntax errors, by count", 500, 1, |n| {
        rejects(&units[&n]);
    });
}
