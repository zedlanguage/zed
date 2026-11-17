//! Placing each `break;` and marking the paths of a statement whose blocks may export nothing
//! are linear in the size of the unit (one walk of the tree each, on first use). Each input is
//! lexed and parsed before timing, so the work measured is building, resolving and dropping.

use std::collections::HashMap;

use zed_tests::scaling;

use crate::breaks::{nested_breaks, nested_exports};
use crate::scaling::{Parsed, parsed, pass};

/// Checks that building and resolving `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect();
    scaling::check(what, base, |n| pass(&units[&n], false));
}

#[test]
fn nested_loops_each_with_a_break_scale() {
    linear("n nested loops, each with a `break;`", 1000, nested_breaks);
}

#[test]
fn nested_blocks_that_export_nothing_scale() {
    linear(
        "n blocks nested in exports, in statement position",
        1000,
        nested_exports,
    );
}
