//! Building blocks is of order n log n in the length of the text, and the depth of their
//! nesting is bounded by memory alone (DESIGN.md Part G). Each text is lexed and parsed before
//! timing, so the checks time the building alone. The benchmarks of this step, run by
//! `tools/run_tests.sh --bench`; `scaling.rs` builds each of their trees at small sizes.

use std::collections::HashMap;

use zed_tests::scaling::{check, inputs};
use zed_tests::trees::parsed;

use super::scaling::{Case, LONG_BLOCK, NESTED_BLOCKS, Parsed, builds};

/// The texts of `case` at `n` and `8n`, lexed and parsed before any run is timed.
fn trees(case: &Case, n: usize) -> HashMap<usize, Parsed> {
    inputs(n, |m| parsed((case.text)(m), "Expr"))
}

#[test]
fn a_long_block_scales() {
    let built = trees(&LONG_BLOCK, 200);
    check("building a block of n statements", 200, |n| {
        builds(&LONG_BLOCK, &built[&n], n)
    });
}

#[test]
fn nested_blocks_scale() {
    let built = trees(&NESTED_BLOCKS, 200);
    check("building blocks nested n deep", 200, |n| {
        builds(&NESTED_BLOCKS, &built[&n], n)
    });
}
