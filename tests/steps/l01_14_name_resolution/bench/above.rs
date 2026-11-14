//! Checking that each name is defined above its uses is linear in the block or list: the
//! benchmark of `above.rs`, whose test resolves the same chains at small sizes.

use zedc::resolve::resolve_text;

use crate::above::{chain_errors, chains, reports};

#[test]
fn checking_the_order_of_a_block_or_a_list_scales() {
    // Complexity tradeoff (COMPLEXITY.md F16b): each use compares its binder's position in
    // O(1); rescanning the block for each use was O(uses × bindings).
    let n = 20_000;
    let built = zed_tests::scaling::inputs(n, chains);
    for (k, (what, errors)) in chain_errors(n).into_iter().enumerate() {
        let (text, stmts) = &built[&n][k];
        reports(text, stmts, what, errors);
        zed_tests::scaling::check(what, n, |m| {
            let (text, stmts) = &built[&m][k];
            let _ = resolve_text(stmts, Some(text));
        });
    }
}
