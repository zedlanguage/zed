//! Checking that each name is defined above its uses is linear in the block or list: the
//! benchmark of `above.rs`, whose test resolves the same chains at small sizes.

use zedc::resolve::resolve_text;

use crate::above::{chain, chain_errors, reports};

/// Complexity tradeoff (COMPLEXITY.md F16b): each use compares its binder's position in O(1);
/// rescanning the block for each use was O(uses × bindings).
///
/// One test for each chain of `above::chains` (TEST-split-chkbub1-long). Until then the three
/// were one test, which took 40 s at load 39 and 27.7 s at load 17 in main-watch's runs of
/// 2026-11-21 and 61.6 s alone at load 71, while its three measured runs at n and 8n added up
/// to 4.1 s: the test built all three chains at both sizes, three texts of up to 160,000 lines
/// lexed and parsed, and on a count of instructions the run at 8n of each check runs in a new
/// process of the test binary that runs the test from its start, so the builds ran in four
/// processes, and the earlier checks were replayed there (`scaling::compare_by`). Now each
/// test builds only its own chain, in two processes. The chains, sizes and checks are as
/// before.
mod checking_the_order_of_a_block_or_a_list_scales {
    use super::*;

    /// The chain at place `k` of `above::chains`, which must be the one `chain_errors` names
    /// `what`, at n 20,000 and 8n: its errors at n checked first, then its resolution timed. The
    /// length 3 is the number of tests below: a chain added to `chain_errors` changes it, and
    /// this fails to compile until the chain has a test of its own.
    fn case(k: usize, what: &str) {
        let n = 20_000;
        let kinds: [_; 3] = chain_errors(n);
        let (name, errors) = kinds[k];
        assert_eq!(name, what, "chain_errors(n)[{k}]");
        let built = zed_tests::scaling::inputs(n, |m| chain(m, k));
        let (text, stmts) = &built[&n];
        reports(text, stmts, what, errors);
        zed_tests::scaling::check(what, n, |m| {
            let (text, stmts) = &built[&m];
            let _ = resolve_text(stmts, Some(text));
        });
    }

    #[test]
    fn a_block_in_order() {
        case(0, "a block of n bindings in order");
    }

    #[test]
    fn a_block_with_each_binding_used_above_it() {
        case(1, "a block of n bindings each used above it");
    }

    #[test]
    fn a_parameter_list_with_each_default_naming_a_later_one() {
        case(2, "a parameter list of n defaults each naming a later one");
    }
}
