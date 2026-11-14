//! The form rule `stage::ends` of `ends.rs` at `k` and `8k` levels: a shared part is read
//! once, so the time grows with the term's distinct parts, not its places. Each term is built
//! before the timing; `ends.rs` checks the answers at small sizes.

use zed_tests::scaling;
use zedc::stage::ends;

use crate::ends::{
    arms_calling_let_functions, built_into_freed_blocks, let_functions, mixed_levels_read,
    shared_arms_read, shared_arms_terms,
};

#[test]
fn a_chain_whose_if_arms_share_their_term_is_read_in_time_near_its_size() {
    // The walk read the term as a tree: 2^k steps.
    let n = 1000;
    let terms = scaling::inputs(n, shared_arms_terms);
    scaling::check("stage::ends on k levels of shared if arms", n, |k| {
        shared_arms_read(&terms[&k]);
    });
}

#[test]
fn many_let_functions_called_at_the_end_are_read_in_time_near_their_number() {
    let n = 1000;
    let terms = scaling::inputs(n, let_functions);
    scaling::check("stage::ends on k let functions called at the end", n, |k| {
        assert!(ends(&terms[&k]));
    });
}

#[test]
fn arms_that_call_different_let_functions_on_a_shared_part_are_read_in_time_near_their_size() {
    let n = 1000;
    let terms = scaling::inputs(n, arms_calling_let_functions);
    scaling::check(
        "stage::ends on k levels of arms calling let functions",
        n,
        |k| {
            assert!(ends(&terms[&k]));
        },
    );
}

#[test]
fn reading_a_term_built_into_freed_blocks_scales() {
    let n = 1000;
    let terms = scaling::inputs(n, built_into_freed_blocks);
    scaling::check(
        "stage::ends on k mixed levels of shared if arms built into freed blocks",
        n,
        |k| mixed_levels_read(&terms[&k]),
    );
}
