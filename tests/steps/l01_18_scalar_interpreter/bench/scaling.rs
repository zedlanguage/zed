//! The scalar tier at the rule of low complexity (DESIGN.md Part G). The inputs are built in
//! `scaling.rs`, whose tests check their results at a small size.

use zed_tests::scaling::{check, check_order};
use zed_tests::step_helpers::l01_16_elaboration::value;

use super::super::scaling::{chain_of_failures, evaluated, f32_chain};

#[test]
fn a_chain_of_n_failures_merging_scales() {
    // Each `+` merged the failures so far with one more by copying them into a new set. The
    // chain is a kernel term, so that only the evaluator is timed; it nests n deep, past the
    // default thread stack. About 5 µs and 10 KB a link: 1x about 0.2 s, 3.3 GB at 8n.
    let n = 40_000;
    check("n failures merged by a chain of `+`", n, |n| {
        evaluated(&chain_of_failures(n));
    });
}

#[test]
fn checking_and_running_a_chain_of_f32_arithmetic_scales() {
    // About 0.29 ms and 0.27 MB a binding: 1x about 0.29 s, 2.2 GB at 8n.
    let n = 1000;
    let srcs: std::collections::HashMap<usize, String> =
        [n, 8 * n].into_iter().map(|n| (n, f32_chain(n))).collect();
    check_order("a chain of n f32 bindings", n, 1, |n| {
        value(&srcs[&n], "x");
    });
}
