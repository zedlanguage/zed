//! Naming a primitive in a refusal at the rule of low complexity. The input is built in
//! `prim_names.rs`, whose test checks the refusal at a small size.

use zed_tests::scaling::{check_order, inputs};

use super::super::prim_names::{key_path_step_under_calls, type_error};

/// The refusal of a step on key paths looks down the calls running for the one that generated
/// it, once: under n and 8n calls of `y -> y` and no `reindex`, the whole run, the walk to the
/// bottom included, grows as n.
#[test]
fn naming_the_call_of_a_key_path_step_scales_with_the_depth() {
    // About 0.65 µs and 360 bytes a call: 1x about 0.32 s, 1.4 GB at 8n, 10 s in all.
    let n = 500_000;
    let built = inputs(n, key_path_step_under_calls);
    check_order("a key path step refused under n calls", n, 1, |n| {
        type_error(&built[&n]);
    });
}
