//! `n` powers past the memory limit of `main`, at `n` and `8n` (`main_limits.rs`).

use zed_tests::scaling;

use crate::main_limits::{powers, powers_past_the_memory_limit_rejected};

#[test]
fn rejecting_many_powers_past_the_memory_limit_scales() {
    let n = 360;
    let srcs = scaling::inputs(n, powers);
    scaling::check(
        "n powers past the memory limit of main, each rejected",
        n,
        |k| {
            powers_past_the_memory_limit_rejected(&srcs[&k], k);
        },
    );
}
