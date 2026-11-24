//! `n` powers past the memory limit of `main`, at `n` and `8n` (`main_limits.rs`).

use zed_tests::scaling;

use crate::main_limits::{powers, powers_past_the_memory_limit_rejected};

#[test]
fn rejecting_many_powers_past_the_memory_limit_scales() {
    // At n = 360 the run took 171 s on a Colab VM (b22-checkrest10, 2026-11-23), about 53 ms a
    // power over the 3240 powers of the runs at n and 8n, past the 60 s a piece may take
    // (BENCH-powers-over-60s); n = 80 runs 720 powers. At n = 80 the piece took 43 s
    // (FAIL-powers-bench-43s): each line's repair folded the same trial powers `b ^ (2^j)`
    // again; folded once a check (`Ck::shrunk_power_fits`), the piece took 6.6 s and the run
    // at 8n 4.2 s, instruction ratio 5.166 (v5e3, b22-checkrest13, 2026-11-24). The ratio is
    // below 8 because the trial powers, a fixed cost, are now paid once a run.
    let n = 80;
    let srcs = scaling::inputs(n, powers);
    scaling::check(
        "n powers past the memory limit of main, each rejected",
        n,
        |k| {
            powers_past_the_memory_limit_rejected(&srcs[&k], k);
        },
    );
}
