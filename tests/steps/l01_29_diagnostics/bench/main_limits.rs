//! `n` powers, and `n` products of powers, past the memory limit of `main`, at `n` and `8n`
//! (`main_limits.rs`).

use zed_tests::scaling;

use crate::main_limits::{
    powers, powers_past_the_memory_limit_rejected, products,
    products_past_the_memory_limit_rejected,
};

#[test]
fn rejecting_many_products_past_the_memory_limit_scales() {
    // Each product costs about 130 ms (measured 2026-11-23 on a Colab VM, natively: 1.30 s at
    // 10 products, 10.6 s at 80; not profiled), so `n` is kept small for the run to stay within
    // a minute.
    let n = 4;
    let srcs = scaling::inputs(n, products);
    scaling::check(
        "n products past the memory limit of main, each offering a smaller power operand",
        n,
        |k| {
            products_past_the_memory_limit_rejected(&srcs[&k], k);
        },
    );
}

#[test]
fn rejecting_many_powers_past_the_memory_limit_scales() {
    // At n = 360 the run took 171 s on a Colab VM (b22-checkrest10, 2026-11-23), about 53 ms a
    // power over the 3240 powers of the runs at n and 8n, past the 60 s a piece may take
    // (BENCH-powers-over-60s); n = 80 runs 720 powers.
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
