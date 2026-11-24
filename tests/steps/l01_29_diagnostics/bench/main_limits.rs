//! `n` powers, and `n` products of powers, past the memory limit of `main`, at `n` and `8n`
//! (`main_limits.rs`).

use zed_tests::scaling;

use crate::main_limits::{
    powers, powers_past_the_memory_limit_rejected, products,
    products_past_the_memory_limit_rejected,
};

#[test]
fn rejecting_many_products_past_the_memory_limit_scales() {
    // With operands of 4.2 Mbit each product cost about 130 ms (b22-checkrest10, 2026-11-23),
    // all of it multiplication of the numbers the line fixes, and `n` was 4; `products` now
    // builds operands 16 times smaller (PERF-products-bench-native-cost). At n = 40 the run at
    // 8n took 6.75 s, about 21 ms a product, and the instruction ratio was 8.456 (v5e4,
    // b22-checkrest12, 2026-11-24).
    let n = 40;
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
