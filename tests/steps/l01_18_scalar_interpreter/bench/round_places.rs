//! `allocate` at the rule of low complexity (plan row SPEC-round-places-wire). Its answer at
//! each case of DESIGN.md is checked in `round_places.rs`, and the input here at a small size.

use super::super::round_places::allocate_input;
use zed_tests::scaling::check_order_inputs;

#[test]
fn allocate_scales() {
    // One pass over the weights for their sum and each part's floor and remainder, then the
    // `d` parts with the largest remainders get one unit more, `d < n`: zed-bignum
    // `round::allocate`, O(n log n) for the sort of the remainders, under the ratio for power 1
    // (8 log 8n / log n = 8 * 15 / 12 = 10.0 at this n, below 10.5). The total and the weights
    // are each a few words, so each part is O(1) words. Measured 2026-11-26 on a Colab VM:
    // 43306382 and 366332771 instructions at n = 4096 and 32768, 8.46 times the work.
    let n = 1 << 12;
    check_order_inputs(
        "allocate of 1000000.01r over n weights at places: 2",
        n,
        1,
        allocate_input,
        |t| {
            zed_kernel::eval(t).expect("a list");
        },
    );
}
