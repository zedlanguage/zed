//! The split of a power is proved in time that grows with its exponent's digits: the benchmark
//! of `factored.rs`.

use zed_tests::scaling;

use crate::factored::{split_of, split_proved};

#[test]
fn the_split_scales_with_its_exponent_digits() {
    // 16 and 128 bits: the work is the points' powers, one squaring a bit, and the factors'
    // expansion, the same at both.
    let ins = scaling::inputs(16, split_of);
    scaling::check(
        "(1 + x) ^ e == (1 + x) ^ h * (x + 1) ^ (e - h), e of n bits",
        16,
        |n| split_proved(&ins[&n]),
    );
}
