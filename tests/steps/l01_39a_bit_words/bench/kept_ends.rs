//! The bits, trailing zeros and shift right of kept ends, at exponents `k` and `8k` (ledger
//! BIT-kept-ends).

use std::collections::HashMap;

use zed_kernel::Prim;
use zed_tests::scaling;
use zedc::store::interval::{End, End::PosInf, IntervalSet, Num, bit_word};

use super::super::kept_ends::ends;

#[test]
fn bits_and_trailing_zeros_of_kept_ends_do_not_grow_with_the_exponent() {
    // The bits, trailing zeros and shift right of kept ends of exponents k and 8k, and the
    // rules that read the bits of 2 ^ k - 1. Written out, each grows with the digits, 8
    // times or more.
    let n = 1 << 20;
    let built: HashMap<usize, Vec<(Num, Option<Num>)>> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, ends(m as i64)))
        .collect();
    scaling::check_order(
        "bits, trailing zeros and shr of kept ends of exponent k",
        n,
        0,
        |m| {
            let width = IntervalSet::single(m as i64);
            let x = IntervalSet::range(End::of(1), PosInf);
            for (v, p) in &built[&m] {
                std::hint::black_box(v.bits());
                std::hint::black_box(v.trailing_zeros());
                if let Some(p) = p {
                    std::hint::black_box(v.div_floor(p));
                }
            }
            std::hint::black_box(bit_word(Prim::LeadingZeros, &[x.clone(), width.clone()]));
            std::hint::black_box(bit_word(Prim::TrailingZeros, &[x, width]));
        },
    );
}
