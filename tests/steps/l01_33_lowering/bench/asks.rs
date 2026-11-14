//! Lowering two equal lambdas is linear in the bytes of the constant they hold: the benchmark of
//! `asks.rs`, whose test lowers them to one node for a constant of a few bytes.

use std::collections::HashMap;

use zed_kernel::{Term, Value};
use zed_tests::scaling::check_order;
use zedc::zir::lower::lower;

use crate::asks::{two_lambdas, wide};
use crate::count;

/// Lowering two equal lambdas is linear in the bits of the constant they hold: the second is
/// found by its key and confirmed by the bytes of its own node and its region's number.
#[test]
fn lowering_equal_lambdas_of_a_wide_constant_scales() {
    let (n, sizes) = (1usize << 20, [1usize << 20, 8 << 20]);
    let inputs: HashMap<usize, Term> = sizes
        .into_iter()
        .map(|b| (b, two_lambdas(&Value::int(wide(b)))))
        .collect();
    check_order(
        "lowering two equal lambdas of a wide constant, by its bytes",
        n,
        1,
        |b| {
            let g = lower(&inputs[&b]).expect("memory is given");
            assert_eq!(count(&g, "lambda"), 1);
        },
    );
}
