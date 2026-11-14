//! `sqrt` and `fma` in the kernel at the rule of low complexity: O(1) a call.

use zed_kernel::Term;
use zed_tests::instances::Rng;
use zed_tests::scaling::{check_order, inputs};
use zed_tests::step_helpers::l01_36_cranelift::kernel;

use super::super::sqrt_fma::{bounded_f64, f64v, fma, sqrt};

/// `m` rows of a `sqrt` and an `fma` of positive operands with exponents in -300..=300, drawn
/// from the seed `m`.
fn rows(m: usize) -> Vec<[Term; 2]> {
    let mut rng = Rng::new(m as u64);
    (0..m)
        .map(|_| {
            let r = [0; 3].map(|_| f64v(bounded_f64(&mut rng, -300, 300).abs().to_bits()));
            [
                sqrt(r[0].clone()),
                fma(r[0].clone(), r[1].clone(), r[2].clone()),
            ]
        })
        .collect()
}

/// n and 8n calls of each word on random operands, in the kernel.
#[test]
fn n_calls_cost_linear_time() {
    // About 1.1 µs and 1.2 KB a row: 1x about 0.28 s, 2.5 GB at 8n, 9 s in all.
    let n = 1 << 18;
    let ops = inputs(n, rows);
    check_order("sqrt and fma, one call each per operand row", n, 1, |m| {
        for ts in &ops[&m] {
            for t in ts {
                kernel(t).unwrap();
            }
        }
    });
}
