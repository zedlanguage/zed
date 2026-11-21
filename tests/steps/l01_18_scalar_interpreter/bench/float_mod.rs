//! `floatMod` in the kernel at the rule of low complexity: O(1) a call, the `fmod` loop being
//! bounded by the exponent gap, here at most 600 binades for every size alike.

use zed_kernel::Term;
use zed_kernel::term::build::lit;
use zed_tests::instances::Rng;
use zed_tests::scaling::{check_order, inputs};
use zed_tests::step_helpers::l01_36_cranelift::kernel;

use super::super::float_mod::float_mod;

/// `m` calls of `floatMod` with `x` of either sign and `m > 0`, exponents in -300..=300, drawn
/// from the seed `m`.
fn rows(m: usize) -> Vec<Term> {
    let mut rng = Rng::new(m as u64);
    let mut f = |sign: u64| {
        let field = (rng.int(-300, 300) + 1023) as u64;
        let x = f64::from_bits(sign | field << 52 | rng.next_u64() >> 12);
        lit(zed_kernel::Value::float(x))
    };
    (0..m)
        .map(|i| float_mod(f(((i as u64) & 1) << 63), f(0)))
        .collect()
}

/// n and 8n calls on random operands, in the kernel.
#[test]
fn n_calls_cost_linear_time() {
    let n = 1 << 18;
    let ops = inputs(n, rows);
    check_order("floatMod, one call per operand pair", n, 1, |m| {
        for t in &ops[&m] {
            kernel(t).unwrap();
        }
    });
}
