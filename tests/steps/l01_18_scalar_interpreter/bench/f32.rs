//! A float to an `int` power in the kernel (plan row POW-domains) at the rule of low
//! complexity: O(1) a call for an exponent of one machine word, O(size) for a larger one.

use num_bigint::BigInt;
use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Prim, Rat, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling::{check_order, inputs};
use zed_tests::step_helpers::l01_36_cranelift::kernel;

use super::super::sqrt_fma::bounded_f64;

/// `m` rows of `f64 ^ int` drawn from the seed `m`: a base with exponent in -4..=4 to an
/// exponent in -300..=300, and every fourth row to a 70-bit exponent past 2^53, which takes the
/// path that reads the nearest `f64` of its parity.
fn rows(m: usize) -> Vec<Term> {
    let mut rng = Rng::new(m as u64);
    (0..m)
        .map(|i| {
            let x = lit(Value::float(bounded_f64(&mut rng, -4, 4)));
            let k = rng.int(-300, 300);
            let n = if i % 4 == 0 {
                Value::integer(Rat::int((BigInt::from(k) << 70) + 1))
            } else {
                Value::Int(k)
            };
            prim(Prim::Pow, vec![x, lit(n)])
        })
        .collect()
}

/// n and 8n powers on random operands, in the kernel.
#[test]
fn n_powers_cost_linear_time() {
    let n = 1 << 18;
    let ops = inputs(n, rows);
    check_order("f64 ^ int, one power per operand row", n, 1, |m| {
        for t in &ops[&m] {
            assert!(matches!(kernel(t).unwrap(), Value::Float(_)));
        }
    });
}
