//! Step L1.17a at the rule of low complexity: `wide mod 3`, `wide mod (2^128 + 1)`, `1 - wide`,
//! `wide div 3`, and `wide mod` and `div (2^8192 + 1)`, each one pass over the digits of `wide`
//! = `2^n + 1`, O(n), with the operands built before timing. Their answers are checked exactly
//! at a small width by `wide_differences_quotients_and_remainders_are_exact` in `in_place.rs`.
//!
//! Sizes: most passes take well under 1 ns a bit, so 0.6 s at 1x would need billions of bits,
//! and 8n a number of several GB. Most run at `n = 2^30` bits, 128 MiB, and 8n at 1 GiB; a
//! result as wide as `wide` is 1 GiB more at 8n. Those whose runs take more memory run at a
//! smaller `n`, as each says.

use zed_kernel::{Prim, Term, Value, eval};
use zed_tests::kernel::{bin, sub};
use zed_tests::scaling::{check_order, inputs};

use super::super::in_place::{above, num};

/// `op` of `2^n + 1` at n and 8n bits, built once before timing.
fn terms(n: usize, op: impl Fn(Term) -> Term) -> std::collections::HashMap<usize, Term> {
    inputs(n, |m| op(num(above(m as u64))))
}

#[test]
fn a_wide_number_mod_3_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 0.08 ns a
    // bit, 1x 84 ms; memory holds n at 2^30.
    let n = 1 << 30;
    let t = terms(n, |w| bin(Prim::Mod, w, num(3)));
    check_order("2^n + 1 mod 3", n, 1, |m| {
        assert_eq!(eval(&t[&m]).unwrap(), Value::Int(2));
    });
}

#[test]
fn a_wide_number_mod_a_number_of_two_words_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 3.2 ns a
    // bit, 1x 0.43 s, 1.7 GB at 8n.
    let n = 1 << 27;
    let t = terms(n, |w| bin(Prim::Mod, w, num(above(128))));
    check_order("2^n + 1 mod 2^128 + 1", n, 1, |m| {
        assert!(matches!(eval(&t[&m]).unwrap(), Value::Int(_)));
    });
}

#[test]
fn one_less_a_wide_number_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 0.11 ns a
    // bit, 1x 0.11 s, 2.1 GB at 8n; memory holds n at 2^30.
    let n = 1 << 30;
    let t = terms(n, |w| sub(num(1), w));
    check_order("1 - (2^n + 1)", n, 1, |m| {
        assert!(matches!(eval(&t[&m]).unwrap(), Value::Big(_)));
    });
}

#[test]
fn a_wide_number_div_3_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 0.19 ns a
    // bit, 1x 0.20 s, 2.1 GB at 8n; memory holds n at 2^30.
    let n = 1 << 30;
    let t = terms(n, |w| bin(Prim::IntDiv, w, num(3)));
    check_order("2^n + 1 div 3", n, 1, |m| {
        assert!(matches!(eval(&t[&m]).unwrap(), Value::Big(_)));
    });
}

#[test]
fn a_wide_number_mod_a_number_of_8193_bits_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 0.52 ns a
    // bit, 1x 0.14 s, 1.6 GB at 8n, which holds n down: at 2^30 it took 6.2 GB.
    let n = 1 << 28;
    let t = terms(n, |w| bin(Prim::Mod, w, num(above(8192))));
    check_order("2^n + 1 mod 2^8192 + 1", n, 1, |m| {
        assert!(eval(&t[&m]).is_ok());
    });
}

#[test]
fn a_wide_number_div_a_number_of_8193_bits_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 0.63 ns a
    // bit, 1x 84 ms, 2.6 GB at 8n, which holds n down: at 2^30 it took 20 GB.
    let n = 1 << 27;
    let t = terms(n, |w| bin(Prim::IntDiv, w, num(above(8192))));
    check_order("2^n + 1 div 2^8192 + 1", n, 1, |m| {
        assert!(matches!(eval(&t[&m]).unwrap(), Value::Big(_)));
    });
}
