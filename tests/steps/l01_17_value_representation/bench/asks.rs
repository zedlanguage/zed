//! The work of item RAT-asks at the rule of low complexity. The inputs are built in `asks.rs`,
//! whose test `the_asks_benchmarks_give_their_results_at_a_small_size` checks each at a small
//! size.

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Prim, eval};
use zed_tests::deep::resolved;
use zed_tests::scaling::{check_order, inputs};

use super::super::asks::{float_at_int, joined_nines};

/// Checking a float literal of `n` digits reads them where they are and copies its text once,
/// in memory asked first: O(n).
#[test]
fn checking_a_long_float_literal_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 7 ns a digit,
    // 1x 0.47 s; the inputs and runs take 2.1 GB at 8n (it ran at 2^16 before).
    let n = 1 << 26;
    let units = inputs(n, |n| resolved(&format!("x = 0.{}f64;\n", "9".repeat(n))));
    check_order("checking a float literal of n digits", n, 1, |m| {
        let (stmts, res) = &units[&m];
        assert!(zedc::check::walk::check(stmts, res).errors.is_empty());
    });
}

/// The message for a decimal literal of `n` digits where an int is expected costs O(n log^2 n):
/// the checker reads the literal's digits into a `rat` by halves (`zed_kernel::num::read_digits`,
/// COMPLEXITY.md K41), and the rest is O(n): the test for a factor 2 counts trailing zeros, the
/// test for a factor 5 is one pass of `divides`, and the scan of the text and the quote in the
/// message read each byte a bounded number of times. Until 2026-11-20 this test was named
/// `the_message_for_a_long_literal_costs_order_n`, which the reading never was.
///
/// The bound (author decision P300, the proof at `read_digits`): with `LEAF_DIGITS` = 2048 there
/// are `L = log2(n / 2048)` levels, 10 at `n` = 2^21 and 13 at `8n`, and level `j` costs about
/// one product of total width `n` by transforms, `a n (11 + j)`, so the reading costs
/// `a n (11 L + L^2 / 2 + L / 2)` and predicts `8 * 234 / 165` = 11.35 (and `8 (ln 8n / ln n)^2`
/// 10.45 counted from one digit). Measured 9.54 times the instructions on 2026-11-18 and 10.07
/// on 2026-11-20 (8.74 times the bytes).
/// At three sizes on 2026-11-21 (PERF-ratios-over-9-l0136): 9.54, 9.55 and 9.46 times at `n` =
/// 2^21, 2^22 and 2^23, no growth with `n`, as the bound predicts.
#[test]
fn the_message_for_a_long_literal_costs_n_log_squared_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 150 ns a
    // digit, 1x 0.31 s, 1.4 GB at 8n. The ratio was 10.3 at 2^16 and is 9.7 here.
    let n = 1 << 21;
    let units = inputs(n, |n| resolved(&float_at_int(n)));
    check_order("the message for a decimal literal of n digits", n, 1, |m| {
        let (stmts, res) = &units[&m];
        assert_eq!(zedc::check::walk::check(stmts, res).errors.len(), 1);
    });
}

/// Copying a string of `n` nines joined from two halves into one piece costs O(n), through
/// `f64`, whose reading of the text is one pass. `int` and `rat` copy it the same way, but
/// their reading of the digits is O(n^1.47) (COMPLEXITY.md K41, measured by
/// `l01_18_scalar_interpreter::scaling`), so they would measure that and not the copy.
#[test]
fn reading_a_joined_string_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 3 ns a byte,
    // 1x 0.42 s, 1.1 GB at 8n.
    let n = 1 << 27;
    let strings = inputs(n, joined_nines);
    check_order("f64 of a joined string of n digits", n, 1, |m| {
        assert!(eval(&prim(Prim::CastF64, vec![lit(strings[&m].clone())])).is_ok());
    });
}
