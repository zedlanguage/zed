//! The benchmarks of `num_text.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `num_text.rs`.

use super::*;

/// An end of 1,280,000 and of 10,240,000 digits written in decimal, the value built before
/// timing, in n log^2 n, the order of radix conversion (COMPLEXITY.md C31), held to the limit of
/// 10.5 as `writing_a_wide_end_scales` is. At 160,000 and 1,280,000 digits it measured 11.2 times
/// the work (2026-11-13), over 10.5; at 8 times those sizes, 10.3 times the work and 8.9 times the
/// bytes. Both sizes are above `PRINT_WHOLE` words (1,280,000 digits is 66,439 words), so both are
/// split by halves. Below `PRINT_WHOLE`, num-bigint's printing, faster there, grows faster:
/// `writing_an_end_below_print_whole_scales`, deferred to plan row PRINT-below-whole-13 in
/// wt/scratch/deferred-tests/PRINT-below-whole-13.rs.
#[test]
fn writing_a_long_decimal_end_scales() {
    let ends = scaling::inputs(1_280_000, |n| {
        let text = digits(&mut Rng::new(n as u64), n);
        text.parse::<Num>().expect("digits")
    });
    let words = 1_280_000.0 / (64.0 * std::f64::consts::LOG10_2);
    assert!(
        words > PRINT_WHOLE as f64 + 1.0,
        "1,280,000 digits are split"
    );
    scaling::check("writing a decimal end of n digits", 1_280_000, |n| {
        assert!(!ends[&n].to_string().is_empty());
    });
}

/// An end of 65,536 and 524,288 words (about 1.26 and 10.1 million digits) written in decimal,
/// by the kernel's printer: O(M(n) log n) = O(n log^2 n), about 2.3 times the work per
/// doubling, 12 times here (COMPLEXITY.md K81, C31), held to the limit of 10.5 every scaling
/// test meets; 10.2 times (2026-11-13).
#[test]
fn writing_a_wide_end_scales() {
    let n = 1 << 16;
    let ends = scaling::inputs(n, |m| Num::from(wide(&mut Rng::new(m as u64), m)));
    scaling::check("writing a decimal end of n words", n, |m| {
        assert!(!ends[&m].to_string().is_empty());
    });
}
