//! Step L1.17a at the rule of low complexity: the memory check of a shared tuple, and the order
//! of two numbers that agree in many bits. Their answers are checked at small sizes in
//! `memory_check.rs`, by `the_string_of_a_shared_tuple_after_a_number_too_large_is_refused` and
//! `close_numbers_order_and_round_exactly_when_memory_is_given`.

use zed_kernel::{KernelError, eval};
use zed_tests::scaling::{check_order, inputs};

use super::super::memory_check::{built_above, shared_tuple, two_to};

/// The memory check reads a sequence shared many times once: a number too large to build,
/// read last, after `n` copies of one tuple of `n` numbers, is refused after reading `2n`
/// values, not `n^2`.
#[test]
fn a_shared_tuple_is_checked_once_before_printing() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 75 ns a
    // value, 1x 0.16 s, 0.8 GB at 8n. Building the inputs and the runs at 8n make the test
    // 9.4 s; at 2^22 it took 23 s.
    let n = 1 << 21;
    let t = inputs(n, shared_tuple);
    check_order(
        "String of n copies of one shared tuple of n numbers",
        n,
        1,
        |m| {
            let err = eval(&t[&m]).unwrap_err();
            assert!(
                matches!(&err, KernelError::NumberTooLarge { op: "String", .. }),
                "{err:?}"
            );
        },
    );
}

/// Comparing `2^n + 1`, built, with `2^n`, kept, doubles the precision of the bounds until it
/// reaches `n` bits and then builds the two once: O(n) in all.
#[test]
fn comparing_numbers_that_agree_in_n_bits_costs_order_n() {
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 0.3 ns a
    // bit, 1x 11 ms, 2.2 GB at 8n, which holds n down.
    let n = 1 << 25;
    let pairs = inputs(n, |m| (built_above(m as u64), two_to(m as u64)));
    check_order("2^n + 1 against 2^n, compared", n, 1, |m| {
        let (a, b) = &pairs[&m];
        assert_eq!(a.try_cmp(b), Ok(std::cmp::Ordering::Greater));
        assert!(a > b);
    });
}
