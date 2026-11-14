//! The benchmarks of `setop.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `setop.rs`.

use super::*;

/// Meets of `k` members at `k` and `8k`: with one empty operand the decider settles the meet
/// with no search; with all operands inhabited, in
/// [`meets_of_k_inhabited_members_scale`], only the meet is searched.
///
/// Size (TEST-bench-move-l0123, author P169): n 8 before, now 16384; 1x 215 ms at load
/// 23.33.
#[test]
fn meets_of_k_members_scale() {
    let n = 16384;
    let empty = scaling::inputs(n, |k| meet_of_k(k, true));
    scaling::check("the verdict on a meet of k members, one empty", n, |k| {
        assert_eq!(verdict_and_searched(&empty[&k]), (Verdict::Empty, 0));
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 8 before, now 16384; 1x 206 ms at load
/// 23.33.
#[test]
fn meets_of_k_inhabited_members_scale() {
    let n = 16384;
    let full = scaling::inputs(n, |k| meet_of_k(k, false));
    scaling::check("the verdict on a meet of k inhabited members", n, |k| {
        assert_eq!(verdict_and_searched(&full[&k]), (Verdict::Inhabited, 1));
    });
}

/// The product of `k` parity lists is inhabited (`[k]` is in it), and the search for a value
/// finds the singleton before following the recursive tuple fork (COMPLEXITY.md K35).
/// Both the verdict and emptiness are checked in the size of the constraints. Small instance
/// `the_product_of_a_few_parity_lists_has_a_singleton`.
///
/// Size (TEST-bench-move-l0123, author P169): n 4 before, now 4096; 1x 155 ms at load
/// 21.54.
#[test]
fn the_product_of_k_parity_lists_has_a_checked_singleton() {
    let n = 4096;
    let meets = scaling::inputs(n, parity_meet);
    scaling::check("emptiness of the product of k parity lists", n, |k| {
        Type::forget_emptiness();
        assert!(!meets[&k].is_empty());
    });
}

/// Size (TEST-bench-move-l0123, author P169): left at n 64, its old size, because the ratio
/// fails at larger sizes; 1x 4.0 ms at load 23.33. Instructions from m to 8m: 8.51
/// times from 64 (measured at the old size), 13.88 from 512 and 25.93 from 2048 (833M to
/// 21,587M, while bytes grew 8.0 times), over the limit 10.5.
#[test]
fn canonical_blame_settlement_scales() {
    let n = 64;
    let groups = scaling::inputs(n, canonical_blame_chain);
    scaling::check_order(
        "canonical blame settlement on m refused chain members",
        n,
        1,
        |m| {
            Type::forget_emptiness();
            let v = groups[&m][0].verdict();
            assert_eq!(v, Verdict::Refused(Refusal::NoWitness));
        },
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 4096; 1x 216 ms at load
/// 22.90.
#[test]
fn parity_verdicts_scale_with_the_number_of_constraints() {
    let n = 4096;
    let inputs = scaling::inputs(n, |k| parity_variant(k, 0, Some("Scale_"), false));
    scaling::check_order("parity verdict with a checked singleton", n, 1, |k| {
        Type::forget_emptiness();
        assert_eq!(inputs[&k].verdict(), Verdict::Inhabited);
    });
}

/// Bounded parity of `k` with bound `2k`, with `k` excluded when `exclude`, at `n` and `8n`.
/// One test for each.
fn bounded_parity_verdicts(n: usize, exclude: bool) {
    let inputs = scaling::inputs(n, |k| bounded_parity(k, 2 * k, exclude.then_some(k)));
    scaling::check_order(
        "bounded parity with a further integer constraint",
        n,
        1,
        |k| {
            Type::forget_emptiness();
            assert_eq!(inputs[&k].verdict(), Verdict::Inhabited);
        },
    );
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 4096; 1x 252 ms at load
/// 23.94.
#[test]
fn bounded_parity_verdicts_scale() {
    bounded_parity_verdicts(4096, false);
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 4096; 1x 253 ms at load
/// 23.94.
#[test]
fn bounded_parity_verdicts_with_an_excluded_integer_scale() {
    bounded_parity_verdicts(4096, true);
}

/// The diagonal parity answer is kept with each instance, so a thread that decided the same
/// group first does not make the first decision on this thread cheaper: here the inputs of size
/// `n` are decided on another thread before the first runs, and the first runs still take
/// work in the size of the constraints (item GSX-unsolved, I6.7). Sizes 10 and 80 are this
/// test's own.
///
/// Size (TEST-bench-move-l0123, author P169): left at n 10: the work does not grow with
/// n (3.7 µs and 4.0 µs, 19,711 and 20,180 instructions, at n and 8n, load 24.28), so no n
/// brings the 1x near 0.5 s.
#[test]
fn bounded_empty_parity_decided_on_another_thread_costs_the_same_here() {
    let n = 10;
    // The type decided there is kept alive, and with it its group, which this thread's inputs
    // share.
    let _decided = std::thread::spawn(move || {
        let t = bounded_parity(n, n - 1, None);
        assert_eq!(t.verdict(), Verdict::Empty);
        t
    })
    .join()
    .unwrap();
    let inputs = scaling::inputs(n, |k| bounded_parity(k, k - 1, None));
    scaling::check_order(
        "diagonal parity decided on another thread first",
        n,
        1,
        |k| {
            Type::forget_emptiness();
            assert_eq!(inputs[&k].verdict(), Verdict::Empty);
        },
    );
}

/// Singleton count equations force every allowed symbol to occur evenly, so
/// the sum cannot be the required odd length. Inputs are built before timing.
///
/// Size (TEST-bench-move-l0123, author P169): left at n 9: the work does not grow with
/// n (5.0 µs and 5.1 µs, 20,629 and 20,823 instructions, at n and 8n, load 23.94), so no n
/// brings the 1x near 0.5 s.
#[test]
fn bounded_empty_parity_is_decided_in_the_size_of_the_constraints() {
    // Each instance keeps its diagonal answer while it lives, as it keeps its group's
    // judgment, so a test that built the same group on another thread cannot have decided
    // these inputs before their first runs.
    let n = 9;
    let inputs = scaling::inputs(n, |k| bounded_parity(k, k - 1, None));
    scaling::check_order("diagonal parity contradiction", n, 1, |k| {
        Type::forget_emptiness();
        assert_eq!(inputs[&k].verdict(), Verdict::Empty);
        assert!(inputs[&k].is_empty());
    });
}

/// Size (TEST-bench-move-l0123, author P169): n 16 before, now 4096; 1x 206 ms at load
/// 23.70.
#[test]
fn bounded_parity_with_a_repeated_scalar_field_scales() {
    repeated_integer_field_scale(4096);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 262144; 1x 14 ms at load
/// 21.54. The 1x stays under 0.5 s because building the inputs takes most of the
/// wall time: at 2097152 the test passed the 25 s limit before its first run.
#[test]
fn shared_integer_columns_scale_with_their_written_dag() {
    shared_integer_columns_check(262144, false);
}

/// Distinct columns at `n` and `8n`. The check that a further finite field keeps the point the
/// first search checked is in `a_few_shared_integer_columns_are_inhabited`.
///
/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 65536; 1x 48 ms at load
/// 23.33. Not grown past 65536: peak memory there was 4.6 GB (measured), near the 6 GB
/// stop the resize brief sets.
#[test]
fn distinct_integer_columns_reuse_a_checked_point() {
    shared_integer_columns_check(65536, true);
}

/// Size (TEST-bench-move-l0123, author P169): n 64 before, now 16384; 1x 56 ms at load
/// 22.11.
#[test]
fn shared_cofinite_boundaries_are_not_enumerated_per_row() {
    cofinite_rows_scale(16384);
}

/// The exponent has n+1 decimal digits; the integer has far more than 2^n
/// digits. A checked point must keep those powers instead of expanding them. The types are
/// [`beside_a_large_power`]; small instance, with the check that each holds `(1,)`:
/// `cofinite_integer_points_beside_a_few_large_powers`.
///
/// Size (TEST-bench-move-l0123, author P169): left at n 8: the work does not grow with
/// n (34.6 µs and 36.2 µs, 89,533 and 93,312 instructions, at n and 8n, load 23.33), so no n
/// brings the 1x near 0.5 s.
#[test]
fn cofinite_integer_points_keep_large_powers_symbolic() {
    let n = 8;
    let inputs = scaling::inputs(n, beside_a_large_power);
    scaling::check_order(
        "a cofinite point beyond symbolic integer exclusions",
        n,
        1,
        |k| {
            Type::forget_emptiness();
            assert_eq!(inputs[&k].verdict(), Verdict::Inhabited);
        },
    );
}
