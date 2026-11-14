//! The benchmarks of `setop.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `setop.rs`.

use super::*;

/// Meets of `k` members at `k` and `8k`: with one empty operand the decider settles the meet
/// with no search; with all operands inhabited only the meet is searched.
#[test]
fn meets_of_k_members_scale() {
    let empty = scaling::inputs(8, |k| meet_of_k(k, true));
    let full = scaling::inputs(8, |k| meet_of_k(k, false));
    scaling::check("the verdict on a meet of k members, one empty", 8, |k| {
        assert_eq!(verdict_and_searched(&empty[&k]), (Verdict::Empty, 0));
    });
    scaling::check("the verdict on a meet of k inhabited members", 8, |k| {
        assert_eq!(verdict_and_searched(&full[&k]), (Verdict::Inhabited, 1));
    });
}

/// The product of `k` parity lists is inhabited (`[k]` is in it), and the search for a value
/// finds the singleton before following the recursive tuple fork (COMPLEXITY.md K35).
/// Both the verdict and emptiness are checked in the size of the constraints. Small instance
/// `the_product_of_a_few_parity_lists_has_a_singleton`.
#[test]
fn the_product_of_k_parity_lists_has_a_checked_singleton() {
    let meets = scaling::inputs(4, parity_meet);
    scaling::check("emptiness of the product of k parity lists", 4, |k| {
        Type::forget_emptiness();
        assert!(!meets[&k].is_empty());
    });
}

#[test]
fn canonical_blame_settlement_scales() {
    let groups = scaling::inputs(64, canonical_blame_chain);
    scaling::check_order(
        "canonical blame settlement on m refused chain members",
        64,
        1,
        |m| {
            Type::forget_emptiness();
            let v = groups[&m][0].verdict();
            assert_eq!(v, Verdict::Refused(Refusal::NoWitness));
        },
    );
}

#[test]
fn parity_verdicts_scale_with_the_number_of_constraints() {
    let inputs = scaling::inputs(16, |k| parity_variant(k, 0, Some("Scale_"), false));
    scaling::check_order("parity verdict with a checked singleton", 16, 1, |k| {
        Type::forget_emptiness();
        assert_eq!(inputs[&k].verdict(), Verdict::Inhabited);
    });
}

#[test]
fn bounded_parity_verdicts_scale() {
    for exclude in [false, true] {
        let inputs = scaling::inputs(16, |k| bounded_parity(k, 2 * k, exclude.then_some(k)));
        scaling::check_order(
            "bounded parity with a further integer constraint",
            16,
            1,
            |k| {
                Type::forget_emptiness();
                assert_eq!(inputs[&k].verdict(), Verdict::Inhabited);
            },
        );
    }
}

/// The diagonal parity answer is kept with each instance, so a thread that decided the same
/// group first does not make the first decision on this thread cheaper: here the inputs of size
/// `n` are decided on another thread before the first runs, and the first runs still take
/// work in the size of the constraints (item GSX-unsolved, I6.7). Sizes 10 and 80 are this
/// test's own.
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

#[test]
fn bounded_parity_with_a_repeated_scalar_field_scales() {
    repeated_integer_field_scale(16);
}

#[test]
fn shared_integer_columns_scale_with_their_written_dag() {
    shared_integer_columns_check(64, false);
}

/// Distinct columns at `n` and `8n`. The check that a further finite field keeps the point the
/// first search checked is in `a_few_shared_integer_columns_are_inhabited`.
#[test]
fn distinct_integer_columns_reuse_a_checked_point() {
    shared_integer_columns_check(64, true);
}

#[test]
fn shared_cofinite_boundaries_are_not_enumerated_per_row() {
    cofinite_rows_scale(64);
}

/// The exponent has n+1 decimal digits; the integer has far more than 2^n
/// digits. A checked point must keep those powers instead of expanding them. The types are
/// [`beside_a_large_power`]; small instance, with the check that each holds `(1,)`:
/// `cofinite_integer_points_beside_a_few_large_powers`.
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
