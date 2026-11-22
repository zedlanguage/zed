use std::collections::BTreeMap;

use zed_tests::scaling;

use super::super::Resolved;
use super::super::shared_tuples::{by_bindings, by_calls};

/// Besides its ratio: the value is data, with no error. Small instance:
/// `shared_tuples::a_value_held_twice_at_each_level_is_data`.
#[test]
fn values_held_twice_at_each_level_are_checked_in_linear_time() {
    type Family = fn(usize, &str) -> String;
    for (what, text) in [
        ("an integer doubled by n nested calls", by_calls as Family),
        ("an integer doubled by n bindings", by_bindings),
    ] {
        // On the 2 MiB stack of a test thread: nothing recurses on the 4,000 levels.
        let units: BTreeMap<usize, Resolved> = [5000, scaling::FACTOR * 5000]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n, "1"))))
            .collect();
        scaling::check_order(what, 5000, 1, |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{what} at {n}");
        });
    }
}

/// The depth of the program STACK-big-tests (a44c82a2) probed on a 2 MiB stack and did not
/// commit (TESTS-STACK-big-tests-deep-ops, test audit 2026-11-08 row 15).
const PAIR_LEVELS: usize = 100_000;

/// `text(PAIR_LEVELS, "1")` read, resolved and checked on a thread of a 2 MiB stack, whatever
/// `RUST_MIN_STACK` says: a walk on its path that recursed once a level would overflow it. The
/// value is data, so there is no error, as at 3 levels in
/// `shared_tuples::a_value_held_twice_at_each_level_is_data`.
fn checked_on_a_small_stack(what: &str, text: fn(usize, &str) -> String) {
    zed_tests::deep::on_small_stack(|| {
        let start = std::time::Instant::now();
        let errors = Resolved::new(&text(PAIR_LEVELS, "1")).type_errors();
        assert_eq!(errors, Vec::<String>::new(), "{what}, {PAIR_LEVELS} levels");
        eprintln!(
            "{what}, {PAIR_LEVELS} levels: read, resolved and checked in {:.2?}",
            start.elapsed()
        );
    });
}

#[test]
fn an_integer_doubled_by_100_000_nested_calls_is_checked_on_a_2_mib_stack() {
    checked_on_a_small_stack("an integer doubled by nested calls", by_calls);
}

#[test]
fn an_integer_doubled_by_100_000_bindings_is_checked_on_a_2_mib_stack() {
    checked_on_a_small_stack("an integer doubled by bindings", by_bindings);
}
