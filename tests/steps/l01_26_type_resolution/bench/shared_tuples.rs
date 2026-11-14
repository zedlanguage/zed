use std::collections::BTreeMap;

use zed_tests::scaling;

use super::super::Resolved;
use super::super::shared_tuples::{by_bindings, by_calls};

#[test]
fn values_held_twice_at_each_level_are_checked_in_linear_time() {
    type Family = fn(usize, &str) -> String;
    for (what, text) in [
        ("an integer doubled by n nested calls", by_calls as Family),
        ("an integer doubled by n bindings", by_bindings),
    ] {
        // On the 2 MiB stack of a test thread: nothing recurses on the 4,000 levels.
        let units: BTreeMap<usize, Resolved> = [500, scaling::FACTOR * 500]
            .into_iter()
            .map(|n| (n, Resolved::new(&text(n, "1"))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{what} at {n}");
        });
    }
}
