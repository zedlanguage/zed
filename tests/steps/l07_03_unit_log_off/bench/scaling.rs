//! Building, formatting and resolving the unit items of `scaling.rs` is linear in their number.
//! Each input is lexed and parsed before timing.

use std::collections::HashMap;

use zed_tests::scaling;

use crate::scaling::{Parsed, copies, misplaced, parsed, pass};

/// Checks that building, formatting and resolving `make(n)` is linear in `n`, from `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect();
    scaling::check(what, base, |n| pass(&units[&n], n));
}

#[test]
fn many_unit_items_scale() {
    linear("n copies of the unit item", 4000, copies);
}

#[test]
fn many_misplaced_unit_items_scale() {
    linear("n blocks holding the unit item", 4000, misplaced);
}
