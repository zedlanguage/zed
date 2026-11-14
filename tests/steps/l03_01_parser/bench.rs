//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, refusing in name resolution and dropping a unit is linear in its size. These are
//! the benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-rest). Each check they make besides the ratio is made at small
//! sizes by a test of `scaling.rs`.

use std::collections::HashMap;

use zed_tests::scaling;

use crate::scaling::{Parsed, arms, array, deep, display, nested, parsed, pass};

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect();
    scaling::check(what, base, |n| pass(&units[&n]));
}

#[test]
fn a_display_of_many_entries_scales() {
    linear("a display of n entries", 2000, display);
}

#[test]
fn a_match_of_many_range_arms_scales() {
    linear("a match of n range-pattern arms", 2000, arms);
}

#[test]
fn a_section_nested_deep_scales() {
    linear("a section nested n deep", 1000, deep);
}

#[test]
fn an_array_display_of_many_elements_scales() {
    linear("an array display of n elements", 2000, array);
}

#[test]
fn an_array_display_nested_deep_scales() {
    linear("an array display nested n deep", 1000, nested);
}
