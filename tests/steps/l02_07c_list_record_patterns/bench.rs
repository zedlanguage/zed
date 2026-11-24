//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, resolving and dropping a unit of list and record patterns is linear in its size.
//! These are the benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of
//! its default run. Each check they make besides the ratio is made at small sizes by a test of
//! `scaling.rs`.

use std::collections::HashMap;

use zed_tests::scaling;

use crate::scaling::{Parsed, arms, entries, fields, nested, parsed, pass};

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = scaling::inputs(base, |n| parsed(make(n)));
    scaling::check(what, base, |n| {
        pass(&units[&n]);
    });
}

#[test]
fn a_list_pattern_of_many_entries_scales() {
    linear("a list pattern of n entries and a rest", 4000, entries);
}

#[test]
fn a_record_pattern_of_many_fields_scales() {
    linear("a record pattern of n fields", 4000, fields);
}

#[test]
fn list_and_record_patterns_nested_deep_scale() {
    linear("list and record patterns nested n deep", 1000, nested);
}

#[test]
fn a_match_of_many_list_and_record_arms_scales() {
    linear("a match of n arms of list and record patterns", 2000, arms);
}
