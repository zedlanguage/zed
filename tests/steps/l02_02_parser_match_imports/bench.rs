//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting, refusing in name resolution and dropping a unit is linear in its size. These are
//! the benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-rest). Each check they make besides the ratio is made at small
//! sizes by a test of `scaling.rs`.

use std::collections::HashMap;

use zed_tests::scaling;

use crate::scaling::{Parsed, annotated, arms, deep, imports, one_import, parsed, pass};

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect();
    scaling::check(what, base, |n| pass(&units[&n]));
}

#[test]
fn a_match_of_many_arms_scales() {
    linear("a match of n arms", 4000, arms);
}

#[test]
fn many_imports_scale() {
    linear("n imports", 1000, imports);
}

#[test]
fn one_import_of_many_names_scales() {
    linear("one import of n names", 1000, one_import);
}

#[test]
fn a_deep_pattern_scales() {
    linear("a match pattern nested n deep", 1000, deep);
}

#[test]
fn many_annotations_scale() {
    linear("n annotated functions", 1000, annotated);
}
