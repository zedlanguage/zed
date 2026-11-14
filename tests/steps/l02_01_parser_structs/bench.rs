//! The L2 forms at the rule of low complexity (DESIGN.md Part G): building, formatting and
//! dropping a unit is linear in its size. These are the benchmarks of `scaling.rs`, run by
//! `tools/run_tests.sh --bench` and left out of its default run (TEST-bench-move-rest). Each
//! check they make besides the ratio is made at small sizes by a test of `scaling.rs`.

use std::collections::HashMap;

use zed_tests::scaling;

use crate::scaling::{Parsed, chain, deep, imports, methods, named, parsed, pass, repeated, wide};

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = [base, 8 * base]
        .into_iter()
        .map(|n| (n, parsed(make(n))))
        .collect();
    scaling::check(what, base, |n| pass(&units[&n]));
}

#[test]
fn a_struct_of_many_fields_scales() {
    linear("a struct and a display of n fields", 1000, wide);
}

#[test]
fn a_struct_of_many_imports_scales() {
    linear("a struct of n imports", 1000, imports);
}

#[test]
fn a_struct_that_imports_every_path_twice_scales() {
    linear("a struct of n imports, each written twice", 1000, repeated);
}

#[test]
fn many_methods_scale() {
    linear("n methods", 500, methods);
}

#[test]
fn a_deep_display_scales() {
    linear("a display nested n deep", 1000, deep);
}

#[test]
fn a_chain_of_updates_scales() {
    linear("a chain of n updates and an update of n paths", 1000, chain);
}

#[test]
fn a_display_of_named_values_and_long_chains_scales() {
    linear(
        "a display of n bare-name values, and chains of n operands of && and else",
        1000,
        named,
    );
}
