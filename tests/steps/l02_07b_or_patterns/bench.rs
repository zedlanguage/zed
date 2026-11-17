//! The forms of this step at the rule of low complexity (DESIGN.md Part G): building,
//! formatting and resolving a unit, and each refusal of this step, is linear in its size. These
//! are the benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. Each check they make besides the ratio is made at small sizes by a test of
//! `scaling.rs`.

use std::collections::HashMap;

use zed_tests::scaling;

use crate::scaling::{Parsed, alts, arms, bare, differ, nested, parsed, pass, refuse};

/// Checks that `pass` over `make(n)` is linear in `n`, from `n` = `base`.
fn linear(what: &str, base: usize, make: impl Fn(usize) -> String) {
    let units: HashMap<usize, Parsed> = scaling::inputs(base, |n| parsed(make(n)));
    scaling::check(what, base, |n| {
        pass(&units[&n]);
    });
}

#[test]
fn an_or_pattern_of_many_alternatives_scales() {
    linear("an or-pattern of n alternatives", 4000, alts);
}

#[test]
fn a_deeply_nested_or_pattern_scales() {
    linear("an or-pattern nested n deep", 1000, nested);
}

#[test]
fn a_match_of_many_arms_of_the_new_forms_scales() {
    linear(
        "a match of n arms of or-patterns, ranges and is-patterns",
        2000,
        arms,
    );
}

/// The parse is timed too: the refusal is found after it fails.
#[test]
fn a_bare_or_pattern_of_many_alternatives_is_refused_in_linear_time() {
    let texts = scaling::inputs(4000, bare);
    scaling::check("an or-pattern of n alternatives written bare", 4000, |n| {
        std::hint::black_box(refuse(&texts[&n]));
    });
}

#[test]
fn alternatives_binding_many_different_names_are_refused_in_linear_time() {
    linear(
        "n alternatives each binding a name of its own",
        4000,
        differ,
    );
}
