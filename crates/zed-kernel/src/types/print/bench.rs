//! The benchmarks of the text of types, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). Each check they make besides the ratio has a small
//! instance among the correctness tests of `print.rs`, named at each benchmark.

use std::collections::BTreeMap;

use super::super::Type;
use super::tests::{decision_list, three_carriers};
use crate::scaling;

/// Small instances: `the_text_of_a_decision_list_has_a_connective_between_each_two_literals`.
#[test]
fn the_text_of_a_long_decision_list_scales() {
    let n = 24_000;
    let built: BTreeMap<usize, Type> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, decision_list(m)))
        .collect();
    scaling::check(
        "the text of a decision list of blocks of two, by atoms",
        n,
        |m| {
            let s = built[&m].surface();
            assert!(s.defs.is_empty());
            assert_eq!(
                s.root.matches(" \\ ").count() + s.root.matches(" | ").count(),
                m - 1
            );
        },
    );
}

/// Small instances: `a_union_of_numeric_literals_of_three_carriers_prints_ascending`.
#[test]
fn a_union_of_many_numeric_literals_prints_ascending_in_m_log_m() {
    let n = 50_000;
    let built: BTreeMap<usize, Type> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, three_carriers(m)))
        .collect();
    scaling::check(
        "the text of a union of literals of three carriers, ascending",
        n,
        |m| {
            let s = built[&m].surface();
            assert_eq!(s.root.matches(" | ").count(), 3 * m - 1);
        },
    );
}
