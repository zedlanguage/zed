//! The benchmarks of the text of types, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). Each check they make besides the ratio has a small
//! instance among the correctness tests of `print.rs`, named at each benchmark.

use std::collections::BTreeMap;

use super::super::Type;
use super::tests::{decision_list, part_ring, three_carriers};
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

/// Small instances: `a_cycle_of_parts_written_by_name_is_defined`.
#[test]
fn a_long_cycle_of_parts_written_by_name_scales() {
    let n = 2_000;
    let built: BTreeMap<usize, Type> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, part_ring(m)))
        .collect();
    scaling::check(
        "the text by name of a ring of parts kept unevaluated",
        n,
        |m| {
            let s = built[&m].surface_by_name(super::super::TextPlace::Any);
            assert_eq!(s.defs.len(), m + 1);
        },
    );
}

/// Small instances: `a_cycle_of_parts_written_by_name_is_defined`, and in `rec::unfold::tests`
/// `a_part_s_name_is_unchanged_when_the_names_inside_it_are_shared` and
/// `a_nest_of_parts_prints_as_it_did_before_names_were_shared`. Item PERF-part-name-nested:
/// each part of `part_cycle` was named by its whole subexpression, so the names of `k` nested
/// parts spelled out O(k^2) text (42.4 times the instructions at 100 and 800 parts); built once
/// per part with the names inside it shared, they take O(k) work, and the printer's sort of its
/// tokens O(t log t), which is 10.19 times at 2,000 and 16,000 (`scaling`; `n` is at least
/// 777). Measured alone: 9.98 times the instructions and 9.06 the bytes; building alone 8.4,
/// building and printing by name 8.7, plain 8.7. Printed plain first and by name after,
/// `part_ring` takes more than in the other order, before this item too (10.5 against 8.9),
/// item PERF-print-by-name-after-plain.
#[test]
fn a_long_nest_of_parts_is_built_and_printed_in_n_log_n_work() {
    let n = 2_000;
    scaling::check(
        "building and printing a nest of parts kept unevaluated, by name and plain",
        n,
        |m| {
            let t = super::tests::part_cycle(m);
            let s = t.surface_by_name(super::super::TextPlace::Any);
            assert_eq!(s.defs.len(), m + 1);
            assert!(!t.surface().root.is_empty());
        },
    );
}
