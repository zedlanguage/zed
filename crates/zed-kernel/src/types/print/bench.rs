//! The benchmarks of the text of types, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-crates). Each check they make besides the ratio has a small
//! instance among the correctness tests of `print.rs`, named at each benchmark.

use std::collections::BTreeMap;

use super::super::Type;
use super::tests::{decision_list, doubled, part_ring, three_carriers};
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

/// QUESTIONS A5, answer A (row A5-print): a tuple doubled to depth `m` holds `2^m` copies of
/// `(int, int)` on `m + 1` distinct parts, and prints as `m` definitions, each read back by the
/// checker (`l01_29_diagnostics::shared_parts`), in work that grows with `m`, not `2^m`.
/// Small instances: `a_doubled_tuple_names_each_level_once`.
#[test]
fn a_type_doubled_to_depth_n_prints_in_n_definitions() {
    let n = 2_000;
    scaling::check("building and printing a tuple doubled to depth n", n, |m| {
        let t = doubled(Type::tuple(vec![Type::int(), Type::int()]), m);
        let s = t.surface();
        assert_eq!(s.defs.len(), m);
        assert_eq!(s.root, format!("(Part{m}, Part{m})"));
    });
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

/// Small instances: `a_cycle_of_parts_written_by_name_is_defined`. Each ring is printed once
/// when built, so every run measured is a print after the first, at both sizes: `scaling`
/// compared the run at `n`, after its warm-up, with the first run at `8n` (until author A160,
/// 2026-11-20, since when each size runs once), and a first print
/// of a ring costs 1.5 times a later one (304 and 192 million instructions at 2,000 parts),
/// so that comparison measured 9.96 times. Until item PERF-print-by-name-after-plain the
/// instances that part cycles kept alive (`rec::unfold::Env::forget`) made the first print at
/// `8n` cheaper (9.07 times then). Here 8.80 times; measured alone, in a process of its own
/// for each size, a later print takes 9.21 times the instructions at 16,000 parts, a first
/// print 8.76.
#[test]
fn a_long_cycle_of_parts_written_by_name_scales() {
    let n = 2_000;
    let built: BTreeMap<usize, Type> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let t = part_ring(m);
            assert_eq!(
                t.surface_by_name(super::super::TextPlace::Any).defs.len(),
                m + 1
            );
            (m, t)
        })
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

/// Small instances: `a_cycle_of_parts_written_by_name_is_defined`, and in `rec::group::tests`
/// `an_instance_whose_parts_were_unfolded_is_freed_at_the_end_of_its_unit`. Item
/// PERF-print-by-name-after-plain: a [`part_ring`] printed plain then by name, then a second
/// one by name then plain. Neither order costs more: plain first measured 10.48 times and by
/// name first 8.88 at f0086dfbf because the end of a unit forgot the unfoldings of a group's
/// members but not of its parts, whose unfoldings refer to each other in a cycle, so the
/// instance and its group stayed alive to the end of the process, and the warm-up's left the
/// run at `n` less to make than the first run at `8n`. Each ring is built in the run, the
/// second after the first is dropped, so every print is a first print. Measured apart, 2,000
/// and 16,000 parts, printing alone (instructions, building subtracted), before the fix: the
/// first pair 8.81 times plain first and 8.90 by name first, a pair after the first 9.10 and
/// 9.01.
#[test]
fn a_ring_of_parts_printed_plain_and_by_name_scales_in_either_order() {
    let n = 2_000;
    scaling::check(
        "building and printing a ring of parts kept unevaluated, plain then by name and by \
         name then plain",
        n,
        |m| {
            let by_name = |t: &Type| t.surface_by_name(super::super::TextPlace::Any).defs.len();
            let t = part_ring(m);
            assert!(!t.surface().root.is_empty());
            assert_eq!(by_name(&t), m + 1);
            drop(t);
            // On a thread of its own: the memos the first left on this thread made the second
            // ring's prints take less than half a first print's instructions.
            std::thread::scope(|s| {
                s.spawn(|| {
                    let t = part_ring(m);
                    assert_eq!(by_name(&t), m + 1);
                    assert!(!t.surface().root.is_empty());
                });
            });
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
/// building and printing by name 8.7, plain 8.7. Until item PERF-print-by-name-after-plain an
/// instance whose parts were unfolded stayed alive to the end of the process
/// (`rec::unfold::Env::forget`); freed at the end of its unit, this measures 8.61 times
/// (10.16 before, both at load near 40).
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
