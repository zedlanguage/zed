//! The checks of `scaling.rs` at `n` and `8n`. Each input is built before the timing.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zedc::run::load;
use zedc::stage::ends;

use crate::scaling::{
    Shape, a_chain_staged, a_deep_unit_colored, a_deep_unit_mixed, callers, chain, deep_unit,
    every_function_split, function_values, function_values_left, many_callees,
    nested_lets_calling_len, the_values_passed,
};

/// Checks that staging `chain(n, all)` scales, `what` naming it, with the program loaded
/// before timing: loading it, which parses, checks and elaborates, did 7 to 9 times the work
/// of staging, enough to hide a quadratic added to it (COMPLEXITY.md F85).
fn mixing_scales(what: &'static str, n: usize, all: bool) {
    let progs = scaling::inputs(n, |k| load(chain(k, all).as_bytes()).unwrap());
    scaling::check(what, n, |k| {
        a_chain_staged(&progs[&k]);
    });
}

#[test]
fn mixing_a_chain_of_local_definitions_scales() {
    mixing_scales("mixing a chain of n run-stage definitions", 400, false);
}

#[test]
fn mixing_a_term_that_reads_every_definition_scales() {
    mixing_scales(
        "mixing a chain of n definitions all read at the end",
        200,
        true,
    );
}

#[test]
fn definitions_whose_values_are_functions_are_left_to_run_in_time_that_scales() {
    // Each is run as written and left, with the reason read off the error in O(1).
    let n = 300;
    let progs = scaling::inputs(n, |k| load(function_values(k).as_bytes()).unwrap());
    scaling::check("n definitions whose values are functions", n, |k| {
        function_values_left(&progs[&k]);
    });
}

#[test]
fn the_values_passed_by_many_definitions_are_read_in_time_that_scales() {
    // Each definition was looked for among the names of all of them.
    let n = 2000;
    let units = scaling::inputs(n, |k| elab(&callers(k)).unwrap());
    scaling::check("the values passed by n definitions", n, |k| {
        the_values_passed(&units[&k], k);
    });
}

#[test]
fn the_form_rule_on_many_nested_lets_calling_a_prelude_word_scales() {
    // Each call through a name looked for it among every name bound around the call, and a
    // prelude word is bound by none of them.
    let n = 1000;
    let terms = scaling::inputs(n, nested_lets_calling_len);
    scaling::check("the form rule on n nested lets", n, |k| {
        assert!(ends(&terms[&k]));
    });
}

#[test]
fn splitting_many_functions_of_one_unit_scales() {
    // Each split mixed the whole unit again to find the values its calls pass, so splitting
    // each of `n` functions took `O(n²)`; the calls are now read from one mix.
    let n = 650;
    let units = scaling::inputs(n, |k| elab(&many_callees(k)).unwrap());
    scaling::check_order("splitting n functions of a unit", n, 1, |k| {
        every_function_split(&units[&k], k);
    });
}

/// Checks that mixing and coloring `shape`, and deciding that the sum ends, take time linear
/// in the depth, 6,250 and 50,000 deep, on a stack of 2 MiB. Reading the free names, the
/// effects and whether a term ends, indexing it and mixing it each recursed once per level of
/// the term, and overflowed this stack near 10,000 levels. One test per shape: the four
/// together took 28 s alone at load 41, and each alone took 11 s to 34 s at load 60 at 12,500 and
/// 100,000 deep, so they run at half that depth since TEST-bench-move-l0125 (author P169).
fn staged_on_a_2_mib_stack(shape: Shape) {
    let n = 6_250;
    let what = shape.name();
    zed_tests::deep::on_small_stack(move || {
        let units = scaling::inputs(n, |k| deep_unit(shape, k));
        scaling::check_order(&format!("mixing {what}"), n, 1, |k| {
            a_deep_unit_mixed(&units[&k].0, shape);
        });
        scaling::check_order(&format!("coloring {what}"), n, 1, |k| {
            a_deep_unit_colored(&units[&k].0);
        });
        scaling::check_order("deciding that a sum ends", n, 1, |k| {
            assert!(ends(&units[&k].1));
        });
    });
}

#[test]
fn a_let_chain_50000_deep_is_staged_on_a_2_mib_stack() {
    staged_on_a_2_mib_stack(Shape::Chain);
}

#[test]
fn a_left_nested_sum_50000_deep_is_staged_on_a_2_mib_stack() {
    staged_on_a_2_mib_stack(Shape::Sum);
}

#[test]
fn ifs_50000_deep_are_staged_on_a_2_mib_stack() {
    staged_on_a_2_mib_stack(Shape::Ifs);
}

/// The bound (author decision P300, the proof at `Maps` in `crates/zedc-stage/src/stage.rs`):
/// each of the `n` names pushed copies one path of the scope's trie, about `log2 n + 5` map
/// nodes, so `n (log2 n + 4.95)` nodes in all (counted: 109,728 at 6,250 and 1,027,972 at 50,000,
/// 9.37 times), each made once, `O(n log n)`. The table of those nodes doubles as it fills to
/// 7/8 of its buckets, and its rehashes cost in all about twice its final buckets, which are
/// `2^17` at 6,250 but `2^21` at 50,000 (1,027,972 passes `7/8 · 2^20`), 16 times. Counted
/// 2026-11-20 with the table made at its final size up front: coloring 176.4 M and 1,533.6 M
/// instructions, mixing 212.0 M and 1,818.6 M, so the rehashes cost 46.1 M and 46.2 M at 6,250.
/// The prediction, that rest plus 16 times the rehashes at 6,250 over the whole at 6,250, is
/// 10.21 for coloring and 9.90 for mixing; measured 10.225 and 9.914.
#[test]
fn lambdas_50000_deep_are_staged_on_a_2_mib_stack() {
    staged_on_a_2_mib_stack(Shape::Lams);
}
