//! The benchmarks of elaboration, the checker and the order of a unit at the rule of low
//! complexity (DESIGN.md Part G), run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-rest). Each builds its inputs before timing and makes, at each size, the
//! check that `scaling::each_benchmark_input_elaborates_at_small_sizes` makes at small sizes.
//!
//! A test of elaboration times it alone, from units parsed, resolved and checked before timing
//! ([`Checked`]): on all but one of these families the parser and the checker do 4 to 92 times
//! the work of elaboration, and a test that times them too lets through an added quadratic
//! whose cost at size n is less than 0.4 times all it times (COMPLEXITY.md F85, measured before
//! F86 cut the parser's work by 3 to 4 times).

use std::collections::BTreeMap;

use zed_tests::scaling::{self, FACTOR, inputs};
use zedc::resolve::resolve;

use crate::scaling::{
    big_callee, chain, checks_clean, cycle_graph, defaults_stay_short, differences,
    elaborates_main, elaborates_some, elaborates_two, else_patterns, finds_every_cycle, found,
    front, has_a_test_per_row, last_def_is, named, named_through_a_value, nested, open,
    orders_after_overloads, orders_all, orders_reversed, passing_many_arguments, reversed_chain,
    rows, rows_pass, uses_of_overloads, wide, wide_finds_main,
};
use crate::{Checked, checked, elab};

#[test]
fn defaults_calling_functions_with_defaults_scale() {
    // A call leaving a parameter out held a copy of its default, and the copy's own calls
    // copies of theirs, so the chain's term doubled with each function (2.9 million
    // characters for `main` at `k = 16`).
    let units: BTreeMap<usize, Checked> = [8, FACTOR * 8]
        .into_iter()
        .map(|k| (k, checked(&chain(k))))
        .collect();
    scaling::check("elaborating a chain of defaults, by length", 8, |k| {
        defaults_stay_short(&units[&k]);
    });
}

#[test]
fn the_dependency_order_scales() {
    // Each item waits on the next, so the scan for the first ready item passed every item
    // before it: `n²/2` steps.
    let graphs = inputs(4000, reversed_chain);
    scaling::check("a reversed chain of dependencies, by length", 4000, |n| {
        orders_reversed(&graphs[&n]);
    });
}

#[test]
fn finding_every_cycle_scales() {
    // `n` items: the first half one cycle, each item waiting on the next through a join of
    // its own, so the search goes `n / 2` deep; the second half `n / 4` cycles of two, each
    // with a join of both that the first item waits on. The graphs are built before timing.
    let n = 10_000;
    let graphs = inputs(n, cycle_graph);
    scaling::check("every cycle of n items with joins", n, |k| {
        finds_every_cycle(&graphs[&k], k);
    });
}

#[test]
fn checking_and_ordering_nested_functions_scales() {
    // Each scope ordered its statements by the uses inside them, those of the scopes nested
    // in them too, so a use was read once for each scope around it. Each run of a signature
    // search checked the functions declared inside it again, so the runs multiplied with the
    // depth; and once found, a nested function's writes were made again at each finding.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            // The checker and elaboration are timed apart, each from what comes before it,
            // made before timing.
            let units: BTreeMap<usize, Checked> = [100, FACTOR * 100]
                .into_iter()
                .map(|n| (n, checked(&nested(n))))
                .collect();
            scaling::check("checking functions nested n deep", 100, |n| {
                checks_clean(&units[&n]);
            });
            scaling::check("elaborating functions nested n deep", 100, |n| {
                elaborates_main(&units[&n]);
            });
            let want = (
                Some("int".to_string()),
                Some("T -> T for T in int | f32 | f64 | rat".to_string()),
            );
            assert_eq!(found(&nested(100), 99), want);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn checking_nested_functions_beside_many_others_scales() {
    // A nested function's writes were made again each time its signature was found again,
    // the writes of the functions inside it too.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            let texts = inputs(50, |n| wide(n, 20));
            scaling::check("functions nested n deep beside 20 others", 50, |n| {
                wide_finds_main(&texts[&n], n);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Checks that elaborating the unit `text(m)` is of order m, parsing and checking each size
/// first, so that elaboration is timed alone, and that its last definition is `last`. (Until
/// ELAB-scaling-isolation the checker, which `elaborate` runs first, was timed too: 9 and 16
/// times elaboration's work on the two families below.)
fn elaboration_scales(what: &str, n: usize, text: fn(usize) -> String, last: &str) {
    let units = inputs(n, |m| checked(&text(m)));
    scaling::check(what, n, |m| last_def_is(&units[&m], last));
}

#[test]
fn a_call_naming_many_arguments_scales() {
    // Each named argument was looked for among all the parameters, and the parameters each
    // default reads among all of them.
    elaboration_scales("a call naming n arguments", 8000, named, "y");
}

#[test]
fn a_call_through_a_value_naming_many_arguments_scales() {
    // The same, where the parameter names come from the type of the value called.
    elaboration_scales(
        "a call of a value naming n arguments",
        8000,
        named_through_a_value,
        "h",
    );
}

#[test]
fn a_call_passing_the_atoms_of_many_arguments_by_scales() {
    // Each argument found its atoms by a search of the call's recorded entries; they are now a
    // map by argument span (PASS-at-args). The search costs a few instructions an entry
    // against about 26,000 an argument for elaboration, so it shows only from 4,000
    // arguments: 35.9 times the work at 4,000 and 32,000, and 14.7 at 1,000 and 8,000.
    elaboration_scales(
        "a call of n arguments that each pass atoms by",
        4000,
        passing_many_arguments,
        "g",
    );
}

#[test]
fn ordering_a_function_with_many_rows_scales() {
    // Each use in a row was tested against every row of the function.
    let units = inputs(250, |n| checked(&rows(n)));
    scaling::check("elaborating a function with n rows", 250, |n| {
        has_a_test_per_row(&units[&n], n);
    });
}

#[test]
fn searches_through_nested_functions_scale() {
    // A signature search checked the functions declared in its body again for each type it
    // tried, so the contexts grew about 1.6 times with each level (167 s at 32 deep), until a
    // cap of 64 contexts gave `_` past it. Each body is now checked once: the parameters
    // added together share one class, of the outermost function, so the innermost one's
    // signature is in terms of `h0`'s variable at every depth.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            let texts = inputs(128, open);
            scaling::check("searches through n nested functions", 128, |n| {
                elab(&texts[&n]).unwrap();
            });
            crate::scaling::open_signature_is_h0s(64);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn rows_reaching_a_large_definition_scale() {
    // Each row's key printed every definition it reaches and its run closed it over a copy of
    // each, so `n` rows reaching a function of `n` terms took `O(n²)`; a definition's digest is
    // now made once and its term shared. The front end's result for each size is made before
    // timing, so that the rows alone are timed.
    let t = std::thread::Builder::new().stack_size(1 << 29).spawn(|| {
        let warm = inputs(100, |n| front(&big_callee(n)));
        scaling::check_order("n rows reaching a function of n terms", 100, 1, |n| {
            let (text, db) = &warm[&n];
            rows_pass(text, db, n);
        })
    });
    t.unwrap().join().unwrap();
}

#[test]
fn ordering_many_uses_of_many_overloads_scales() {
    // Each use of an overloaded name was recorded once for each overload, and each statement
    // using it waited on each overload directly, so `k` uses of `k` overloads made `k²`
    // entries and dependencies.
    // The statements and their resolution are built before the timing, so only the tables of
    // uses and the order are measured.
    let n = 1000;
    let built = inputs(n, uses_of_overloads);
    scaling::check("k uses of k overloads, ordered", n, |k| {
        let (stmts, res) = &built[&k];
        orders_after_overloads(stmts, res, k);
    });
}

/// Orders the top-level statements of each program of `shapes` on a 2 MiB stack, 100,000 deep
/// and 12,500 deep, and checks the time is linear. Finding the function declarations inside
/// the statements recursed once per level of nesting, and overflowed this stack near 20,000.
fn ordered_deep(shapes: &[&str]) {
    use zed_tests::deep::{on_small_stack, program, statements};
    let n = 12_500;
    on_small_stack(|| {
        for &shape in shapes {
            let built = inputs(n, |k| {
                let stmts = statements(&program(shape, k).text);
                let res = resolve(&stmts).unwrap();
                (stmts, res)
            });
            scaling::check_order(&format!("ordering {shape}"), n, 1, |k| {
                let (stmts, res) = &built[&k];
                orders_all(stmts, res);
            });
        }
    });
}

#[test]
fn sums_calls_and_long_bodies_100000_deep_are_ordered_on_a_2_mib_stack() {
    ordered_deep(&[
        "a left-nested sum",
        "nested calls",
        "a long sum in a function's body",
    ]);
}

#[test]
fn blocks_and_tuples_nested_100000_deep_are_ordered_on_a_2_mib_stack() {
    ordered_deep(&["nested blocks", "nested tuples"]);
}

/// Elaborates each program of `shapes` on a 2 MiB stack, `n` deep and `8n` deep, and checks
/// the time is linear. Elaboration recursed once per level of nesting. Each program is checked
/// first, on the same stack, and elaboration is timed alone: the checker did 5 to 92 times its
/// work on these shapes, and `l01_26_type_resolution::scaling` times the checker on each.
fn elaborates_deep(shapes: &[&str], n: usize) {
    use zed_tests::deep::{on_small_stack, program, statements};
    on_small_stack(|| {
        for &shape in shapes {
            let units = inputs(n, |k| Checked::new(statements(&program(shape, k).text)));
            scaling::check_order(&format!("elaborating {shape}"), n, 1, |k| {
                elaborates_some(&units[&k], shape);
            });
        }
    });
}

#[test]
fn blocks_nested_100000_deep_elaborate_on_a_2_mib_stack() {
    elaborates_deep(&["nested blocks"], 12_500);
}

// The checker, which runs on each program before it is elaborated, costs about 140,000
// instructions for each `+` and half that for each negation, branch or call (CHK-node-cost, in
// `l01_26_type_resolution::scaling`), so these shapes elaborate 8,000 deep.

#[test]
fn sums_and_else_if_chains_8000_deep_elaborate_on_a_2_mib_stack() {
    elaborates_deep(
        &[
            "a left-nested sum",
            "a sum nested in parentheses",
            "an `else if` chain",
        ],
        1_000,
    );
}

#[test]
fn negations_and_calls_8000_deep_elaborate_on_a_2_mib_stack() {
    // Nested tuples are left out: the checker takes time superlinear in their depth (open).
    elaborates_deep(&["nested negations", "nested calls"], 1_000);
}

/// Checks and elaborates `text(n)` and `text(8n)` on a 2 MiB stack, and checks that the time of
/// each is linear, timed apart: the checker did up to 7 times the work of elaboration on these.
fn elaborates_text_deep(what: &str, n: usize, text: fn(usize) -> String) {
    use zed_tests::deep::{on_small_stack, statements};
    on_small_stack(|| {
        let units = inputs(n, |k| Checked::new(statements(&text(k))));
        scaling::check_order(&format!("checking {what}"), n, 1, |k| {
            checks_clean(&units[&k]);
        });
        scaling::check_order(&format!("elaborating {what}"), n, 1, |k| {
            elaborates_two(&units[&k], what);
        });
    });
}

#[test]
fn a_type_100000_deep_elaborates_on_a_2_mib_stack() {
    elaborates_text_deep("a difference of types", 12_500, differences);
}

// The kernel's `Pattern` drops its parts by recursion (ZED_PORT_GAPS.md), so a pattern 100,000
// deep overflows a 2 MiB stack whatever elaborates it; these go 10,000 deep.

#[test]
fn else_patterns_10000_deep_elaborate_on_a_2_mib_stack() {
    elaborates_text_deep("a pattern by position", 1_250, |n| else_patterns(n, false));
    elaborates_text_deep("a pattern by name", 1_250, |n| else_patterns(n, true));
}
