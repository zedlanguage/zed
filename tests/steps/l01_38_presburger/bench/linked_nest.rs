//! The benchmarks of `linked_nest.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::linked_nest::*;
use zed_tests::scaling;
use zedc::store::presburger::Formula;

#[test]
fn a_linked_nest_projects_in_time_linear_in_its_depth() {
    let sizes = [16, 32, 64, 128];
    let w = even_weights(128);
    let inputs = scaling::inputs(16, |k| nest(k, &w, (2, 1), true));
    let all: Vec<(usize, Formula)> = sizes
        .iter()
        .map(|&k| (k, nest(k, &w, (2, 1), true)))
        .collect();
    exponents("project_each of the linked nest, x[k] odd", &sizes, |k| {
        let f = &all.iter().find(|(n, _)| *n == k).expect("an input").1;
        assert_no_way_has_an_odd_top(f);
    });
    scaling::check("project_each of a linked nest k deep, x[k] odd", 16, |k| {
        assert_no_way_has_an_odd_top(&inputs[&k]);
    });
}

#[test]
fn twin_linked_nests_project_in_time_linear_in_their_depth() {
    let sizes = [4, 8, 16, 32];
    let w = powers_of_two(32);
    let all: Vec<(usize, Formula)> = sizes
        .iter()
        .map(|&k| (k, twin(k, &w, (2, 1), true)))
        .collect();
    exponents(
        "project_each of the twin nests, x[k] + y[k] odd",
        &sizes,
        |k| {
            let f = &all.iter().find(|(n, _)| *n == k).expect("an input").1;
            assert_twin_answered(f);
        },
    );
    let inputs = scaling::inputs(4, |k| twin(k, &w, (2, 1), true));
    scaling::check("project_each of twin linked nests k deep", 4, |k| {
        assert_twin_answered(&inputs[&k]);
    });
}

/// `linked_nest::twin_linked_nests_project_as_written_out_and_keep_every_value` as first
/// written, 4.7 s (2026-11-14, load 25): depths 1 to 3, the first two weights, every residue.
#[test]
fn twin_linked_nests_of_depths_to_3_project_as_written_out_and_keep_every_value() {
    for k in 1..=3 {
        for weight in &WEIGHTS[..2] {
            for (m, r) in RESIDUES {
                twin_projects_as_written_out(k, weight, (m, r));
            }
        }
    }
}
