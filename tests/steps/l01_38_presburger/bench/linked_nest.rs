//! The benchmarks of `linked_nest.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::linked_nest::*;
use zed_tests::scaling::{self};
use zedc::store::presburger::{Formula, project_each};

#[test]
fn a_linked_nest_projects_in_time_linear_in_its_depth() {
    let sizes = [16, 32, 64, 128];
    let w: Vec<i64> = (0..=128).map(|i| 1i64 << (1 + i % 50)).collect();
    let inputs = scaling::inputs(16, |k| nest(k, &w, (2, 1), true));
    let syms = [v("x0")];
    let all: Vec<(usize, Formula)> = sizes
        .iter()
        .map(|&k| (k, nest(k, &w, (2, 1), true)))
        .collect();
    exponents("project_each of the linked nest, x[k] odd", &sizes, |k| {
        let f = &all.iter().find(|(n, _)| *n == k).expect("an input").1;
        let (each, _) = project_each(f, &syms).expect("an answer");
        assert!(
            matches!(&each[0], Ok(s) if s.is_empty()),
            "no way has x[k] odd"
        );
    });
    scaling::check("project_each of a linked nest k deep, x[k] odd", 16, |k| {
        let (each, _) = project_each(&inputs[&k], &syms).expect("an answer");
        assert!(
            matches!(&each[0], Ok(s) if s.is_empty()),
            "no way has x[k] odd"
        );
    });
}

#[test]
fn twin_linked_nests_project_in_time_linear_in_their_depth() {
    let sizes = [4, 8, 16, 32];
    let w: Vec<i64> = (0..=32).map(|i| 1i64 << i).collect();
    let syms = [v("x0"), v("y0")];
    let all: Vec<(usize, Formula)> = sizes
        .iter()
        .map(|&k| (k, twin(k, &w, (2, 1), true)))
        .collect();
    exponents(
        "project_each of the twin nests, x[k] + y[k] odd",
        &sizes,
        |k| {
            let f = &all.iter().find(|(n, _)| *n == k).expect("an input").1;
            project_each(f, &syms).expect("an answer");
        },
    );
    let inputs = scaling::inputs(4, |k| twin(k, &w, (2, 1), true));
    scaling::check("project_each of twin linked nests k deep", 4, |k| {
        project_each(&inputs[&k], &syms).expect("an answer");
    });
}
