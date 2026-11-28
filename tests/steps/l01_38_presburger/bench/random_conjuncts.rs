//! The benchmarks of `random_conjuncts.rs` (PRES-conjunct-one-pass), run by
//! `tools/run_tests.sh --bench`.

use std::sync::Arc;

use crate::random_conjuncts::cases;
use zed_tests::scaling;
use zedc::store::presburger::{Atom, Formula, decide, project_each};

/// The first `n` formulas of `random_conjuncts::SEED`, for the larger size of a benchmark.
fn formulas(n: usize) -> Vec<Formula> {
    cases(n * scaling::FACTOR)
        .iter()
        .map(|c| c.formula())
        .collect()
}

/// `decide` on the first 300 and the first 2400 formulas of `random_conjuncts::SEED`. Of the
/// three reads of each formula's top-level conjuncts that PRES-conjunct-one-pass would merge,
/// `decide_written` makes two (`OneRow::of`, `row_sums::read`). The formulas are drawn alike, so
/// the work is linear in their number. Their answers are checked against the points of the box
/// in `random_conjuncts::the_families_of_the_benchmarks_are_answered_at_small_sizes`.
#[test]
fn decide_on_random_small_formulas_scales() {
    let n = 300;
    let fs = formulas(n);
    scaling::check("decide on random small formulas", n, |m| {
        for f in &fs[..m] {
            let _ = std::hint::black_box(decide(f));
        }
    });
}

/// `project_each` onto `x` and `y` of the same formulas: the path that makes all three reads of
/// PRES-conjunct-one-pass (`may_start` in `forced::empty`, `OneRow::of`, `row_sums::read`).
/// Answers checked in
/// `random_conjuncts::the_projections_of_the_benchmarks_are_the_values_of_the_box_at_small_sizes`.
#[test]
fn project_on_random_small_formulas_scales() {
    let n = 300;
    let fs = formulas(n);
    let syms = [Atom::Sym(Arc::from("x")), Atom::Sym(Arc::from("y"))];
    scaling::check("project on random small formulas", n, |m| {
        for f in &fs[..m] {
            let _ = std::hint::black_box(project_each(f, &syms));
        }
    });
}
