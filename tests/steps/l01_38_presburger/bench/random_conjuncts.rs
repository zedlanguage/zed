//! The benchmark of `random_conjuncts.rs` (PRES-conjunct-one-pass), run by
//! `tools/run_tests.sh --bench`.

use crate::random_conjuncts::cases;
use zed_tests::scaling;
use zedc::store::presburger::{Formula, decide};

/// `decide` on the first 300 and the first 2400 formulas of `random_conjuncts::SEED`. The
/// instructions it prints are the measure of PRES-conjunct-one-pass: three reads of each
/// formula's top-level conjuncts (`may_start`, `OneRow::of`, `row_sums::read`) against one read
/// giving all three answers. The formulas are drawn alike, so the work is linear in their number.
/// Their answers are checked against the points of the box in
/// `random_conjuncts::the_families_of_the_benchmarks_are_answered_at_small_sizes`.
#[test]
fn decide_on_random_small_formulas_scales() {
    let n = 300;
    let fs: Vec<Formula> = cases(n * scaling::FACTOR)
        .iter()
        .map(|c| c.formula())
        .collect();
    scaling::check("decide on random small formulas", n, |m| {
        for f in &fs[..m] {
            let _ = std::hint::black_box(decide(f));
        }
    });
}
