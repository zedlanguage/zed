//! The benchmark of `solve_names_tests`, run by `tools/run_tests.sh --bench` and left out of
//! its default run. The correctness test that keeps a small instance of it is
//! `two_tied_remainder_rows_are_answered_alike_under_every_naming`.

use super::*;
use crate::scaling;

/// The whole of `solve` on [`tied_remainders`] with `n` division pairs, which the Omega test
/// refuses: the count of rows of two terms or more holding each class, which tells the tied
/// remainder rows' unit terms apart in `modular::solve_modular_whole` (step 3), and the point
/// the modular solver finds by it. The count is one pass over the rows, O(r) lookups for r
/// terms, so the whole stays at the order of `division_pairs_refused_scale` (modular r7).
#[test]
fn tied_remainders_scale() {
    let inputs = scaling::inputs(N_TIED, |n| {
        let (vars, rows) = tied_remainders(1000, [-1200, -1201, -1202], n, false);
        let name: Vec<String> = (0..vars).map(|i| format!("z{i:06}")).collect();
        cons(&rows, &name)
    });
    scaling::check_order("tied remainder rows answered by solve", N_TIED, 1, |n| {
        assert!(matches!(solve(&inputs[&n], false), Ok(Some(_))));
    });
}

/// The size of [`tied_remainders_scale`].
const N_TIED: usize = 4_000;
