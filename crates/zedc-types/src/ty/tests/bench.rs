//! The tests of `ty::tests` at unusual sizes (author P178), run by `tools/run_tests.sh --bench`
//! and left out of its default run (TEST-bench-move-crates). The correctness tests that keep
//! what each checks at small sizes are
//! `the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows` and
//! `the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes`.

use super::*;

/// The comparisons of the index tests on large overloads: four cases of 300 arrows of the
/// plain shapes, and four of 90 arrows of the wider shapes, the largest sizes those tests had.
/// Each verdict is checked against every set of arrows as there; only the sizes differ.
#[test]
fn the_index_of_arrows_gives_the_verdict_on_large_overloads() {
    let mut rng = Rng(crate::seed::seed(
        "the_index_of_arrows_gives_the_verdict_on_large_overloads",
    ));
    let mut counts = Counts::default();
    for case in 0..4 {
        index_case(&mut rng, 300, case, &mut counts);
        wider_case(&mut rng, 90, case, &mut counts);
    }
}
