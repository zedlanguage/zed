//! The benchmarks of `canonical.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::canonical::*;
use zed_tests::instances::Rng;
use zed_tests::scaling;

#[test]
fn refinement_scales() {
    let n = 7_200;
    let chains = (pipeline(n), pipeline(scaling::FACTOR * n));
    scaling::check("colors of a pipeline", n, |m| {
        drop(colors(if m == n { &chains.0 } else { &chains.1 }));
    });
    let mut rng = Rng::new(0xCA_0002);
    let sparse = (
        random(&mut rng, n, 2 * n, "v"),
        random(&mut rng, scaling::FACTOR * n, 2 * scaling::FACTOR * n, "v"),
    );
    scaling::check("colors of a random sparse system", n, |m| {
        drop(colors(if m == n { &sparse.0 } else { &sparse.1 }));
    });
}

/// The 2400 and 1800 shuffles of the CANON-stable verifier (plan row
/// TESTS-random-batteries-to-size), 420 systems of 10 each. Correctness test:
/// `colors_follow_random_namings_and_row_orders_of_random_systems`, 400 shuffles.
#[test]
fn colors_follow_4200_random_namings_and_row_orders() {
    scaling::timed("4200 shuffles", || {
        colors_follow_random_namings_and_row_orders(
            "colors_follow_4200_random_namings_and_row_orders",
            420,
            10,
        )
    });
}
