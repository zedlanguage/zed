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
