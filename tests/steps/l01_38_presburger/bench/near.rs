//! The benchmarks of `near.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::near::*;
use zed_tests::scaling;
use zedc::store::negsssp::potential_alone;

#[test]
fn duong_scales_alone() {
    let (small, large) = (feasible(512, 1), feasible(scaling::FACTOR * 512, 1));
    for out in [&small, &large] {
        let p = potential_alone(out).expect("no negative cycle");
        assert!(holds(out, &p));
    }
    scaling::check("Duong's search, random graphs by n", 512, |n| {
        let out = if n == 512 { &small } else { &large };
        std::hint::black_box(potential_alone(out));
    });
}
