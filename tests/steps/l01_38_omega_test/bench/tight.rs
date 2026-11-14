//! The benchmarks of `tight.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::scaling::decides;
use crate::tight::*;
use zedc::store::presburger::Refusal;

#[test]
fn the_tight_three_term_family_scales() {
    decides(
        "the tight three-term family",
        1100,
        Err(Refusal::Growth),
        |n| tight(n, 0xfeed_beef_1380),
    );
}
