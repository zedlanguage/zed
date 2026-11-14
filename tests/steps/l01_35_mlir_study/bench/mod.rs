//! The benchmarks of the MLIR study, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-rest). Each check they make besides the ratio is made at small
//! sizes by a correctness test: of the step's `mod.rs` for the benchmark here, and of the module
//! whose name each file bears for the others.

use zed_tests::scaling::check_order;

use crate::{struct_variants, variants};

mod layout;

#[test]
fn reading_the_variants_is_linear_in_the_source() {
    let n = 20_000;
    let (small, large) = (struct_variants(n), struct_variants(8 * n));
    check_order("reading the variants of an enum of n variants", n, 1, |k| {
        let found = variants(if k == n { &small } else { &large }, "Op");
        assert_eq!(found.len(), k);
    });
}
