//! The benchmarks of `admission.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `admission.rs`.

use super::*;

/// The refusal of a chain of `n` definitions, whose path names all of them, is found and
/// written in time linear in `n`.
#[test]
fn a_refusal_through_a_long_path_scales() {
    let n = 512;
    let groups = zed_tests::scaling::inputs(n, chain);
    zed_tests::scaling::check("refusing a group narrowed through a chain", n, |n| {
        let message = Group::new(groups[&n].clone()).unwrap_err().message;
        assert!(message.contains(&format!("`D{}` is named in `D{}`", n - 2, n - 1)));
    });
}
