//! The benchmarks of `bound_sameness.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `bound_sameness.rs`.

use super::*;

// The two checks below were one test, `nested_bounds_scale`, the first at n = 2^11 and the
// second at n = 512; each is now a test of its own (TEST-bench-move-l0123, author P169).

/// A body of `n` nodes whose bounds are equal and nested `log2 n` deep, admitted in time
/// linear in its size. `n` is a power of 2, `1 << d`.
/// TEST-bench-move-l0123, author P169: d was 11, now 14; 1x 0.33 s at load 25.
#[test]
fn a_group_whose_equal_bounds_nest_scales() {
    let d = 14;
    let equal = scaling::inputs(1 << d, |n| nested(n.trailing_zeros() as usize, || r(0)));
    scaling::check("admitting a group whose equal bounds nest", 1 << d, |n| {
        assert!(group(equal[&n].clone()).is_ok());
    });
}

/// A body whose bounds differ and are nested `n` deep, admitted in time linear in its size.
/// TEST-bench-move-l0123, author P169: n was 512, now 140_000; 1x 0.41 s at load 25.
#[test]
fn a_group_whose_differing_bounds_nest_scales() {
    let n = 140_000;
    let differing = scaling::inputs(n, differing_chain);
    scaling::check("admitting a group whose differing bounds nest", n, |n| {
        assert!(group(differing[&n].clone()).is_ok());
    });
}
