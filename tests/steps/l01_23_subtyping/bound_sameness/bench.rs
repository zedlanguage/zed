//! The benchmarks of `bound_sameness.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `bound_sameness.rs`.

use super::*;

/// A body of `n` nodes whose bounds are equal and nested `log2 n` deep, and one whose bounds
/// differ and are nested `d` deep, each admitted in time linear in its size.
#[test]
fn nested_bounds_scale() {
    let d = 11;
    let equal = scaling::inputs(1 << d, |n| nested(n.trailing_zeros() as usize, || r(0)));
    scaling::check("admitting a group whose equal bounds nest", 1 << d, |n| {
        assert!(group(equal[&n].clone()).is_ok());
    });
    // `(((int) .. int -> int) .. int -> int)`: the guarantee of each level is the level below.
    let differ = |d: usize| {
        (0..d).fold(ty(Type::bool()), |l, _| {
            m(l, ty(Type::int()), ty(Type::int()))
        })
    };
    let n = 512;
    let differing = scaling::inputs(n, differ);
    scaling::check("admitting a group whose differing bounds nest", n, |n| {
        assert!(group(differing[&n].clone()).is_ok());
    });
}
