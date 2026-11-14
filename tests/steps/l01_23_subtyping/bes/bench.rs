//! The benchmarks of `bes.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `bes.rs`.

use super::*;

#[test]
fn the_families_scale() {
    for name in FAMILIES {
        scales(name, 512);
    }
}

#[test]
fn the_widened_families_scale() {
    for name in WIDENED {
        scales(name, 4096);
    }
}

/// Deciding [`long_run`] of `n` and `8n` unions: the test of union edges reads each edge once,
/// with the run of unions after each node counted once (`bes::one_cycle_but_union_chords`),
/// where walking each edge along the cycle would take `n` steps an edge.
#[test]
fn a_long_run_of_union_edges_scales() {
    let n = 4096;
    let small = long_run(n).bes();
    let large = long_run(scaling::FACTOR * n).bes();
    scaling::check_order("deciding a run of n unions with union edges", n, 1, |m| {
        let g = if m == n { &small } else { &large };
        std::hint::black_box(decide(std::hint::black_box(g)));
    });
}
