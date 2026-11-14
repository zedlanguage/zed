//! Benchmarks of `xst::s4`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// [`relation_points_written_after`] backward: each test is kept with the points of its
/// cases, and each constraint rereads only the tests that fix its own `x_i`, so near linear
/// time in the number of tests. The answers are checked at a small size in
/// `points_of_relations_written_after_are_dropped`. Sized at 64 tests: at load 24 to 31 the
/// one run at 64 takes 0.16 s and at 512 1.6 s, the whole check (warm-up, first and least
/// runs of each size) 4.7 s; at 128 the check took 15 s and at 256 it passed the 20 s limit.
#[test]
fn points_of_relations_written_after_scale() {
    let inputs = scaling::inputs(64, relation_points_written_after);
    scaling::check_order(
        "points of relations written after, Backward, k tests",
        64,
        1,
        |m| {
            drop(inputs[&m].narrowed(How::Backward));
        },
    );
}
