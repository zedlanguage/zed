//! Phase 1's time on nested loops, and the time of their weak topological order, each linear
//! in the depth (COMPLEXITY.md S3, S9). What [`evals`] asserts, that the order nests every
//! loop in the one around it, is checked at depths 1 to 48 by
//! `scaling::nested_loops_cost_linear_work_in_the_depth`.

use zed_tests::scaling;
use zedc::store::iterate::order;

use crate::scaling::{Nest, evals};

#[test]
fn the_nest_scales() {
    // Depth 1000, up from 6 (SCALE-small-n-rest; DESIGN sec:plan, n log n is under 10.5 only
    // from n = 777), on a stack deep enough for the nest, as the order's check below.
    scaling::on_a_stack(1 << 28, || {
        scaling::check("phase 1 on nested loops", 1000, |depth| {
            evals(depth);
        });
    });
}

/// The order of the nest: the recursive algorithm traversed each component again at every
/// level, so its cost grew as the square of the depth (COMPLEXITY.md S9).
#[test]
fn the_order_of_nested_loops_takes_time_linear_in_the_depth() {
    // A deep nest is dropped one level per stack frame.
    scaling::on_a_stack(1 << 28, || {
        scaling::check("the weak topological order of nested loops", 1000, |d| {
            order(&Nest::new(d)).unwrap();
        });
    });
}
