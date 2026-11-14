//! Phase 1's time on nested loops, and the time of their weak topological order, each linear
//! in the depth (COMPLEXITY.md S3, S9). What [`evals`] asserts, that the order nests every
//! loop in the one around it, is checked at depths 1 to 48 by
//! `scaling::nested_loops_cost_linear_work_in_the_depth`.

use zed_tests::scaling;
use zedc::store::iterate::order;

use crate::scaling::{Nest, evals};

#[test]
fn the_nest_scales() {
    scaling::check("phase 1 on nested loops", 6, |depth| {
        evals(depth);
    });
}

/// The order of the nest: the recursive algorithm traversed each component again at every
/// level, so its cost grew as the square of the depth (COMPLEXITY.md S9).
#[test]
fn the_order_of_nested_loops_takes_time_linear_in_the_depth() {
    // A deep nest is dropped one level per stack frame.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check("the weak topological order of nested loops", 1000, |d| {
                order(&Nest::new(d)).unwrap();
            });
        })
        .expect("a thread")
        .join()
        .expect("the check passes");
}
