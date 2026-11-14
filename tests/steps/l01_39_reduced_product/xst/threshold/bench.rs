//! Benchmarks of `xst::threshold`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// O(N log N) in the parts at a fixed hub width.
#[test]
fn the_walk_is_solved_in_near_linear_time() {
    let inputs = scaling::inputs(500, |n| walk(n, 1));
    scaling::check("threshold walk, n parts", 500, |m| {
        drop(threshold::solve(&inputs[&m]));
    });
}

/// O(log W) propagations in the hub's width W: at a fixed number of parts, a hub of width
/// `W^8` costs at most 8 times one of width `W` and a little more, not `W^7` times.
#[test]
fn the_hub_search_scales_with_the_digits_of_its_width() {
    // The greatest hub value that passes is in the middle of the hub's values: the walk's last
    // name is at most `w/2 + 1`.
    let make = |digits: usize| {
        let w = 10i64.pow(digits as u32);
        let mut sys = walk(50, w);
        sys.uppers.push(upper(49, 1, w + 1));
        sys
    };
    let inputs = scaling::inputs(2, make);
    scaling::check("threshold hub search, digits of the hub's width", 2, |d| {
        drop(threshold::solve(&inputs[&d]));
    });
}
