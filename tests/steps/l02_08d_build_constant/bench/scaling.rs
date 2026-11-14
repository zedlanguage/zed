//! The reads of `build` are replaced in time linear in the program: the benchmark of
//! `scaling.rs`.

use crate::scaling::{fast_build, front_passes};

#[test]
fn reads_scale_linearly() {
    let build = fast_build();
    zed_tests::scaling::check_order("the front end over n reads of `build`", 2000, 1, |n| {
        front_passes(&build, n);
    });
}
