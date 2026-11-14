//! Finding the kinds of build in DESIGN.md is linear in its lines: the benchmark of `modes.rs`.

use zed_tests::scaling;

use crate::modes::{kinds_found, lines_of_builds};

#[test]
fn finding_the_kinds_of_build_is_linear() {
    let texts: Vec<(usize, String)> = [3000, 24000]
        .into_iter()
        .map(|n| (n, lines_of_builds(n)))
        .collect();
    scaling::check_order("finding the kinds of build in n lines", 3000, 1, |n| {
        let (_, text) = texts.iter().find(|(m, _)| *m == n).unwrap();
        kinds_found(text, n);
    });
}
