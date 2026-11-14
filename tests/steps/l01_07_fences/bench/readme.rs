//! Reading a page's stated results and comparing them with the table of expected results is
//! linear in the number of fences: the benchmark of `readme/scaling.rs`, whose test compares a
//! generated page of a few sections.

use zed_tests::scaling::check;

use crate::readme::problems;
use crate::readme::scaling::inputs;

#[test]
fn reading_and_comparing_stated_results_is_linear() {
    let n = 4_000;
    let small = inputs(n);
    let large = inputs(8 * n);
    check("README stated results, by fences", n, |size| {
        let (page, fences, table) = if size == n { &small } else { &large };
        assert!(problems(page, fences, table).is_empty());
    });
}
