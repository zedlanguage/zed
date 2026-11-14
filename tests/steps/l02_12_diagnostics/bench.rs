//! Printing a diagnostic that quotes a string of n bytes is linear in n: the benchmark of this
//! step, run by `tools/run_tests.sh --bench` and left out of its default run
//! (TEST-bench-move-rest). Its check besides the ratio is made at small sizes by
//! `a_quoted_string_of_a_few_escapes_prints_escaped`.

use zed_tests::scaling;

use crate::{prints_no_esc, quoted};

#[test]
fn printing_a_quoted_string_scales() {
    let inputs = scaling::inputs(4000, quoted);
    scaling::check_order("a diagnostic quoting a string of n bytes", 4000, 1, |n| {
        let (d, t) = &inputs[&n];
        prints_no_esc(d, t);
    });
}
