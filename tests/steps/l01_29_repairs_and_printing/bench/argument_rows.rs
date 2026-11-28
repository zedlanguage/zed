//! The calls of `argument_rows.rs` at `n` and `8n`.

use zed_tests::scaling;

use crate::argument_rows::*;

#[test]
fn the_repairs_of_many_misfit_calls_scale() {
    let n = 200;
    let srcs = scaling::inputs(n, calls);
    scaling::check("the argument-row repairs of n calls", n, |k| {
        calls_offered(&srcs[&k], k);
    });
}
