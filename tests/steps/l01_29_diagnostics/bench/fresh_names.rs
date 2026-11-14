//! The variables of `n` functions named beside `n` program names, at `n` and `8n`
//! (`fresh_names.rs`).

use zed_tests::scaling;

use crate::fresh_names::{crowded, variables_named_past_the_program_names};

#[test]
fn naming_variables_beside_many_program_names_scales() {
    // Each of the n functions names its variable past the n names the program binds: a run of
    // them is stepped over at once, so the whole is linear, where trying each name in turn
    // would be n². Negative control, not committed (2026-11-09): trying each name in turn took
    // 18.3 times the work at 600 and 4800, against 8.0 here and a limit of 11.7. At 200 the
    // check of each binding hides the n² lookups (11.9 times, under the limit of 12.25), so the
    // size is 600.
    let n = 1600;
    let inputs = scaling::inputs(n, crowded);
    scaling::check_order(
        "naming the variables of n functions beside n program names",
        n,
        1,
        |size| variables_named_past_the_program_names(&inputs[&size], size),
    );
}
