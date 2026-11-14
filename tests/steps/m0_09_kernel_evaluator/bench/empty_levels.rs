//! Empty inner levels at the rule of low complexity: building, reading back, a rekey of the
//! outer level, a discard and a fold of `n` classes, linear in `n`. What it asserts besides its
//! ratio is checked at small sizes by
//! `empty_levels::empty_levels_are_built_read_rekeyed_filtered_and_folded_at_small_sizes`.

use zed_kernel::term::build::lit;
use zed_tests::scaling;

use crate::empty_levels::{classes, empty_levels_pass};

#[test]
fn empty_levels_scale() {
    let n = 2000;
    let inputs = scaling::inputs(n, |n| lit(classes(n)));
    // Build, read back, rekey, filter (emptying the levels with a negative entry) and fold.
    scaling::check(
        "empty levels: building, leaves, a rekey of the outer level, a discard and a fold, by \
         classes",
        n,
        |n| empty_levels_pass(n, &inputs[&n]),
    );
}
