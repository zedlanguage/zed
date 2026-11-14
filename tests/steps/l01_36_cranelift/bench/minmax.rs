//! A fold of `min` compiles and runs natively in work linear in its length, inline, and gives
//! the kernel's value (COMPLEXITY.md Z15, the passes of the code generator). The small
//! instances are in `minmax.rs`.

use zed_tests::scaling;

use crate::minmax::fold_agrees;

#[test]
fn a_fold_of_min_scales_linearly() {
    scaling::on_a_thread(1 << 29, || {
        scaling::check("a fold of min over n floats", 3_000, fold_agrees)
    });
}
