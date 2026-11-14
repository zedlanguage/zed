//! Complexity tradeoff (COMPLEXITY.md F85, STAGE-generic-fold): an operation on generic
//! literals alone reads its witness once and is built once per carrier, at most six, inside one
//! `match`, so a sum of n literals elaborates to O(n) nodes in O(n) time. Built as before, one
//! `match` per literal and each partial sum bound by a `let`, it was O(n) too, but the build
//! stage could not fold it. Small instance: `an_operation_on_several_literals_is_one_match`.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::checked;

use super::super::operations::chain;

#[test]
fn an_operation_on_many_literals_elaborates_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let units = scaling::inputs(100_000, |m| checked(&chain(m)));
        scaling::check(
            "elaborating an operation on n generic literals",
            100_000,
            |m| {
                units[&m].elab();
            },
        );
    });
}
