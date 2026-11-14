//! Complexity tradeoff (COMPLEXITY.md F85, STAGE-generic-fold): an operation on generic
//! literals alone reads its witness once and is built once per carrier, at most six, inside one
//! `match`, so a sum of n literals elaborates to O(n) nodes in O(n) time. Built as before, one
//! `match` per literal and each partial sum bound by a `let`, it was O(n) too, but the build
//! stage could not fold it. Small instance: `an_operation_on_several_literals_is_one_match`.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::checked;

use super::super::operations::{chain, mixed_chain};

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

/// The same with `/`, decimals and `^` among the literals (STAGE-generic-fold-div): each
/// operation's carrier in every arm is read from its operands' arms in O(C), C ≤ 4, so a sum of
/// n such terms is still one `match` built in O(n) time. Small instance:
/// `a_sum_of_quotients_decimals_and_powers_is_one_match`. Sizes 2,000 and 16,000:
/// checking the input, done before the timing, takes most of the run; at 100,000 and 800,000
/// the whole test took about 250 s.
#[test]
fn a_sum_of_quotients_decimals_and_powers_elaborates_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let units = scaling::inputs(2_000, |m| checked(&mixed_chain(m)));
        scaling::check(
            "elaborating a sum of n quotients, decimals and powers of generic literals",
            2_000,
            |m| {
                units[&m].elab();
            },
        );
    });
}
