//! The benchmark of `revision`, run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates, author P178: a test that needs an unusual size is a benchmark).
//! It sweeps `backward` over operands with ends in `-4..=4`, about 575,000 triples;
//! `backward_transfer_keeps_every_operand_that_can_give_the_result` in the tests of
//! `revision.rs` makes the same checks on operands with ends in `{-2, 0, 1, 3}`.

use super::tests::{backward_keeps_every_operand, operands};

/// `backward` keeps every operand that can give the result: `x` over every operand, `y` over
/// every third and `z` over every fourth.
#[test]
fn backward_transfer_keeps_every_operand_on_the_full_sweep() {
    let all = operands();
    let ys: Vec<_> = all.iter().step_by(3).cloned().collect();
    let zs: Vec<_> = all.iter().step_by(4).cloned().collect();
    backward_keeps_every_operand(&all, &ys, &zs);
}
