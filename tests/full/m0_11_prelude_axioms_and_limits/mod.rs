//! No count of steps stops compile-time evaluation (DESIGN.md step M0.11: "there is no minimum
//! of steps or of memory, since no count of either may stop compile-time evaluation"). The
//! evaluator with its default settings, which have no fuel, runs one step past 10,000,000, the
//! minimum of steps that step M0.11 fixed before the author's decision of 2026-11-09: 17.7 s at
//! load 35, too long for the local suite, whose test
//! `m0_11_prelude_axioms_and_limits::limits::with_no_fuel_no_count_of_steps_stops_the_evaluation`
//! runs the same program at small sizes. It needs no tool outside the Rust toolchain.

use zed_kernel::{Value, eval};

#[path = "../../steps/m0_11_prelude_axioms_and_limits/leaves.rs"]
mod leaves;

use leaves::count_leaves;

#[test]
fn ten_million_and_one_steps_run_with_no_fuel() {
    // 5,000,001 items make 10,000,001 calls, one past the old minimum.
    assert_eq!(eval(&count_leaves(5_000_001)), Ok(Value::Int(5_000_001)));
}
