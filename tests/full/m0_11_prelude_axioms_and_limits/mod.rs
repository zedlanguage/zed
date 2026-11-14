//! The step limit of compile-time evaluation at its minimum, 10,000,000 steps: about 14 s at
//! each side, too long for the local suite, whose test
//! `m0_11_prelude_axioms_and_limits::limits::the_step_past_the_fuel_is_refused` checks the same
//! boundary at small fuel. It needs no tool outside the Rust toolchain.

use zed_kernel::eval::MIN_STEPS;
use zed_kernel::{KernelError, Value};

#[path = "../../steps/m0_11_prelude_axioms_and_limits/leaves.rs"]
mod leaves;

use leaves::{count_leaves, with_fuel};

#[test]
fn ten_million_steps_are_accepted() {
    // 5,000,000 items make 9,999,999 calls.
    let within = count_leaves(5_000_000);
    assert_eq!(with_fuel(MIN_STEPS, &within), Ok(Value::Int(5_000_000)));
}

#[test]
fn the_step_past_ten_million_is_refused() {
    // 5,000,001 items make 10,000,001 calls.
    assert_eq!(
        with_fuel(MIN_STEPS, &count_leaves(5_000_001)),
        Err(KernelError::OutOfFuel)
    );
}
