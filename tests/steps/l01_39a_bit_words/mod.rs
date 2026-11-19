//! Step L1.39a: the bit words `bitAnd`, `bitOr`, `bitXor`, `bitNot`, `shl`, `shr`, `popCount`,
//! `leadingZeros`, `trailingZeros`, `rotl`, `rotr` and `f64Bits` (DESIGN.md sec:domains), kernel
//! primitives on the unbounded `int` with forward transfer on intervals. A negative operand, or
//! an `x` wider than its width, is a type error at the call with its derivation.

mod as_values;
mod bench;
mod completeness;
mod corners;
mod deep;
mod errors;
mod generic;
mod kept_ends;
// Runs executables built with the system C compiler driver, as step L1.36a does.
#[cfg(target_os = "linux")]
mod nan;
mod narrowing;
mod reference;
mod rung2;
mod shapes;
mod transfer;
mod values;

use zed_kernel::{Prim, Value};
use zed_tests::step_helpers::l01_29_diagnostics::{
    accepted_with_main as accepted, rejected_with_main as rejected, with_main as program,
};

/// The value of `x = <expr>;`, printed.
fn x(expr: &str) -> String {
    zed_tests::step_helpers::l01_16_elaboration::value(&format!("x = {expr};\n"), "x")
}

/// The kernel's value of the bit word `p` on machine integers.
fn word(p: Prim, args: &[i64]) -> Value {
    let vs: Vec<Value> = args.iter().map(|&a| Value::Int(a)).collect();
    zed_kernel::bits::word(p, &vs).unwrap_or_else(|e| panic!("{p:?} {args:?}: {e}"))
}
