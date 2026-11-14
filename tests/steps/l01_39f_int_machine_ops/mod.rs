//! Step L1.39f: the integer machine operations `mulHi`, `bitReverse`, `byteSwap`, `pdep`,
//! `pext`, `funnelShl` and `funnelShr` (DESIGN.md sec:linalg, machine operations), kernel
//! primitives on the unbounded `int` with the operand domains of the bit words and forward
//! transfer on intervals. An operand outside its domain is a type error at the call with its
//! derivation: a negative one, one read as `width` digits that is not below `2 ^ width`, a
//! funnel shift's `k` that is not below `width`, and a width of `byteSwap` that is not a
//! multiple of 8.

mod bench;
mod completeness;
mod errors;
mod native;
mod pext_popcount;
mod reference;
mod transfer;
mod values;

use zed_kernel::{Prim, Value};
use zedc::run::load;

/// The value of `x = <expr>;`, printed.
fn x(expr: &str) -> String {
    zed_tests::step_helpers::l01_16_elaboration::value(&format!("x = {expr};\n"), "x")
}

/// `src` as a whole program: a `main` is added when it declares none.
fn program(src: &str) -> String {
    match src.contains("main(") {
        true => src.to_string(),
        false => format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n"),
    }
}

/// The rendered diagnostics of the rejected program `src`.
fn rejected(src: &str) -> String {
    match load(program(src).as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e,
    }
}

/// Whether the program `src` is accepted.
fn accepted(src: &str) -> bool {
    load(program(src).as_bytes()).is_ok()
}

/// The kernel's value of the word `p` on machine integers.
fn word(p: Prim, args: &[i64]) -> Value {
    let vs: Vec<Value> = args.iter().map(|&a| Value::Int(a)).collect();
    zed_kernel::bits::word(p, &vs).unwrap_or_else(|e| panic!("{p:?} {args:?}: {e}"))
}
