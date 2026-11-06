//! Step L1.39c: code points and UTF-8 bytes, the prelude words `codePoint`, `scalar`, `utf8` and
//! `fromUtf8` on strings. `codePoint` and `scalar` give `#notScalar` for a string that is not one
//! scalar and for an int that is not a scalar value; `fromUtf8` gives `#badUtf8` for bytes that
//! are not well-formed UTF-8. The interpreter and native code give the same values.

mod bytes;
mod checks;
mod native;
mod scaling;
mod values;

use zed_kernel::family::Family;
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
        false => format!("{src}main(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- \"\";\n}}\n"),
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

/// The kernel's value of the word `p` on `x`.
fn word(p: Prim, x: Value) -> Value {
    let t = zed_kernel::Term::Prim(p, vec![zed_kernel::Term::Lit(x)]);
    zed_kernel::eval(&t).unwrap_or_else(|e| panic!("{p:?}: {e}"))
}

/// The family of `bytes` keyed by position from 1, as `utf8` gives it.
fn from_one(bytes: &[i64]) -> Value {
    Value::Family(Family::of(
        bytes
            .iter()
            .zip(1i64..)
            .map(|(&b, i)| (Value::Int(i), Value::Int(b))),
    ))
}

/// The family of `bytes` keyed from 0, as the array display `[b0, b1, …]` gives it.
fn from_zero(bytes: &[i64]) -> Value {
    Value::Family(Family::of(
        bytes
            .iter()
            .zip(0i64..)
            .map(|(&b, i)| (Value::Int(i), Value::Int(b))),
    ))
}

/// The scalar values at the ends of each range of UTF-8 lengths and around the surrogates.
const BOUNDARIES: [u32; 10] = [
    0, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF,
];
