//! Step L1.39c: code points and UTF-8 bytes, the prelude words `codePoint`, `scalar`, `utf8` and
//! `fromUtf8` on strings. `codePoint` and `scalar` give `#notScalar` for a string that is not one
//! scalar and for an int that is not a scalar value; `fromUtf8` gives `#badUtf8` for bytes that
//! are not well-formed UTF-8. The interpreter and native code give the same values.

mod bench;
mod bytes;
mod checks;
mod completeness;
mod native;
mod values;

use zed_kernel::value::Family;
use zed_kernel::{Prim, Value};
use zedc::run::load;

/// Functions that pass their argument on, so that a word applied to their result is judged on
/// a value known only when the program runs: the word on a literal that never converts is
/// rejected (row "Operation that always fails").
const PASS: &str = "text(positional v: String) = v;\nwhole(positional v: int) = v;\n";

/// The value of `x = <expr>;` after [`PASS`], printed.
fn x(expr: &str) -> String {
    zed_tests::step_helpers::l01_16_elaboration::value(&format!("{PASS}x = {expr};\n"), "x")
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

/// The kernel's value of the word `p` on `x`.
fn word(p: Prim, x: Value) -> Value {
    let t = zed_kernel::Term::Prim(p, vec![zed_kernel::Term::Lit(x)]);
    zed_kernel::eval(&t).unwrap_or_else(|e| panic!("{p:?}: {e}"))
}

/// The family of `bytes` keyed from 1: keys other than an array's, which `fromUtf8` reads in key
/// order all the same.
fn from_one(bytes: &[i64]) -> Value {
    Value::Family(Family::of(
        bytes
            .iter()
            .zip(1i64..)
            .map(|(&b, i)| (Value::Int(i), Value::Int(b))),
    ))
}

/// The family of `bytes` keyed from 0, as `utf8` and the array display `[b0, b1, …]` give it.
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
