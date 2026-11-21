//! Step L1.18: the interpreter's scalar tier. Programs run through the L1 prelude words
//! (`String`, the checked casts, `abs`, `sum` and the string words), failures from several
//! operands merge into `#errs`, and floats print in the shortest form that reads back.
// Proving the bench closures `Sync` (zed_tests::scaling::check) walks the kernel's nested types
// deeper than rustc's default limit of 128; since nightly-2026-11-18 that is the lint
// `recursion_depth_exceeding_limit` (rust-lang/rust#159228), an error under clippy -D warnings.
#![recursion_limit = "256"]

mod bench;
mod cast_negzero;
mod casts;
mod completeness;
mod f32;
mod failures;
mod float_mod;
mod floats;
mod literals;
mod prim_names;
mod rat_text;
mod rounding;
mod scaling;
mod sqrt_fma;
mod tuple_min_max;
mod unfixed_decimal;
mod word_args;
mod words;

use zed_tests::step_helpers::l01_16_elaboration::value;

/// Functions that pass their argument on, each declared with a carrier. A call is not judged,
/// so `int(text("x"))` keeps the `#invalid` it gives when the program runs, where `int("x")`,
/// whose operand the checker reads, is rejected as an operation that always fails (DESIGN.md
/// sec:failure).
const PASS: &str = "text(positional v: String) = v;\nreal(positional v: f64) = v;\n\
                    whole(positional v: int) = v;\n";

/// The value of `x = <expr>;` after [`PASS`], printed.
fn x(expr: &str) -> String {
    value(&format!("{PASS}x = {expr};\n"), "x")
}
