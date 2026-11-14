//! Step L1.18: the interpreter's scalar tier. Programs run through the L1 prelude words
//! (`String`, the checked casts, `abs`, `sum` and the string words), failures from several
//! operands merge into `#errs`, and floats print in the shortest form that reads back.

mod bench;
mod cast_negzero;
mod casts;
mod completeness;
mod f32;
mod failures;
mod floats;
mod literals;
mod prim_names;
mod rat_text;
mod scaling;
mod sqrt_fma;
mod tuple_min_max;
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
