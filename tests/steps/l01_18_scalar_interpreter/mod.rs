//! Step L1.18: the interpreter's scalar tier. Programs run through the L1 prelude words
//! (`String`, the checked casts, `abs`, `sum` and the string words), failures from several
//! operands merge into `#errs`, and floats print in the shortest form that reads back.

mod casts;
mod failures;
mod floats;
mod words;

use crate::l01_16_elaboration::value;

/// The value of `x = <expr>;`, printed.
fn x(expr: &str) -> String {
    value(&format!("x = {expr};\n"), "x")
}
