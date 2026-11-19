//! Step L1.12: declarations, namely functions in equation and block form with their `test`
//! tables, `main`'s port header, the whole-value push `p <- e`, and `if`/`else`.

mod bench;
#[cfg(feature = "spec")]
mod fences;
mod functions;
mod given;
mod ifs;
mod pushes;
mod ranges;
mod scaling;

use zed_tests::step_helpers::l02_01_parser_structs::check;
