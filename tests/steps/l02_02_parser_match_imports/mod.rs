//! Step L2.2: the parser of `match` with guards and type patterns, `import` statements with an
//! `@hash` pin, and the `@` annotation syntax. Each form builds and formats; name resolution
//! refuses it, naming the step that gives it meaning, and refuses each annotation, naming its
//! layer.

mod annotations;
mod bench;
mod formatting;
mod imports;
mod later;
mod matches;
mod scaling;

use zed_tests::step_helpers::l02_01_parser_structs::{check, fmt};
