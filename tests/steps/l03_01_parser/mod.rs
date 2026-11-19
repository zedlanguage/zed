//! Step L3.1: the parser of the forms of layer L3. Each form builds and formats; name
//! resolution refuses it, naming the step that compiles it.

mod arrays;
mod bench;
mod corners;
mod formatting;
mod forms;
mod later;
mod scaling;

use zed_tests::step_helpers::l02_01_parser_structs::{check, fmt, refused};
