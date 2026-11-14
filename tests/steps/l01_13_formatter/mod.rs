//! Step L1.13: the source formatter. What it writes parses to the same statements and formats
//! to itself, and keeps every comment.

mod alternatives;
mod bench;
mod corpus;
mod fences;
#[path = "../l01_08_parser/grammar_cases.rs"]
mod grammar_cases;
mod layout;
mod prelude;
mod scaling;
mod strings;

pub(crate) use zed_tests::step_helpers::l01_13_formatter::{build, fmt};
