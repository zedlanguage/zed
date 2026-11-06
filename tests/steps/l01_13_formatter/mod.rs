//! Step L1.13: the source formatter. What it writes parses to the same statements and formats
//! to itself, and keeps every comment.

mod corpus;
mod fences;
mod layout;
mod prelude;
mod scaling;

pub(crate) use zed_tests::step_helpers::l01_13_formatter::{build, fmt};
