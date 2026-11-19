//! Step L1.11: statements in a block, namely bindings with their tuple-destructuring targets
//! and `return` with a value or a comma list, and the `;` rule: every statement ends in `;`
//! but the trailing expression, which is the block's `return`.

mod bench;
mod blocks;
mod empty_family;
#[cfg(feature = "spec")]
mod fences;
mod returns;
mod scaling;

use zed_tests::step_helpers::l02_01_parser_structs::{check_exprs as check, expr_sx as sx};
