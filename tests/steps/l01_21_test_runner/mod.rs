//! Step L1.21: the `test { }` runner. From here on a test of what a Zed program computes is
//! written in Zed: each step's `zed/` folder holds units whose tables and ✗ marks
//! `zedc test` checks. The tests here check the runner itself.

mod bench;
mod command;
mod completeness;
mod cones;
mod fences;
mod marks;
mod near_miss;
mod ports;
mod predictions;
mod rows;
mod rows_are_calls;
mod scaling;
mod tables;
mod zed;

pub(crate) use zed_tests::step_helpers::l01_21_test_runner::checks;
