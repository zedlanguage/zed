//! Helpers that the tests of more than one step folder use. Each step folder is a test target
//! of its own (tests/Cargo.toml), so a folder cannot reach into another folder's modules; what
//! two folders share lives here, in a module named after the folder it came from, and that
//! folder re-exports it. A path `crate::<folder>::x` written in another folder is
//! `zed_tests::step_helpers::<folder>::x`.

pub mod l01_10_lambdas_types_else_tuples;
pub mod l01_13_formatter;
pub mod l01_14_name_resolution;
pub mod l01_16_elaboration;
#[cfg(unix)]
pub mod l01_17_value_representation;
pub mod l01_19_whole_file_ports;
pub mod l01_19a_command_line;
pub mod l01_21_test_runner;
pub mod l01_25_preimage_catalog;
pub mod l01_26_type_resolution;
pub mod l01_31_zir;
pub mod l01_33_lowering;
pub mod l01_34_memory;
pub mod l01_36_cranelift;
#[cfg(target_os = "linux")]
pub mod l01_36a_executables;
pub mod l01_38_presburger;
pub mod l01_39_reduced_product;
pub mod m0_03_grammar_tools;

pub use crate::scratch::{process_tmpdir, scratch, target_tmpdir};
