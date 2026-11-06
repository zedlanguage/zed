//! Step L1.19a: the command-line arguments as an input port. A `CommandLine` input is the
//! family of the words after `--`, keyed by position from 1, each a `String`; an argument that
//! is not UTF-8 is a usage error naming its position; `--record` saves the arguments and
//! `zedc replay` reads them from the record.

// binary.rs is not a module of this target: crates/zed-native/Cargo.toml builds it as the test
// `command_line_binary`, since only a test of that package can name the zedc executable.
mod arguments;
mod replay;
mod scaling;

pub(crate) use zed_tests::step_helpers::l01_19a_command_line::{
    dir, program, run, run_words, zedc,
};

/// A program that writes its arguments one per line.
pub(crate) const ECHO: &str =
    "main(args: CommandLine) -> (stdout: Lines) {\n  stdout <- args;\n}\n";
