//! Step L1.19a: the command-line arguments as an input port. A `CommandLine` input is the
//! family of the words after `--`, keyed by position from 1, each a `String`; an argument that
//! is not UTF-8 is a usage error naming its position; `--record` saves the arguments and
//! `zedc replay` reads them from the record.

// binary.rs is not a module of `steps`: crates/zed-native/Cargo.toml builds it as the test
// `command_line_binary`, since only a test of that package can name the zedc executable.
mod arguments;
mod replay;
mod scaling;

use std::ffi::OsString;
use std::path::PathBuf;

/// A directory of its own for test `name`, under the test target's scratch directory; files
/// in it are overwritten by each run, never deleted.
pub(crate) fn dir(name: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("l01_19a")
        .join(name);
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The outcome of a `zedc` command line: its status, standard output and standard error.
pub(crate) struct Outcome {
    pub status: u8,
    pub stdout: String,
    pub stderr: String,
}

/// Runs `zedc <args>` with empty standard input.
pub(crate) fn zedc(args: &[OsString]) -> Outcome {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(args, &mut "".as_bytes(), &mut out, &mut err);
    Outcome {
        status,
        stdout: String::from_utf8(out).unwrap(),
        stderr: String::from_utf8(err).unwrap(),
    }
}

/// Writes program `src` as `prog.zed` in test directory `name` and gives its path.
pub(crate) fn program(name: &str, src: &str) -> OsString {
    let prog = dir(name).join("prog.zed");
    std::fs::write(&prog, src).unwrap();
    prog.into_os_string()
}

/// The words `zedc run <prog> <more…>`.
pub(crate) fn run_words(prog: &OsString, more: &[&str]) -> Vec<OsString> {
    let mut args = vec![OsString::from("run"), prog.clone()];
    args.extend(more.iter().map(OsString::from));
    args
}

/// Writes program `src` in test directory `name` and runs it with the words `more` after its
/// file.
pub(crate) fn run(name: &str, src: &str, more: &[&str]) -> Outcome {
    zedc(&run_words(&program(name, src), more))
}

/// A program that writes its arguments one per line.
pub(crate) const ECHO: &str =
    "main(args: CommandLine) -> (stdout: Lines) {\n  stdout <- args;\n}\n";
