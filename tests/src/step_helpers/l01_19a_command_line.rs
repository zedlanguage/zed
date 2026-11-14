//! `zedc` command-line helpers of step L1.19a (tests/steps/l01_19a_command_line).

use std::ffi::OsString;
use std::path::PathBuf;

/// A directory of its own for test `name`, under this process's scratch directory
/// ([`super::scratch`]), which no other process and no other test uses.
pub fn dir(name: &str) -> PathBuf {
    let d = super::scratch(format!("l01_19a/{name}"));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// The outcome of a `zedc` command line: its status, standard output and standard error.
pub struct Outcome {
    /// The exit status.
    pub status: u8,
    /// What it wrote to standard output.
    pub stdout: String,
    /// What it wrote to standard error.
    pub stderr: String,
}

/// Runs `zedc <args>` with empty standard input.
pub fn zedc(args: &[OsString]) -> Outcome {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(args, &mut "".as_bytes(), &mut out, &mut err);
    Outcome {
        status,
        stdout: String::from_utf8(out).unwrap(),
        stderr: String::from_utf8(err).unwrap(),
    }
}

/// Writes program `src` as `prog.zed` in test directory `name` and gives its path.
pub fn program(name: &str, src: &str) -> OsString {
    let prog = dir(name).join("prog.zed");
    std::fs::write(&prog, src).unwrap();
    prog.into_os_string()
}

/// The words `zedc run <prog> <more…>`.
pub fn run_words(prog: &OsString, more: &[&str]) -> Vec<OsString> {
    let mut args = vec![OsString::from("run"), prog.clone()];
    args.extend(more.iter().map(OsString::from));
    args
}

/// Writes program `src` in test directory `name` and runs it with the words `more` after its
/// file.
pub fn run(name: &str, src: &str, more: &[&str]) -> Outcome {
    zedc(&run_words(&program(name, src), more))
}
