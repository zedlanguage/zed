//! `zedc` command-line helpers of step L1.19 (tests/steps/l01_19_whole_file_ports).

use std::path::PathBuf;

/// A directory of its own for test `name`, under the test target's scratch directory; files
/// in it are overwritten by each run, never deleted.
pub fn dir(name: &str) -> PathBuf {
    let d = super::target_tmpdir().join("l01_19").join(name);
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

/// Runs `zedc <args>` with `stdin` as standard input.
pub fn zedc(args: &[&str], stdin: &str) -> Outcome {
    let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&args, &mut stdin.as_bytes(), &mut out, &mut err);
    Outcome {
        status,
        stdout: String::from_utf8(out).unwrap(),
        stderr: String::from_utf8(err).unwrap(),
    }
}

/// Writes program `src` as `prog.zed` in test directory `name` and runs it with `stdin`
/// and the extra arguments `more`.
pub fn run(name: &str, src: &str, stdin: &str, more: &[&str]) -> Outcome {
    let prog = dir(name).join("prog.zed");
    std::fs::write(&prog, src).unwrap();
    let prog = prog.to_str().unwrap().to_string();
    let mut args = vec!["run", prog.as_str()];
    args.extend_from_slice(more);
    zedc(&args, stdin)
}
