//! The hand-run tools of the Zed implementation. The grammar tools check the grammar and the
//! fences of a spec checkout and report the layers of programs; `fence_layers` gives the tests
//! each fence with its layer, read from the spec in place; `progress` writes the spec's
//! PROGRESS.md; `cite` checks that every section label and step id cited is defined in
//! DESIGN.md; `plan` checks this repository's plan DAG; `conflicts` writes the plan's
//! file-conflict lists; `step_targets` writes the test target of each step folder into
//! `tests/Cargo.toml`; `imports` names every cycle of a Rust crate's file import graph.
//!
//! Each tool is a module with a `run` function over its arguments, and a thin `main` in
//! `src/bin/`. Grammar reading and matching are the compiler's (`zedc::parse`), so a rule of the
//! grammar has one implementation. CI does not read the spec repository, so CI runs none of
//! these on the spec; their tests build a small spec of their own.

pub mod audit;
pub mod cases;
pub mod catalog;
pub mod check;
pub mod cite;
pub mod conflicts;
pub mod fence_layers;
pub mod fences;
pub mod fuzz;
pub mod imports;
pub mod layer;
pub mod llp;
pub mod plan;
pub mod progress;
pub mod random;
pub mod ring;
pub mod spec;
pub mod split;
pub mod step_targets;
pub mod syntax;
pub mod text;

/// What a tool's `run` returns: whether it passed. An `Err` is the message of a failure that
/// stops the tool.
pub type Outcome = Result<bool, String>;

/// Appends a line to the tool's output.
#[macro_export]
macro_rules! say {
    ($out:expr, $($arg:tt)*) => {
        std::fmt::Write::write_fmt($out, format_args!("{}\n", format_args!($($arg)*)))
            .expect("writing to a String")
    };
}

/// The root of this repository: the checkout this tool was built from.
pub fn impl_root() -> String {
    format!("{}/../..", env!("CARGO_MANIFEST_DIR"))
}

/// The source directories of the Rust-hosted compiler under `root`: those of `zedc` and of each
/// crate `zedc-*` it is split into, by name.
pub fn compiler_dirs(root: &str) -> Result<Vec<String>, String> {
    let crates = format!("{root}/crates");
    let mut dirs = Vec::new();
    for entry in std::fs::read_dir(&crates).map_err(|e| format!("{crates}: {e}"))? {
        let entry = entry.map_err(|e| format!("{crates}: {e}"))?;
        let name = entry.file_name();
        let name = name
            .to_str()
            .ok_or_else(|| format!("{crates}: a name that is not UTF-8"))?;
        if name == "zedc" || name.starts_with("zedc-") {
            dirs.push(format!("{crates}/{name}/src"));
        }
    }
    dirs.sort_unstable();
    Ok(dirs)
}

/// Runs a tool's `run` on the command line's arguments, prints what it wrote, and gives the exit
/// status: 0 when it passed, and 1 when it failed or stopped, with a stopping failure's message
/// on standard error.
pub fn main_of(run: fn(&[String], &mut String) -> Outcome) -> std::process::ExitCode {
    use std::io::Write;
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut out = String::new();
    let outcome = run(&args, &mut out);
    std::io::stdout()
        .write_all(out.as_bytes())
        .expect("writing to standard output");
    match outcome {
        Ok(true) => std::process::ExitCode::SUCCESS,
        Ok(false) => std::process::ExitCode::FAILURE,
        Err(message) => {
            eprintln!("{message}");
            std::process::ExitCode::FAILURE
        }
    }
}

/// The argument at `i`, which the tool's usage line `usage` requires.
pub fn arg<'a>(args: &'a [String], i: usize, usage: &str) -> Result<&'a str, String> {
    args.get(i)
        .map(String::as_str)
        .ok_or_else(|| format!("usage: {usage}"))
}
