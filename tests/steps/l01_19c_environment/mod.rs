//! Step L1.19c: the environment variables as an input port. An input of type
//! `String ->? String` is a lookup by name: a variable's value, or `#notFound` for a name that
//! is not set; a value that is not UTF-8 is a usage error naming the variable; `--record`
//! saves each name the wave read and what it gave, and `zedc replay` reads them from the
//! record, never from its own environment.

// binary.rs is not a module of this target: crates/zed-native/Cargo.toml builds it as the test
// `environment_binary`, since only a test of that package can name the zedc executable.
mod bench;
mod combinations;
mod reads;
mod replay;

use std::ffi::OsString;

pub(crate) use zed_tests::step_helpers::l01_19a_command_line::{Outcome, program, run_words};

/// A program that writes the variables `ZED_A` and `ZED_B`, `-` for one that is not set.
pub(crate) const TWO: &str = "main(m: MainArgs) {\n  \
    m.stdout <- \"${m.env[\"ZED_A\"] else \"-\"}|${m.env[\"ZED_B\"] else \"-\"}\";\n}\n";

/// The variables `vars` as a process holds them.
pub(crate) fn vars(vars: &[(&str, &[u8])]) -> Vec<(OsString, OsString)> {
    use std::os::unix::ffi::OsStringExt;
    vars.iter()
        .map(|(k, v)| (OsString::from(k), OsString::from_vec(v.to_vec())))
        .collect()
}

/// Runs `zedc <args>` with the variables `env` and empty standard input.
pub(crate) fn zedc(args: &[OsString], env: Vec<(OsString, OsString)>) -> Outcome {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command_in(args, env, &mut "".as_bytes(), &mut out, &mut err);
    Outcome {
        status,
        stdout: String::from_utf8(out).unwrap(),
        stderr: String::from_utf8(err).unwrap(),
    }
}

/// Writes program `src` in test directory `name` and runs it with the variables `env`.
pub(crate) fn run(name: &str, src: &str, env: &[(&str, &[u8])]) -> Outcome {
    zedc(&run_words(&dir_program(name, src), &[]), vars(env))
}

/// Writes program `src` in a test directory `l01_19c_<name>` and gives its path.
pub(crate) fn dir_program(name: &str, src: &str) -> OsString {
    program(&format!("l01_19c_{name}"), src)
}
