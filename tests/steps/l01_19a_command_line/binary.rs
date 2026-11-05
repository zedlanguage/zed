//! The zedc executable, run as a user runs it, given command-line arguments (DESIGN.md step
//! L1.19a): the words reach `zedc run` as the system gives them, so an argument that is not
//! UTF-8 is a usage error naming its position, not a crash. `crates/zed-native/Cargo.toml` names
//! this test, since only a test of that package can name the executable.

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

const ECHO: &str = "main(args: CommandLine) -> (stdout: Lines) {\n  stdout <- args;\n}\n";

/// `zedc run <echo program> -- <args>`, the program written for test `name`.
fn echo(name: &str, args: &[OsString]) -> Output {
    let file = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("command_line_{name}_{}.zed", std::process::id()));
    std::fs::write(&file, ECHO).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg("run")
        .arg(&file)
        .arg("--")
        .args(args)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    std::fs::remove_file(&file).unwrap();
    out
}

#[test]
fn zedc_gives_main_its_arguments() {
    let out = echo("arguments", &["a".into(), "b c".into()]);
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "a\nb c\n");
}

#[test]
fn zedc_names_the_argument_that_is_not_utf8() {
    let out = echo("not_utf8", &["ok".into(), OsString::from_vec(vec![255])]);
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(
        String::from_utf8_lossy(&out.stderr),
        "command-line argument 2 is not UTF-8\n"
    );
    assert!(out.stdout.is_empty());
}
