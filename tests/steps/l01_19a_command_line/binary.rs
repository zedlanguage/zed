//! The zedc executable, run as a user runs it, given command-line arguments (DESIGN.md step
//! L1.19a): the words reach `zedc run` as the system gives them, so an argument that is not
//! UTF-8 is a usage error naming its position, not a crash. `crates/zed-native/Cargo.toml` names
//! this test, since only a test of that package can name the executable.

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

const ECHO: &str = "main(m: MainArgs) {\n  m.stdout <- m.args;\n}\n";

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
        "command-line argument 2 (counted from the first word after `--`) is not UTF-8, and a \
         `CommandLine` port gives the program each argument as a string, which must be UTF-8 \
         text. Pass the argument as UTF-8 text, or pass the path of a file that holds it.\n"
    );
    assert!(out.stdout.is_empty());
}

/// `zedc <words>`, with standard input empty.
fn zedc(words: &[OsString]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_zedc"))
        .args(words)
        .stdin(Stdio::null())
        .output()
        .unwrap()
}

/// The list of commands zedc prints after the reason for a usage error.
const COMMANDS: &str = "\n\nThe commands of zedc are:\n  zedc fmt <file>\n";

#[test]
fn zedc_names_a_word_that_is_no_command() {
    let out = zedc(&["frmat".into(), "a.zed".into()]);
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    let why = "`frmat` is not a command of zedc. The commands are `fmt`, `run`, `replay`, `build` \
               and `test`, and `--report` may come before any of them.";
    assert!(stderr.starts_with(&format!("{why}{COMMANDS}")), "{stderr}");
    assert!(out.stdout.is_empty());
}

#[test]
fn zedc_fmt_counts_the_words_after_it() {
    let out = zedc(&["fmt".into(), "a.zed".into(), "b.zed".into()]);
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    let why = "`zedc fmt` takes one word after it, the file to print in the standard layout, and \
               was given 2 words. Write `zedc fmt <file>`, once for each file.";
    assert!(stderr.starts_with(&format!("{why}{COMMANDS}")), "{stderr}");
}

#[test]
fn zedc_fmt_says_why_it_could_not_read_the_file() {
    let file = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("command_line_no_such_file.zed");
    let out = zedc(&["fmt".into(), file.clone().into()]);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        String::from_utf8_lossy(&out.stderr),
        format!(
            "{}: zedc could not read the file: No such file or directory. Check \
             the path and that you may read the file.\n",
            file.display()
        )
    );
}

#[test]
fn zedc_names_a_file_word_that_is_not_utf8() {
    let out = zedc(&["fmt".into(), OsString::from_vec(vec![b'a', 255])]);
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    let why = "zedc reads the words after `fmt`, `build` and `test` as UTF-8 text, and a word of \
               this command line is not UTF-8. Name each file by a path written in UTF-8, or \
               rename the file.";
    assert!(stderr.starts_with(&format!("{why}{COMMANDS}")), "{stderr}");
}
