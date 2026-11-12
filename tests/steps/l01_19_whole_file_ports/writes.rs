//! Writes: one whole-value push per port per wave, committed when the wave ends, each with
//! an acknowledgment; a failed write aborts the wave.

use zed_kernel::{Family, Value};
use zedc::run::{commit, join_lines};

use super::{dir, run};

#[test]
fn a_port_bound_on_the_command_line_is_a_usage_error() {
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"${m.stdin[0] else \"\"}\\n${m.stdin[1] else \"\"}\";\n}\n";
    let out = run("report", src, "total: 42\nitems: 3\n", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "total: 42\nitems: 3\n")
    );
    // A program's ports are its argument's fields, so a `port=path` word names nothing.
    let out = run("report", src, "", &["report=out.txt"]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (
            2,
            "`report=out.txt` names the file `out.txt` for a port `report`, and a program's \
             ports are not named on the command line: `main(m: MainArgs)` reads standard input \
             from `m.stdin` and writes `m.stdout` and `m.stderr` to standard output and standard \
             error, and a program opens a file by its path with `files()`. To read a file as \
             standard input, write `< out.txt`; to write standard output to a file, write `> \
             out.txt`; to give the path to the program, put it after `--`, where `m.args` reads \
             it.\n\nThe forms are:\n  \
             zedc run <file> [--record <out>] [--suppress <address> …] [--addresses] \
             [--option <name> …] [-- arg …]\n  \
             zedc replay <file> <record> [--suppress <address> …] [--addresses] \
             [--option <name> …] [-- arg …]\n"
        )
    );
}

#[test]
fn an_error_stops_the_wave_before_anything_is_written() {
    // `m.stderr` is pushed first in the text, then a string too long for its length stops the
    // wave, and neither stream is written.
    let src = format!(
        "{}main(m: MainArgs) {{\n  m.stderr <- \"half done\";\n  m.stdout <- {};\n}}\n",
        zed_tests::TWICE,
        zed_tests::too_long()
    );
    let out = run("abort", &src, "", &[]);
    assert_eq!(out.status, 1, "{}", out.stderr);
    assert!(out.stderr.contains("cannot join"), "{}", out.stderr);
    assert!(!out.stderr.contains("half done"), "{}", out.stderr);
    assert_eq!(out.stdout, "");
}

#[test]
fn a_port_pushed_twice_in_one_wave_is_an_error() {
    let src = "main(m: MainArgs) {\n  m.stdout <- \"one\";\n  m.stdout <- \"two\";\n}\n";
    let out = run("twice", src, "", &[]);
    assert_eq!(out.status, 1);
    assert_eq!(
        out.stderr,
        "`m.stdout` was pushed to 2 times in this run, and it takes one push per run, which holds \
         everything it writes. Gather the lines into one family of strings and push it once, as \
         `m.stdout <- lines;`, where `lines` holds one entry per line; a push in a branch that \
         does not run does not count.\n"
    );
    assert_eq!(out.stdout, "", "nothing is written");
    // Two push sites on different branches are fine: one of them runs.
    let src = "main(m: MainArgs) {\n  \
               done = if m.stdin[0] == \"yes\" {\n    m.stdout <- \"accepted\";\n    1\n  } \
               else {\n    m.stdout <- \"declined\";\n    0\n  };\n}\n";
    assert_eq!(run("branches", src, "no\n", &[]).stdout, "declined\n");
}

/// `2 ^ 2 ^ 100` is a value, kept as a power of 2, but adding 1 must build its `2^100`
/// bits: the run stops with an error naming that size, before anything is written, and the
/// process does not abort.
#[test]
fn a_number_too_large_to_build_stops_the_run() {
    let src = "main(m: MainArgs) {\n  m.stdout <- \"start\";\n  \
               m.stdout <- String(2^2^100 + 1);\n}\n";
    let out = run("too_large", src, "", &[]);
    assert_eq!(out.status, 1, "{}", out.stderr);
    assert!(
        out.stderr.contains(
            "`+` must build a number in full, and the system refused the \
             1267650600228229401496703205379 bytes of memory asked for it"
        ),
        "{}",
        out.stderr
    );
    assert_eq!(out.stdout, "");
}

/// Printing `2 ^ 2 ^ 100` must build its `2^100` bits: the run stops with an error naming
/// that size, at once, and the process does not abort.
#[test]
fn printing_a_number_too_large_to_build_stops_the_run() {
    let src = "main(m: MainArgs) {\n  m.stdout <- String(2^2^100);\n}\n";
    let out = run("print_too_large", src, "", &[]);
    assert_eq!(out.status, 1, "{}", out.stderr);
    assert!(
        out.stderr.contains(
            "`String` must build a number in full, and the system refused the \
             4322886617184547919947741790226 bytes of memory asked for it"
        ),
        "{}",
        out.stderr
    );
    assert_eq!(out.stdout, "");
}

#[test]
fn only_strings_are_written_as_lines() {
    let src = "main(m: MainArgs) {\n  m.stdout <- 42;\n}\n";
    let out = run("number", src, "", &[]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr
            .contains("2:15: a `Lines` port takes a `String` or a family of strings, not 42"),
        "{}",
        out.stderr
    );
    // The writer checks again what it is given.
    let e = join_lines("stdout", &Value::Int(42)).unwrap_err();
    assert!(
        e.starts_with("port `stdout` writes lines of text, and the program pushed 42 to it")
            && e.contains("`Utf8String(…)`"),
        "{e}"
    );
}

#[test]
fn the_first_failed_write_aborts_the_rest() {
    let writes = vec![
        ("audit".to_string(), b"a\n".to_vec()),
        ("stdout".to_string(), b"b\n".to_vec()),
        ("stderr".to_string(), b"c\n".to_vec()),
    ];
    let mut done = Vec::new();
    let acks = commit(&writes, |port, _| {
        done.push(port.to_string());
        if port == "stdout" {
            Err(("stdout".into(), "disk full".into()))
        } else {
            Ok(())
        }
    });
    assert_eq!(done, ["audit", "stdout"], "stderr is never written");
    let acks: Vec<(String, String)> = acks.into_iter().map(|(p, v)| (p, v.to_string())).collect();
    assert_eq!(
        acks,
        [
            ("audit".to_string(), Value::atom("ok").to_string()),
            (
                "stdout".to_string(),
                "#ioError(op: \"write\", path: \"stdout\", why: \"disk full\")".to_string()
            ),
        ]
    );
    // Through the command, a failed write to standard output exits 1 and names the port.
    /// Standard output that refuses every write.
    struct Full;
    impl std::io::Write for Full {
        fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("the disk is full"))
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let prog = dir("unwritable").join("prog.zed");
    std::fs::write(&prog, "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n").unwrap();
    let args = ["run".to_string(), prog.display().to_string()];
    let mut err = Vec::new();
    let status = zedc::run::command(&args, &mut std::io::empty(), &mut Full, &mut err);
    assert_eq!(
        (status, String::from_utf8(err).unwrap().as_str()),
        (
            1,
            "the program wrote to `m.stdout`, and zedc could not write it to the standard output \
             of this process: the disk is full. Send the standard output to a place that accepts \
             it, such as a file, with `> out.txt` for standard output or `2> err.txt` for \
             standard error.\n"
        )
    );
}

/// The message for the word `port=path` on the command line, which binds no port: the forms
/// that read and write files instead, and the usage that follows it.
fn names_no_port(port: &str, path: &str) -> String {
    format!(
        "`{port}={path}` names the file `{path}` for a port `{port}`, and a program's ports are \
         not named on the command line: `main(m: MainArgs)` reads standard input from `m.stdin` \
         and writes `m.stdout` and `m.stderr` to standard output and standard error, and a \
         program opens a file by its path with `files()`. To read a file as standard input, \
         write `< {path}`; to write standard output to a file, write `> {path}`; to give the \
         path to the program, put it after `--`, where `m.args` reads it.\n\n{USAGE}"
    )
}

/// The forms of `zedc run` and `zedc replay`, which a usage error ends with.
const USAGE: &str = "The forms are:\n  \
                     zedc run <file> [--record <out>] [--suppress <address> …] [--addresses] \
                     [--option <name> …] [-- arg …]\n  \
                     zedc replay <file> <record> [--suppress <address> …] [--addresses] \
                     [--option <name> …] [-- arg …]\n";

#[test]
fn usage_errors_exit_2() {
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin[0] else \"\";\n}\n";
    let out = run("usage", src, "", &["nosuch=x"]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (2, &*names_no_port("nosuch", "x"))
    );
    // The names of the old header's ports bind nothing either.
    for port in ["stdin", "stdout", "fs", "args"] {
        let out = run("usage", src, "", &[&format!("{port}=x")]);
        assert_eq!(
            (out.status, out.stderr.as_str()),
            (2, &*names_no_port(port, "x"))
        );
    }
    let out = run("usage", src, "", &["--bogus"]);
    assert_eq!(out.status, 2);
    assert_eq!(
        out.stderr,
        format!(
            "`--bogus` is not understood here: before `--` comes only `--record <out>`, which \
             writes a record of the run; after `--` come the program's own arguments. If \
             `--bogus` is meant for the program, put it after `--`.\n\n{USAGE}"
        )
    );
    let out = run("usage", "main( = ;\n", "", &[]);
    assert_eq!(
        out.status, 1,
        "a program that does not parse fails, with its position"
    );
    assert!(out.stderr.contains("prog.zed:1:"), "{}", out.stderr);
}

#[test]
fn an_empty_level_pushed_writes_no_line() {
    // A family whose entry is an empty level, flat or nested, writes the lines of its strings
    // and nothing for the empty level, the bytes written before empty levels were kept.
    let empty = || Value::Family(Family::new());
    let flat = Family::from_leaves([
        (vec![Value::Int(1)], Value::str("a")),
        (vec![Value::Int(2)], empty()),
        (vec![Value::Int(3)], Value::str("b")),
    ])
    .unwrap();
    let nested = Family::from_leaves([
        (vec![Value::Int(1), Value::Int(1)], Value::str("a")),
        (vec![Value::Int(2)], empty()),
        (vec![Value::Int(3), Value::Int(1)], Value::str("b")),
    ])
    .unwrap();
    for f in [flat, nested] {
        let v = Value::Family(f);
        assert_eq!(join_lines("stdout", &v), Ok(b"a\nb\n".to_vec()), "{v}");
        assert_eq!(
            zed_rt::ports::write("stdout", &v),
            Ok(b"a\nb\n".to_vec()),
            "{v}"
        );
    }
    let only = Value::Family(Family::from_leaves([(vec![Value::Int(1)], empty())]).unwrap());
    assert_eq!(join_lines("stdout", &only), Ok(Vec::new()));
    assert_eq!(zed_rt::ports::write("stdout", &only), Ok(Vec::new()));
}

/// A file zedc cannot read or write is named with the system's reason and a repair: the
/// program's file, the file `--record` names, and standard input.
#[test]
fn a_file_zedc_cannot_use_is_named_with_the_reason() {
    let missing = "/nonexistent-dir-l01-19/in.txt";
    let src = "main(m: MainArgs) {\n  m.stdout <- m.stdin[0] else \"\";\n}\n";
    let out = super::zedc(&["run", missing], "");
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (
            2,
            "/nonexistent-dir-l01-19/in.txt: zedc could not read this file: No such file or \
             directory. Check the path and that you may read the file.\n"
        )
    );
    let record = "/nonexistent-dir-l01-19/run.record";
    let out = run("unreadable", src, "x\n", &["--record", record]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (
            1,
            "/nonexistent-dir-l01-19/run.record: zedc could not write the record of this run to \
             this file: No such file or directory. Name a file in a directory you may write to.\n"
        )
    );
    assert_eq!(out.stdout, "", "nothing is written when the record is not");
    /// Standard input that refuses every read.
    struct Refusing;
    impl std::io::Read for Refusing {
        fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("the device is gone"))
        }
    }
    let prog = dir("unreadable").join("prog.zed");
    let args = ["run".to_string(), prog.display().to_string()];
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&args, &mut Refusing, &mut out, &mut err);
    assert_eq!(
        (status, String::from_utf8(err).unwrap().as_str()),
        (
            2,
            "zedc could not read standard input, which `m.stdin` reads: the device is gone. Give \
             zedc a standard input it may read, such as a file, with `< in.txt`.\n"
        )
    );
}

/// A program file in a package whose path under the package root is not UTF-8, reached through
/// a link with a UTF-8 name, cannot be named as a unit, and the message names the root.
#[test]
fn a_unit_whose_path_is_not_utf8_is_named_with_its_root() {
    use std::os::unix::ffi::OsStrExt;
    let root = dir("not_utf8_root");
    std::fs::write(root.join("zed.manifest"), "").unwrap();
    let real = root.join(std::ffi::OsStr::from_bytes(b"caf\xe9.zed"));
    std::fs::write(&real, "main(m: MainArgs) {\n  m.stdout <- \"hi\";\n}\n").unwrap();
    let link = dir("not_utf8_link").join("prog.zed");
    let _ = std::fs::remove_file(&link);
    std::os::unix::fs::symlink(&real, &link).unwrap();
    let args = ["run".to_string(), link.display().to_string()];
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&args, &mut std::io::empty(), &mut out, &mut err);
    let root = std::fs::canonicalize(&root).unwrap();
    assert_eq!(
        (status, String::from_utf8(err).unwrap()),
        (
            2,
            format!(
                "the path of `{}` under its package root `{}` is not UTF-8 text, and a unit is \
                 named by that path. Rename the file and the directories between it and the \
                 package root with UTF-8 names.\n",
                link.display(),
                root.display()
            )
        )
    );
}
