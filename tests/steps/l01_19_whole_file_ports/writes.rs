//! Writes: one whole-value push per port per wave, committed when the wave ends, each with
//! an acknowledgment; a failed write aborts the wave.

use zed_kernel::{Family, Value};
use zedc::run::{commit, join_lines};

use super::{dir, run};

#[test]
fn a_report_goes_to_a_file_bound_on_the_command_line() {
    let d = dir("report");
    let path = d.join("report.txt");
    std::fs::write(&path, "stale\n").unwrap();
    let src = "main(stdin: Lines) -> (report: Lines, stdout: Lines) {\n  \
               report <- \"${stdin[1] else \"\"}\\n${stdin[2] else \"\"}\";\n  \
               stdout <- \"wrote the report\";\n}\n";
    let bind = format!("report={}", path.display());
    let out = run("report", src, "total: 42\nitems: 3\n", &[&bind]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "wrote the report\n"));
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "total: 42\nitems: 3\n"
    );
    // A port other than `stdout` and `stderr` must be bound before the wave runs.
    let out = run("report", src, "", &[]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (
            2,
            "the output port `report` of `main` needs a file to write to, and none is named: \
             only `stdout` and `stderr` write to the process's own streams. Add \
             `report=<path>` to the command line.\n"
        )
    );
}

#[test]
fn an_error_stops_the_wave_before_anything_is_written() {
    let d = dir("abort");
    let path = d.join("out.txt");
    std::fs::write(&path, "previous\n").unwrap();
    // `out` is pushed first in the text, then a string too long for its length stops the wave.
    let src = format!(
        "{}main() -> (out: Lines, stdout: Lines) {{\n  out <- \"half done\";\n  stdout <- {};\n}}\n",
        zed_tests::TWICE,
        zed_tests::too_long()
    );
    let bind = format!("out={}", path.display());
    let out = run("abort", &src, "", &[&bind]);
    assert_eq!(out.status, 1, "{}", out.stderr);
    assert!(out.stderr.contains("cannot join"), "{}", out.stderr);
    assert_eq!(out.stdout, "");
    assert_eq!(std::fs::read_to_string(&path).unwrap(), "previous\n");
}

#[test]
fn a_port_pushed_twice_in_one_wave_is_an_error() {
    let src = "say(positional s) -> (stdout: Lines) {\n  stdout <- s;\n}\n\
               main() -> (stdout: Lines) {\n  a = say(\"one\");\n  b = say(\"two\");\n}\n";
    let out = run("twice", src, "", &[]);
    assert_eq!(out.status, 1);
    assert_eq!(
        out.stderr,
        "the output port `stdout` was pushed to 2 times in this run, and a port takes one push \
         per run, which holds everything it writes. Gather the lines into one family of strings \
         and push it once, as `stdout <- lines;`, where `lines` holds one entry per line; a push \
         in a branch that does not run does not count.\n"
    );
    assert_eq!(out.stdout, "", "nothing is written");
    // Two push sites on different branches are fine: one of them runs.
    let src = "accept() -> (stdout: Lines) {\n  stdout <- \"accepted\";\n}\n\
               decline() -> (stdout: Lines) {\n  stdout <- \"declined\";\n}\n\
               main(stdin: Lines) -> (stdout: Lines) {\n  \
               done = if stdin[1] == \"yes\" { accept() } else { decline() };\n}\n";
    assert_eq!(run("branches", src, "no\n", &[]).stdout, "declined\n");
}

/// `2 ^ 2 ^ 100` is a value, kept as a power of 2, but adding 1 must build its `2^100`
/// bits: the run stops with an error naming that size, before anything is written, and the
/// process does not abort.
#[test]
fn a_number_too_large_to_build_stops_the_run() {
    let src = "main() -> (stdout: Lines) {\n  stdout <- \"start\";\n  \
               stdout <- String(2^2^100 + 1);\n}\n";
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
    let src = "main() -> (stdout: Lines) {\n  stdout <- String(2^2^100);\n}\n";
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
    let src = "main() -> (stdout: Lines) {\n  stdout <- 42;\n}\n";
    let out = run("number", src, "", &[]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr
            .contains("2:13: a `Lines` port takes a `String` or a family of strings, not 42"),
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
    // Through the command, a failed write exits 1 and names the port.
    let src = "main() -> (log2: Lines) {\n  log2 <- \"x\";\n}\n";
    let out = run(
        "unwritable",
        src,
        "",
        &["log2=/nonexistent-dir-l01-19/x.txt"],
    );
    assert_eq!(out.status, 1);
    assert_eq!(
        out.stderr,
        "the program wrote to the output port `log2`, and zedc could not write it to the file \
         /nonexistent-dir-l01-19/x.txt: No such file or directory. Name a file in a directory you \
         may write to, as `log2=<path>`.\n"
    );
}

/// The message for `port=path` naming a file for the input port `port`, which reads none.
fn reads_no_file(port: &str, path: &str) -> String {
    format!(
        "`{port}={path}` names a file for the input port `{port}`, and `{port}` reads no file \
         named on the command line: a `Files` port reads files by the paths the program gives \
         it, a `CommandLine` port reads the words after `--`, and an environment port reads the \
         environment. Remove `{port}={path}`.\n"
    )
}

#[test]
fn usage_errors_exit_2() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin[1] else \"\";\n}\n";
    let out = run("usage", src, "", &["nosuch=x"]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (
            2,
            "`nosuch=x` names a file for the port `nosuch`, and `main` has no port `nosuch`; \
             its ports are `stdin` and `stdout`. Write the name of one of them before `=`, or \
             remove `nosuch=x`.\n"
        )
    );
    let files = "main(fs: Files) -> (stdout: Lines) {\n  stdout <- fs[\"a\"] else \"\";\n}\n";
    let out = run("usage", files, "", &["fs=x"]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (2, &*reads_no_file("fs", "x"))
    );
    let args = "main(args: CommandLine) -> (stdout: Lines) {\n  stdout <- args[1] else \"\";\n}\n";
    let out = run("usage", args, "", &["args=x"]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (2, &*reads_no_file("args", "x"))
    );
    let out = run("usage", src, "", &["--bogus"]);
    assert_eq!(out.status, 2);
    assert_eq!(
        out.stderr,
        "`--bogus` is not understood here: before `--` come only `port=path`, which names the \
         file a port reads or writes, and `--record <out>`, which writes a record of the run; \
         after `--` come the program's own arguments. If `--bogus` is meant for the program, put \
         it after `--`.\n\nThe forms are:\n  \
         zedc run <file> [port=path …] [--record <out>] [--suppress <address> …] [--addresses] \
         [-- arg …]\n  \
         zedc replay <file> <record> [port=path …] [--suppress <address> …] [--addresses] \
         [-- arg …]\n"
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
/// program's file, a file bound to an input port, the file `--record` names, and standard
/// input.
#[test]
fn a_file_zedc_cannot_use_is_named_with_the_reason() {
    let missing = "/nonexistent-dir-l01-19/in.txt";
    let src = "main(stdin: Lines, extra: Lines) -> (stdout: Lines) {\n  \
               stdout <- extra[1] else \"\";\n}\n";
    let out = super::zedc(&["run", missing], "");
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (
            2,
            "/nonexistent-dir-l01-19/in.txt: zedc could not read this file: No such file or \
             directory. Check the path and that you may read the file.\n"
        )
    );
    let bind = format!("extra={missing}");
    let out = run("unreadable", src, "", &[&bind]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (
            2,
            "/nonexistent-dir-l01-19/in.txt: zedc could not read this file: No such file or \
             directory. Check the path and that you may read the file.\n"
        )
    );
    let extra = dir("unreadable").join("extra.txt");
    std::fs::write(&extra, "x\n").unwrap();
    let bind = format!("extra={}", extra.display());
    let record = "/nonexistent-dir-l01-19/run.record";
    let out = run("unreadable", src, "", &[&bind, "--record", record]);
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
    let args = ["run".to_string(), prog.display().to_string(), bind];
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&args, &mut Refusing, &mut out, &mut err);
    assert_eq!(
        (status, String::from_utf8(err).unwrap().as_str()),
        (
            2,
            "zedc could not read standard input, which the port `stdin` reads: the device is \
             gone. Give zedc a standard input it may read, or name a file for the port as \
             `stdin=<path>`.\n"
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
    std::fs::write(
        &real,
        "main() -> (stdout: Lines) {\n  stdout <- \"hi\";\n}\n",
    )
    .unwrap();
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
