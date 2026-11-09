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
        (2, "output port `report` needs a file: `report=path`\n")
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
        "port `stdout` is pushed 2 times in one wave; several pushes to one port arrive at \
         layer L7\n"
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
               stdout <- String(2 ^ 2 ^ 100 + 1);\n}\n";
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
    let src = "main() -> (stdout: Lines) {\n  stdout <- String(2 ^ 2 ^ 100);\n}\n";
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
    assert!(
        out.stderr
            .starts_with("writing port `log2` failed: #ioError(op: \"write\", path: \"/nonexistent-dir-l01-19/x.txt\", why: \"No such file or directory (os error 2)\")"),
        "{}",
        out.stderr
    );
}

#[test]
fn usage_errors_exit_2() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin[1] else \"\";\n}\n";
    let out = run("usage", src, "", &["nosuch=x"]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (2, "`main` has no port `nosuch`\n")
    );
    let files = "main(fs: Files) -> (stdout: Lines) {\n  stdout <- fs[\"a\"] else \"\";\n}\n";
    let out = run("usage", files, "", &["fs=x"]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (2, "input port `fs` reads no file: remove `fs=x`\n")
    );
    let args = "main(args: CommandLine) -> (stdout: Lines) {\n  stdout <- args[1] else \"\";\n}\n";
    let out = run("usage", args, "", &["args=x"]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (2, "input port `args` reads no file: remove `args=x`\n")
    );
    let out = run("usage", src, "", &["--bogus"]);
    assert_eq!(out.status, 2);
    assert!(out.stderr.starts_with("usage: zedc run"), "{}", out.stderr);
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
