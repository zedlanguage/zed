//! Writes: one whole-value push per port per wave, committed when the wave ends, each with
//! an acknowledgment; a failed write aborts the wave.

use zed_kernel::Value;
use zedc::run::commit;

use super::{dir, run};

#[test]
fn a_report_goes_to_a_file_bound_on_the_command_line() {
    let d = dir("report");
    let path = d.join("report.txt");
    std::fs::write(&path, "stale\n").unwrap();
    let src = "main(stdin: Lines) -> (report: Lines, stdout: Lines) {\n  \
               report <- stdin;\n  stdout <- \"wrote the report\";\n}\n";
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
    // `out` is pushed first in the text, then `3 ** 10000000` is past the size limit.
    let src = "main() -> (out: Lines, stdout: Lines) {\n  \
               out <- \"half done\";\n  stdout <- String(3 ** 10000000);\n}\n";
    let bind = format!("out={}", path.display());
    let out = run("abort", src, "", &[&bind]);
    assert_eq!(out.status, 1, "{}", out.stderr);
    assert!(out.stderr.contains("size limit"), "{}", out.stderr);
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

#[test]
fn only_strings_are_written_as_lines() {
    let src = "main() -> (stdout: Lines) {\n  stdout <- 42;\n}\n";
    let out = run("number", src, "", &[]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (1, "port `stdout` takes strings; 42 was pushed\n")
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
            Err("disk full".into())
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
            ("stdout".to_string(), "#ioError(\"disk full\")".to_string()),
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
            .starts_with("writing port `log2` failed: #ioError(\"/nonexistent-dir-l01-19/x.txt: "),
        "{}",
        out.stderr
    );
}

#[test]
fn usage_errors_exit_2() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin;\n}\n";
    let out = run("usage", src, "", &["nosuch=x"]);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (2, "`main` has no port `nosuch`\n")
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
