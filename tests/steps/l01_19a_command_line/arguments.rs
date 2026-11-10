//! The arguments after `--`, read by position, and the usage errors of the command line.

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;

use super::{ECHO, program, run, run_words, zedc};

#[test]
fn arguments_are_keyed_by_position_from_one() {
    // `zedc run greet.zed -- Ada "Grace Hopper"`: each argument is one word, spaces kept.
    let src = "main(args: CommandLine) -> (stdout: Lines) {\n  \
               stdout <- \"${args[1] else \"-\"}|${args[2] else \"-\"}\";\n}\n";
    let out = run("position", src, &["--", "Ada", "Grace Hopper"]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "Ada|Grace Hopper\n"));
    // The family itself is `{1: "a", 2: "b c"}`, written one entry per line in key order.
    let out = run("family", ECHO, &["--", "a", "b c"]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "a\nb c\n"));
}

#[test]
fn a_position_past_the_last_argument_is_not_found() {
    let src = "main(args: CommandLine) -> (stdout: Lines) {\n  \
               stdout <- \"${args[0] else \"none\"}|${args[2] else \"none\"}|${args[3] else \"none\"}\";\n}\n";
    let out = run("missing", src, &["--", "one", "two"]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "none|two|none\n"));
}

#[test]
fn with_no_arguments_the_family_is_empty() {
    // No `--`, and `--` with nothing after it, both give the empty family.
    for more in [&[][..], &["--"][..]] {
        let out = run("empty", ECHO, more);
        assert_eq!((out.status, out.stdout.as_str()), (0, ""), "{more:?}");
    }
    let src = "main(args: CommandLine) -> (stdout: Lines) {\n  \
               stdout <- args[1] else \"no arguments\";\n}\n";
    assert_eq!(run("none", src, &[]).stdout, "no arguments\n");
}

#[test]
fn every_word_after_the_first_dashes_is_an_argument() {
    // Words that would be options or bindings before `--` are plain arguments after it,
    // a second `--` and an empty word among them.
    let more = ["--", "--record", "x", "stdout=out.txt", "--", ""];
    let out = run("options", ECHO, &more);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "--record\nx\nstdout=out.txt\n--\n\n")
    );
}

#[test]
fn ports_are_bound_before_the_dashes_and_arguments_follow() {
    let d = super::dir("bind");
    let input = d.join("in.txt");
    std::fs::write(&input, "3\n").unwrap();
    let src = "main(n: Lines, args: CommandLine) -> (stdout: Lines) {\n  \
               stdout <- \"${n[1] else \"\"} ${args[1] else \"\"}\";\n}\n";
    let bind = format!("n={}", input.display());
    let out = run("bind", src, &[&bind, "--", "apples"]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "3 apples\n"));
}

#[test]
fn a_program_without_the_port_ignores_its_arguments() {
    let src = "main() -> (stdout: Lines) {\n  stdout <- \"hello\";\n}\n";
    let out = run("ignored", src, &["--", "a", "b"]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "hello\n"));
}

/// The message for argument `n` after `--` that is not UTF-8.
fn not_utf8(n: usize) -> String {
    format!(
        "command-line argument {n} (counted from the first word after `--`) is not UTF-8, and a \
         `CommandLine` port gives the program each argument as a string, which must be UTF-8 \
         text. Pass the argument as UTF-8 text, or pass the path of a file that holds it.\n"
    )
}

/// `zedc run <prog> -- <before…> <bad> <after…>`, `bad` a word that is not UTF-8.
fn with_bad_argument(prog: &OsString, before: &[&str], after: &[&str]) -> Vec<OsString> {
    let mut words = run_words(prog, &["--"]);
    words.extend(before.iter().map(OsString::from));
    words.push(OsString::from_vec(vec![b'x', 255]));
    words.extend(after.iter().map(OsString::from));
    words
}

#[test]
fn an_argument_that_is_not_utf8_is_a_usage_error_naming_its_position() {
    let prog = program("not_utf8", ECHO);
    let out = zedc(&with_bad_argument(&prog, &[], &[]));
    assert_eq!(
        (out.status, out.stderr.as_str(), out.stdout.as_str()),
        (2, &*not_utf8(1), "")
    );
    let out = zedc(&with_bad_argument(
        &prog,
        &["fine", "also fine"],
        &["later"],
    ));
    assert_eq!((out.status, out.stderr.as_str()), (2, &*not_utf8(3)));
    // Before `--` a word that is not UTF-8 is named by its place among the words.
    let mut words = vec![OsString::from("run"), OsString::from_vec(vec![255])];
    words.push(prog);
    let out = zedc(&words);
    assert_eq!(
        (out.status, out.stderr.as_str()),
        (
            2,
            "word 2 of the command line is not UTF-8, and the words before `--` (files, ports \
             and options) are read as UTF-8 text. Name each file by a path written in UTF-8, or \
             rename the file.\n"
        )
    );
}

#[test]
fn a_read_may_be_out_of_bounds_so_the_checker_asks_for_its_disposal() {
    let src = "main(args: CommandLine) -> (stdout: Lines) {\n  stdout <- args[1];\n}\n";
    let out = run("undisposed", src, &["--", "a"]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr.contains(
            "a `Lines` port takes a `String` or a family of strings, not String | #outOfBounds"
        ),
        "{}",
        out.stderr
    );
}

#[test]
fn a_command_line_port_is_an_input() {
    let src = "main() -> (args: CommandLine) {\n  args <- \"a\";\n}\n";
    assert_eq!(
        zedc::run::load(src.as_bytes()).err().as_deref(),
        Some(
            "1:12: the output port `args` of `main` is declared as `CommandLine`, and an \
             output port writes lines of text, so its type must be `Lines`. Write `args: Lines`, \
             and push to it a string, which writes one line, or a family of strings, which \
             writes one line per entry, such as `args <- String(x);`."
        )
    );
}
