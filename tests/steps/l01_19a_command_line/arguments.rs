//! The arguments after `--`, read by position, and the usage errors of the command line.

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;

use super::{ECHO, program, run, run_words, zedc};

#[test]
fn arguments_are_keyed_by_position_from_one() {
    // `zedc run greet.zed -- Ada "Grace Hopper"`: each argument is one word, spaces kept.
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"${m.args[1] else \"-\"}|${m.args[2] else \"-\"}\";\n}\n";
    let out = run("position", src, &["--", "Ada", "Grace Hopper"]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "Ada|Grace Hopper\n"));
    // The family itself is `{1: "a", 2: "b c"}`, written one entry per line in key order.
    let out = run("family", ECHO, &["--", "a", "b c"]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "a\nb c\n"));
}

#[test]
fn a_position_past_the_last_argument_is_not_found() {
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"${m.args[0] else \"none\"}|${m.args[2] else \"none\"}|${m.args[3] else \"none\"}\";\n}\n";
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
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- m.args[1] else \"no arguments\";\n}\n";
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
fn standard_input_and_the_arguments_are_read_together() {
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"${m.stdin[1] else \"\"} ${m.args[1] else \"\"}\";\n}\n";
    let out = zed_tests::step_helpers::l01_19_whole_file_ports::run(
        "l01_19a_together",
        src,
        "3\n",
        &["--", "apples"],
    );
    assert_eq!((out.status, out.stdout.as_str()), (0, "3 apples\n"));
}

#[test]
fn a_program_without_the_port_ignores_its_arguments() {
    let src = "main(m: MainArgs) {\n  m.stdout <- \"hello\";\n}\n";
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
            "word 2 of the command line is not UTF-8, and the words before `--` (the program's \
             file and options) are read as UTF-8 text. Name each file by a path written in \
             UTF-8, or rename the file.\n"
        )
    );
}

#[test]
fn a_read_may_be_out_of_bounds_so_the_checker_asks_for_its_disposal() {
    let src = "main(m: MainArgs) {\n  m.stdout <- m.args[1];\n}\n";
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
fn the_arguments_are_an_input() {
    let src = "main(m: MainArgs) {\n  m.args <- \"a\";\n}\n";
    assert_eq!(
        zedc::run::load(src.as_bytes()).err().as_deref(),
        Some(
            "2:3: `m.args <- …` pushes to `m.args`, and `m.args` is an input of the program, \
             which `main` reads and never writes. Push the lines the program writes to \
             `m.stdout` (its standard output) or `m.stderr` (its standard error), as \
             `m.stdout <- lines;`."
        )
    );
}

#[test]
fn a_push_target_may_end_in_one_view() {
    // `PushTarget = Name ('.' Name)* ('::' Name)?` (sec:grammar): `m.stdout::bytes` parses as
    // the view `bytes` of `m.stdout` (DESIGN step L7.3h), which this zedc does not compile yet;
    // `m::stdout` is the view `stdout` of `m`, never the field `m.stdout`.
    for target in ["m.stdout::bytes", "m::stdout"] {
        let src = format!("main(m: MainArgs) {{\n  {target} <- \"a\";\n}}\n");
        assert_eq!(
            zedc::run::load(src.as_bytes()).err().as_deref(),
            Some(
                format!(
                    "2:3: a push to a view of a port `{target}` is part of the Zed language, and \
                     this version of zedc does not compile it yet. Write the program without \
                     it, with the forms this zedc compiles."
                )
                .as_str()
            ),
            "{target}"
        );
    }
}

#[test]
fn a_push_target_has_at_most_one_view_and_it_comes_last() {
    // Neither is a push target, so each reads as an expression, which stops at the `<-`.
    for (target, at) in [
        ("m.stdout::bytes::len", "2:24"),
        ("m::stdout.bytes", "2:19"),
    ] {
        let src = format!("main(m: MainArgs) {{\n  {target} <- \"a\";\n}}\n");
        let err = zedc::run::load(src.as_bytes()).err().unwrap_or_default();
        assert!(
            err.starts_with(&format!("{at}: expected ")),
            "{target}: {err}"
        );
    }
}
