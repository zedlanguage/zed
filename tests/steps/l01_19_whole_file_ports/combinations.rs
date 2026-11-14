//! Completeness of step L1.19 (plan row TEST-complete-ports, COMPLETENESS.md beside this
//! file): the ports of `main` met in each position an expression takes and with the other
//! features of layer L1, each case a small program whose status and output DESIGN.md gives.
//! A failing case names itself; all cases of a table run before the test reports.

use zed_tests::step_helpers::l01_19_whole_file_ports::run_bytes;

use super::{dir, run};

/// Runs each case `(name, program, standard input, status, standard output)` and asserts the
/// status and output of every one, naming each case that differs.
fn expect(table: &str, cases: &[(&str, &str, &[u8], u8, &str)]) {
    let mut wrong = Vec::new();
    for &(name, src, stdin, status, stdout) in cases {
        let out = run_bytes(&format!("{table}_{name}"), src, stdin, &[]);
        if (out.status, out.stdout.as_str()) != (status, stdout) {
            wrong.push(format!(
                "{name}: gave status {} and {:?}, expected {status} and {stdout:?}\n{}",
                out.status, out.stdout, out.stderr
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// `main` writing `expr` to standard output.
fn writes(expr: &str) -> String {
    format!("main(m: MainArgs) {{\n  m.stdout <- {expr};\n}}\n")
}

#[test]
fn a_line_of_standard_input_is_read_in_each_position() {
    let interpolated = writes("\"<${m.stdin[0] else \"-\"}>\"");
    let condition = writes("if (m.stdin[0] else \"\") == \"a\" { \"yes\" } else { \"no\" }");
    let bound = "main(m: MainArgs) {\n  lines = m.stdin;\n  m.stdout <- lines[0] else \"\";\n}\n";
    let computed = writes("m.stdin[1 + 1] else \"\"");
    let helper = "first(s: Lines) = s[0] else \"none\";\n\
                  main(m: MainArgs) {\n  m.stdout <- first(s: m.stdin);\n}\n";
    expect(
        "stdin_position",
        &[
            ("interpolated", &interpolated, b"x\n", 0, "<x>\n"),
            ("interpolated_empty_input", &interpolated, b"", 0, "<->\n"),
            ("condition_true", &condition, b"a\n", 0, "yes\n"),
            ("condition_false", &condition, b"b\n", 0, "no\n"),
            ("bound_to_a_name", bound, b"x\ny\n", 0, "x\n"),
            ("helper_parameter", helper, b"x\n", 0, "x\n"),
            ("helper_parameter_empty", helper, b"", 0, "none\n"),
            ("key_computed", &computed, b"a\nb\nc\n", 0, "c\n"),
        ],
    );
}

#[test]
fn a_key_outside_the_lines_gives_out_of_bounds() {
    let at = |k: &str| {
        writes(&format!(
            "(m.stdin[{k}] else #outOfBounds -> \"oob\") else \"other\""
        ))
    };
    let (past, negative, huge_negative, zero) =
        (at("3"), at("-1"), at("-99999999999999999999999"), at("0"));
    expect(
        "stdin_key",
        &[
            ("one_past_the_last", &past, b"a\nb\nc\n", 0, "oob\n"),
            ("negative", &negative, b"a\n", 0, "oob\n"),
            ("below_64_bits", &huge_negative, b"a\n", 0, "oob\n"),
            ("zero_of_no_lines", &zero, b"", 0, "oob\n"),
            ("zero_of_one_line", &zero, b"a\n", 0, "a\n"),
        ],
    );
}

#[test]
fn a_line_is_utf8_text_or_io_error() {
    let echo = writes("(m.stdin[0] else #ioError -> \"bad\") else \"none\"");
    expect(
        "stdin_utf8",
        &[
            ("ascii", &echo, b"plain\n", 0, "plain\n"),
            (
                "two_byte",
                &echo,
                "h\u{e9}llo\n".as_bytes(),
                0,
                "h\u{e9}llo\n",
            ),
            (
                "three_byte",
                &echo,
                "\u{20ac}\n".as_bytes(),
                0,
                "\u{20ac}\n",
            ),
            (
                "four_byte",
                &echo,
                "\u{1d11e}\n".as_bytes(),
                0,
                "\u{1d11e}\n",
            ),
            ("nul_inside", &echo, b"a\0b\n", 0, "a\0b\n"),
            ("tab_inside", &echo, b"a\tb\n", 0, "a\tb\n"),
            ("lone_continuation_byte", &echo, b"\x80\n", 0, "bad\n"),
            ("overlong_nul", &echo, b"\xc0\x80\n", 0, "bad\n"),
            ("surrogate", &echo, b"\xed\xa0\x80\n", 0, "bad\n"),
            ("above_u10ffff", &echo, b"\xf4\x90\x80\x80\n", 0, "bad\n"),
            ("cut_short_at_the_end", &echo, b"\xe2\x82", 0, "bad\n"),
            (
                "cut_short_before_the_line_end",
                &echo,
                b"\xe2\x82\n",
                0,
                "bad\n",
            ),
        ],
    );
}

#[test]
fn a_pushed_value_is_written_as_lines_at_any_depth() {
    let (embedded, empty_string, unicode) = (
        writes("\"a\\nb\""),
        writes("\"\""),
        writes("\"\u{e9}\u{1d11e}\""),
    );
    expect(
        "push_shape",
        &[
            ("string_holding_a_line_end", &embedded, b"", 0, "a\nb\n"),
            ("empty_string", &empty_string, b"", 0, "\n"),
            ("non_ascii_string", &unicode, b"", 0, "\u{e9}\u{1d11e}\n"),
        ],
    );
}

#[test]
fn of_two_push_sites_only_the_one_that_runs_writes() {
    let src = "main(m: MainArgs) {\n  \
               done = if (m.stdin[0] else \"\") == \"a\" {\n    m.stdout <- \"A\";\n    1\n  } \
               else {\n    m.stdout <- \"B\";\n    0\n  };\n}\n";
    expect(
        "two_sites",
        &[
            ("first_runs", src, b"a\n", 0, "A\n"),
            ("second_runs", src, b"z\n", 0, "B\n"),
        ],
    );
}

#[test]
fn a_push_whose_value_may_hold_a_failure_is_rejected_at_the_push() {
    let cases = [
        ("stdin_line", writes("m.stdin[0]")),
        (
            "stdin_line_to_stderr",
            "main(m: MainArgs) {\n  m.stderr <- m.stdin[0];\n}\n".into(),
        ),
        ("argument", writes("m.args[0]")),
        ("environment", writes("m.env[\"ZED_X\"]")),
        (
            "file",
            "main(m: MainArgs) {\n  fs = main::files;\n  m.stdout <- fs[\"a\"];\n}\n".into(),
        ),
        ("bare_atom", writes("#notFound")),
    ];
    let mut wrong = Vec::new();
    for (name, src) in &cases {
        let out = run(&format!("failure_push_{name}"), src, "x\n", &[]);
        if out.status != 1
            || !out.stdout.is_empty()
            || !out
                .stderr
                .contains("A `Lines` port takes a `String` or a family of strings")
        {
            wrong.push(format!("{name}: status {}\n{}", out.status, out.stderr));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_file_is_read_whole_in_each_position() {
    let d = dir("files_position");
    let empty = d.join("empty.txt");
    let no_end = d.join("no_end.txt");
    std::fs::write(&empty, "").unwrap();
    std::fs::write(&no_end, "a\nb").unwrap();
    let missing = d.join("missing.txt");
    let read = |p: &std::path::Path| {
        format!(
            "main(m: MainArgs) {{\n  fs = main::files;\n  \
             t = (fs[\"{}\"] else #notFound -> \"nf\") else \"io\";\n  m.stdout <- \"<${{t}}>\";\n}}\n",
            p.display()
        )
    };
    let by_stdin = "main(m: MainArgs) {\n  fs = main::files;\n  \
                    m.stdout <- (fs[m.stdin[0] else \"\"] else #notFound -> \"nf\") else \"io\";\n}\n";
    let in_helper = format!(
        "text(p: String) = (main::files[p] else #notFound -> \"nf\") else \"io\";\n\
         main(m: MainArgs) {{\n  m.stdout <- text(p: \"{}\");\n}}\n",
        no_end.display()
    );
    let path_line = format!("{}\n", no_end.display());
    let (r_empty, r_no_end, r_missing, r_dir) =
        (read(&empty), read(&no_end), read(&missing), read(&d));
    expect(
        "files_position",
        &[
            ("empty_file_is_the_empty_text", &r_empty, b"", 0, "<>\n"),
            ("last_line_without_line_end", &r_no_end, b"", 0, "<a\nb>\n"),
            ("missing_file", &r_missing, b"", 0, "<nf>\n"),
            ("directory", &r_dir, b"", 0, "<io>\n"),
            (
                "path_from_standard_input",
                by_stdin,
                path_line.as_bytes(),
                0,
                "a\nb\n",
            ),
            ("empty_path_from_standard_input", by_stdin, b"", 0, "nf\n"),
            ("read_in_a_helper", &in_helper, b"", 0, "a\nb\n"),
        ],
    );
}
