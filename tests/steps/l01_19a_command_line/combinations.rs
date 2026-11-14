//! Completeness of step L1.19a (plan row TEST-complete-ports, COMPLETENESS.md beside this
//! file): arguments of each kind, read in each position an expression takes. A failing case
//! names itself; all cases of a table run before the test reports.

use super::{ECHO, run};

/// Runs each case `(name, program, words after the file, status, standard output)` and
/// asserts the status and output of every one, naming each case that differs.
fn expect(table: &str, cases: &[(&str, &str, &[&str], u8, &str)]) {
    let mut wrong = Vec::new();
    for &(name, src, more, status, stdout) in cases {
        let out = run(&format!("l01_19a_{table}_{name}"), src, more);
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
fn an_argument_of_each_kind_is_written_as_given() {
    expect(
        "kinds",
        &[
            ("empty_word", ECHO, &["--", ""], 0, "\n"),
            (
                "empty_between_words",
                ECHO,
                &["--", "a", "", "b"],
                0,
                "a\n\nb\n",
            ),
            (
                "leading_dash",
                ECHO,
                &["--", "-x", "--option"],
                0,
                "-x\n--option\n",
            ),
            ("only_dashes", ECHO, &["--", "--", "--"], 0, "--\n--\n"),
            ("spaces_kept", ECHO, &["--", " a  b "], 0, " a  b \n"),
            (
                "non_ascii",
                ECHO,
                &["--", "h\u{e9}", "\u{1d11e}"],
                0,
                "h\u{e9}\n\u{1d11e}\n",
            ),
            ("tab_inside", ECHO, &["--", "a\tb"], 0, "a\tb\n"),
            (
                "record_word_after_dashes",
                ECHO,
                &["--", "--record", "x"],
                0,
                "--record\nx\n",
            ),
        ],
    );
}

#[test]
fn an_argument_is_read_in_each_position() {
    let interpolated = writes("\"<${m.args[0] else \"-\"}>\"");
    let condition = writes("if (m.args[0] else \"\") == \"on\" { \"yes\" } else { \"no\" }");
    let computed = writes("m.args[0 + 1] else \"none\"");
    let helper = "first(a: CommandLine) = a[0] else \"none\";\n\
                  main(m: MainArgs) {\n  m.stdout <- first(a: m.args);\n}\n";
    let as_int = writes("\"${(int(m.args[0] else \"\") else 0) + 1}\"");
    let as_path = "main(m: MainArgs) {\n  fs = main::files;\n  \
                   m.stdout <- (fs[m.args[0] else \"\"] else #notFound -> \"nf\") else \"io\";\n}\n";
    expect(
        "position",
        &[
            ("interpolated", &interpolated, &["--", "x"], 0, "<x>\n"),
            ("interpolated_none", &interpolated, &[], 0, "<->\n"),
            ("condition_true", &condition, &["--", "on"], 0, "yes\n"),
            ("condition_false", &condition, &["--", "off"], 0, "no\n"),
            ("key_computed", &computed, &["--", "a", "b"], 0, "b\n"),
            (
                "key_computed_past_the_last",
                &computed,
                &["--", "a"],
                0,
                "none\n",
            ),
            ("helper_parameter", helper, &["--", "x"], 0, "x\n"),
            ("helper_parameter_none", helper, &[], 0, "none\n"),
            ("cast_to_int", &as_int, &["--", "41"], 0, "42\n"),
            ("cast_that_fails", &as_int, &["--", "x"], 0, "1\n"),
            (
                "path_of_a_file_that_is_not_there",
                as_path,
                &["--", "/nonexistent/zed"],
                0,
                "nf\n",
            ),
        ],
    );
}
