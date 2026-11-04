//! A call passing an atom that the body of an undeclared parameter handles runs the body: the
//! values of the rows of the table in zedlanguage/zed issue 1, and of a lambda and a program
//! reading a missing line.

use super::value;
use crate::l01_19_whole_file_ports::run;

/// `r(arg)`, where `r(positional line) = body;`.
fn r(body: &str, arg: &str) -> String {
    value(
        &format!("r(positional line) = {body};\ny = r({arg});\n"),
        "y",
    )
}

#[test]
fn each_row_gives_what_its_body_says_for_a_missing_line() {
    for (body, want) in [
        ("if line is #notFound { #absent } else { \"s\" }", "#absent"),
        (
            "if line is #notFound { #absent } else { line else \"\" }",
            "#absent",
        ),
        (
            "if line is #notFound { #absent } else { trim(line else \"\") }",
            "#absent",
        ),
        ("trim(line else \"\")", "\"\""),
        ("line else \"\"", "\"\""),
        ("upper(line else \"\")", "\"\""),
        ("(line else 0) + 1", "1"),
        ("{ s = line else \"\"; trim(s) }", "\"\""),
        ("{ s = line; trim(s else \"\") }", "\"\""),
        ("{ t = s; s = line; trim(t else \"\") }", "\"\""),
    ] {
        assert_eq!(r(body, "#notFound"), want, "{body}");
    }
    let declared =
        "r(positional line: String | #notFound) = trim(line else \"\");\ny = r(#notFound);\n";
    assert_eq!(value(declared, "y"), "\"\"");
}

#[test]
fn a_present_line_is_still_trimmed() {
    assert_eq!(r("trim(line else \"\")", "\"  ok \""), "\"ok\"");
    assert_eq!(r("upper(line else \"\")", "\"ok\""), "\"OK\"");
    assert_eq!(r("(line else 0) + 1", "41"), "42");
}

#[test]
fn an_atom_the_else_replaces_need_not_be_the_one_the_is_test_names() {
    let body = "if line is #notFound { #absent } else { trim(line else \"\") }";
    assert_eq!(r(body, "#closed"), "\"\"");
}

#[test]
fn an_atom_an_is_test_alone_handles_runs_the_body_and_others_pass_by() {
    let body = "if line is #notFound { \"\" } else { trim(line) }";
    assert_eq!(r(body, "#notFound"), "\"\"");
    assert_eq!(r(body, "#closed"), "#closed");
}

#[test]
fn a_line_trimmed_without_else_passes_a_missing_line_by() {
    assert_eq!(r("trim(line)", "#notFound"), "#notFound");
}

#[test]
fn a_lambda_that_trims_a_line_or_the_empty_string_runs_for_a_missing_line() {
    let text =
        "clean = (line) -> trim(line else \"\");\ny = clean(#notFound);\nz = clean(\" b \");\n";
    assert_eq!(value(text, "y"), "\"\"");
    assert_eq!(value(text, "z"), "\"b\"");
}

#[test]
fn a_program_trimming_a_missing_line_runs_the_body() {
    let src = "r(positional line) = trim(line else \"\");\n\
               main(stdin: Lines) -> (stdout: Lines) {\n\
               \x20 stdout <- if r(stdin[9]) is #notFound { \"the body did not run\" } else { \"the body ran\" };\n\
               }\n";
    let out = run("missing_line", src, "x\n", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""));
    assert_eq!(out.stdout, "the body ran\n");
}
