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

/// `src`'s output on the one line `x`, which it must print without error.
fn output(name: &str, src: &str) -> String {
    let out = run(name, src, "x\n", &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    out.stdout
}

#[test]
fn a_function_whose_atoms_reach_its_result_gives_a_string_for_a_string() {
    // The body handles every loose atom of `line` and also passes them by through `trim`, so
    // `r` has two arrows: a string gives a string, which a `Lines` port takes, and only an
    // argument that may be an atom gives one. One arrow, `(String | #_) -> String | #_`,
    // rejected these programs, which ran before the parameter took the atoms.
    let main =
        |call: &str| format!("main(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- {call};\n}}\n");
    for (name, def, call, want) in [
        (
            "trim_or_empty",
            "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };",
            "r(\" a \")",
            "a\n",
        ),
        (
            "bool_branch",
            "r(positional c) = { d = c else false; if c { \"yes\" } else { \"no\" } };",
            "r(true)",
            "yes\n",
        ),
        (
            "int_branch",
            "r(positional n) = { d = n else 0; if n > 3 { \"big\" } else { \"small\" } };",
            "r(5)",
            "big\n",
        ),
    ] {
        assert_eq!(
            output(name, &format!("{def}\n{}", main(call))),
            want,
            "{def}"
        );
    }
}

#[test]
fn an_argument_that_may_be_an_atom_selects_the_arrow_that_takes_it() {
    // `stdin[2]` is `#notFound` on one line, and the body maps it to "empty"; `stdin[1]` is
    // the line. The lambda is the same function written as a value.
    let src = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n\
               main(stdin: Lines) -> (stdout: Lines) {\n\
               \x20 f = (positional x) -> if (x else \"\") == \"\" { \"e\" } else { trim(x) };\n\
               \x20 stdout <- (r(stdin[2]) else \"gone\") ++ \",\" ++ (r(stdin[1]) else \"gone\") ++ \",\" ++ f(\" b \") ++ \",\" ++ (f(stdin[2]) else \"gone\");\n\
               }\n";
    assert_eq!(output("selects_arrow", src), "empty,x,b,e\n");
    let body = "if (line else \"\") == \"\" { \"empty\" } else { trim(line) }";
    assert_eq!(r(body, "#notFound"), "\"empty\"");
    assert_eq!(r(body, "\" a \""), "\"a\"");
}

#[test]
fn a_function_that_calls_it_with_its_own_parameter_gives_a_string_for_a_string() {
    // `g`'s undeclared `x` takes the first arrow of `r`, so `g` is `(String) -> String`, and
    // an atom passed to `g` passes it by (rule 6), as before `r` took the atoms.
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n\
             g(positional x) = r(x);\n";
    let src = format!(
        "{r}main(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- g(\" a \") ++ \",\" ++ (g(stdin[2]) else \"passed by\");\n}}\n"
    );
    assert_eq!(output("wrapper", &src), "a,passed by\n");
}
