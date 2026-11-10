//! A call passing an atom that the body of an undeclared parameter handles runs the body: the
//! values of the rows of the table in zedlanguage/zed issue 1, and of a lambda and a program
//! reading a missing line.

use super::value;
use zed_tests::step_helpers::l01_19_whole_file_ports::run;

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
    // `stdin[2]` is `#outOfBounds` on one line, and the body maps it to "empty"; `stdin[1]` is
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

#[test]
fn a_function_that_handles_its_parameter_and_passes_it_to_one_that_does_too() {
    // `g` handles the atoms of `x` and passes `x` on to `r`, which has two arrows. With no atom
    // in `x`, `r(x)` gives what `r`'s first arrow gives, a string, so `g` too has a first arrow
    // `(String) -> String`, and `g(" a ")` goes to a `Lines` port. A missing line takes both
    // functions' second arrows: `g`'s `else` and then `r`'s map it to a string.
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n";
    let main = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- g(\" a \") ++ \",\" ++ g(\"-\") ++ \",\" ++ (g(stdin[2]) else \"gone\");\n}\n";
    for (name, g, want) in [
        (
            "handles_then_passes_on",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { r(x) };\n",
            "a,dash,empty\n",
        ),
        (
            "binds_then_passes_on",
            "g(positional x) = { d = x else \"\"; r(x) };\n",
            "a,-,empty\n",
        ),
    ] {
        assert_eq!(output(name, &format!("{r}{g}{main}")), want, "{g}");
    }
}

#[test]
fn a_method_call_passes_its_receiver_as_the_first_argument() {
    // `x.r()` is `r(x)`: the receiver fills `r`'s first parameter, so with no atom in `x` the
    // call takes `r`'s first arrow, as the calls written `r(x)` above do, and each `g` gives a
    // string for a string. `r2` has a second parameter after the receiver. The same holds for
    // `x?.r()`, which passes an atom of `x` by, a chain `x.r().r()`, and a call through a local
    // name of a function or of a lambda.
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n\
             r2(positional line, positional d) = if (line else \"\") == \"\" { d } else { trim(line) };\n";
    let main = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- g(\" a \") ++ \",\" ++ g(\"-\") ++ \",\" ++ (g(stdin[2]) else \"gone\");\n}\n";
    for (name, g, want) in [
        ("method_wrapper", "g(positional x) = x.r();\n", "a,-,gone\n"),
        (
            "method_handles_then_passes_on",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { x.r() };\n",
            "a,dash,empty\n",
        ),
        (
            "method_binds_then_passes_on",
            "g(positional x) = { d = x else \"\"; x.r() };\n",
            "a,-,empty\n",
        ),
        (
            "method_second_argument",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { x.r2(\"none\") };\n",
            "a,dash,none\n",
        ),
        (
            "safe_method",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { x?.r() };\n",
            "a,dash,gone\n",
        ),
        (
            "chained_methods",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { x.r().r() };\n",
            "a,dash,empty\n",
        ),
        (
            "local_name_of_a_function",
            "g(positional x) = { f = r; if (x else \"\") == \"-\" { \"dash\" } else { f(x) } };\n",
            "a,dash,empty\n",
        ),
        (
            "local_lambda",
            "g(positional x) = { f = (positional y) -> if (y else \"\") == \"\" { \"e\" } else { trim(y) }; if (x else \"\") == \"-\" { \"dash\" } else { f(x) } };\n",
            "a,dash,e\n",
        ),
        (
            "method_without_parentheses",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { x.r };\n",
            "a,dash,empty\n",
        ),
        (
            "methods_without_parentheses_chained",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { x.r.r };\n",
            "a,dash,empty\n",
        ),
        (
            "method_without_parentheses_after_a_binding",
            "g(positional x) = { d = x else \"\"; x.r };\n",
            "a,-,empty\n",
        ),
        (
            "prelude_word_without_parentheses",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { x.trim };\n",
            "a,dash,gone\n",
        ),
    ] {
        assert_eq!(output(name, &format!("{r}{g}{main}")), want, "{g}");
    }
}

#[test]
fn a_function_value_called_with_a_handled_parameter_gives_a_string_for_a_string() {
    // The function reaches the call as a value: through a function `ap` that calls the one it
    // is given, or as the value of an expression. With no atom in `x`, `r` takes its first
    // arrow there too, so each `g` gives a string for a string; a missing line reaches `r`'s
    // second arrow, which handles it. A `g` that handles nothing takes no atom, so a missing
    // line passes its call by.
    let r = "r(positional line) = if (line else \"\") == \"\" { \"empty\" } else { trim(line) };\n\
             ap(positional f, positional v) = f(v);\n";
    let main = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- g(\" a \") ++ \",\" ++ g(\"-\") ++ \",\" ++ (g(stdin[2]) else \"gone\");\n}\n";
    for (name, g, want) in [
        (
            "higher_order",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { ap(r, x) };\n",
            "a,dash,empty\n",
        ),
        (
            "computed_callee",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { (if true { r } else { r })(x) };\n",
            "a,dash,empty\n",
        ),
        (
            "higher_order_wrapper",
            "g(positional x) = ap(r, x);\n",
            "a,-,gone\n",
        ),
    ] {
        assert_eq!(output(name, &format!("{r}{g}{main}")), want, "{g}");
    }
}

/// `src`'s output on the input `input`, which it must print without error.
fn output_on(name: &str, src: &str, input: &str) -> String {
    let out = run(name, src, input, &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    out.stdout
}

#[test]
fn a_line_that_may_be_missing_or_unreadable_runs_the_body_that_tests_for_a_missing_one() {
    // `stdin[2]` is `String | #outOfBounds | #ioError(..)`. A parameter tested only for
    // `#outOfBounds`, by `is` or by a pattern `else`, takes that atom and omits `#ioError`:
    // rule 6 treats each region of the argument apart, so `#ioError` passes the call by and
    // `#outOfBounds` runs the body. The call was rejected, since the atoms passed by only when
    // no arrow took any of them; a declared parameter was rejected the same way.
    let main =
        "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- g(stdin[2]) else \"gone\";\n}\n";
    for (name, g, missing) in [
        (
            "is_only",
            "g(positional x) = if x is #outOfBounds { \"nf\" } else { trim(x) };\n",
            "nf\n",
        ),
        (
            "pattern_else",
            "g(positional x) = trim(x else #outOfBounds -> \"\");\n",
            "\n",
        ),
        (
            "pattern_else_in_a_test",
            "g(positional x) = if (x else #outOfBounds -> \"\") == \"-\" { \"dash\" } else { trim(x) };\n",
            "gone\n",
        ),
        (
            "declared",
            "g(positional x: String | #outOfBounds) = if x is #outOfBounds { \"nf\" } else { trim(x) };\n",
            "nf\n",
        ),
    ] {
        let src = format!("{g}{main}");
        assert_eq!(output_on(name, &src, "x\n"), missing, "{g}");
        assert_eq!(output_on(name, &src, "x\n b \n"), "b\n", "{g}");
    }
}

#[test]
fn an_atom_the_parameter_omits_passes_by_while_the_one_it_tests_runs_the_body() {
    let g = "g(positional x) = if x is #outOfBounds { \"nf\" } else { trim(x) };\n";
    let main = "main(stdin: Lines) -> (stdout: Lines) {\n  \
                stdout <- if g(if stdin[1] == \"o\" { #other } else { stdin[2] }) is #other { \"other passed\" } else { \"ran\" };\n}\n";
    let src = format!("{g}{main}");
    assert_eq!(output_on("other", &src, "o\n"), "other passed\n");
    assert_eq!(output_on("other", &src, "x\n"), "ran\n");
}

#[test]
fn a_lambda_given_a_handled_parameter_through_a_function_passes_its_atoms_by_at_that_call() {
    // `ap(f, v) = f(v)` with the lambda `(y) -> trim(y)`, which takes no atom, and `x`, which
    // holds the atoms the `else` handles: an atom of `x` passes by at the call of `ap`, the
    // call whose argument gave it, so `g` gives a string for a string. The call was rejected
    // at `g`'s definition, `f` taking no atom.
    let ap = "ap(positional f, positional v) = f(v);\n";
    let main = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- g(\" a \") ++ \",\" ++ g(\"-\") ++ \",\" ++ (g(stdin[2]) else \"gone\");\n}\n";
    for (name, g, want) in [
        (
            "lambda_in_a_test",
            "g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { ap((positional y) -> trim(y), x) };\n",
            "a,dash,gone\n",
        ),
        (
            "lambda_after_a_default",
            "g(positional x) = { d = x else \"\"; ap((positional y) -> trim(y), x) };\n",
            "a,-,gone\n",
        ),
        (
            "lambda_through_two_functions",
            "ap2(positional f, positional v) = ap(f, v);\n\
             g(positional x) = if (x else \"\") == \"-\" { \"dash\" } else { ap2((positional y) -> trim(y), x) };\n",
            "a,dash,gone\n",
        ),
    ] {
        assert_eq!(output(name, &format!("{ap}{g}{main}")), want, "{g}");
    }
    // A missing line given to `ap` directly passes by at that call too.
    let direct = format!(
        "{ap}main(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- ap((positional y) -> trim(y), stdin[2]) else \"gone\";\n}}\n"
    );
    assert_eq!(output("lambda_direct", &direct), "gone\n");
}

#[test]
fn an_atom_a_function_gives_a_lambda_that_omits_it_is_rejected() {
    // No argument of the call of `ap` gives `#foo`, so it passes by nowhere.
    let src = "ap(positional f) = f(#foo);\n\
               main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- ap((positional y) -> trim(y));\n}\n";
    let out = run("foo", src, "x\n", &[]);
    assert_ne!(out.status, 0);
    assert!(
        out.stderr.contains("`f` does not take (#foo)"),
        "{}",
        out.stderr
    );
}
