//! Calls of functions with named and positional parameters: the checker accepts the calls
//! elaboration accepts and reports the errors elaboration reports, with the same message at
//! the same place, and `zedc run` reports each error once (DESIGN.md sec:values_morphisms:
//! "a parameter written `positional x` ... is passed only by position; every other parameter
//! is passed only by name, in any order").

use super::type_errors;
use crate::l01_16_elaboration::{errors, value};
use crate::l01_19_whole_file_ports::run;

/// A greeting with a positional name and a named punctuation mark, and three arithmetic
/// helpers: `dbl` and `sub` take their parameters by name, `add` by position.
const DECLS: &str = "greet(positional name, punct = \"!\") = name ++ punct;\n\
                     dbl(x) = x + x;\n\
                     sub(a, b) = a - b;\n\
                     add(positional a, positional b) = a + b;\n\
                     tax(price, rate = price / 10.0) = price * rate;\n\
                     zero() = 0;\n";

#[test]
fn calls_that_pass_each_parameter_in_its_form_are_accepted_and_run() {
    let cases = [
        ("y = dbl(x: 3);", "6"),
        ("y = sub(b: 5, a: 3);", "-2"),
        ("y = add(1, 2);", "3"),
        ("y = greet(\"Al\");", "\"Al!\""),
        ("y = greet(\"Al\", punct: \"?\");", "\"Al?\""),
        // The receiver fills the first parameter, named or positional.
        ("y = 3.dbl();", "6"),
        ("y = 3.sub(b: 1);", "2"),
        ("y = 3.add(4);", "7"),
        // A value of a function's type is called as its type says.
        ("k = dbl;\ny = k(x: 4);", "8"),
        ("k = add;\ny = k(1, 2);", "3"),
        ("h = greet(\"Al\", ...);\ny = h(punct: \"?\");", "\"Al?\""),
        ("t = tax;\ny = t(price: 10.0, rate: 0.5);", "5.0"),
        // A lambda with no expected type takes its parameters by position.
        ("inc = x -> x + 1;\ny = inc(3);", "4"),
    ];
    for (call, want) in cases {
        let text = format!("{DECLS}{call}\n");
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{call}");
        assert_eq!(value(&text, "y"), want, "{call}");
    }
}

#[test]
fn the_checker_and_elaboration_reject_a_misplaced_argument_alike() {
    let named =
        |p: &str, f: &str, at: &str| format!("`{p}` of `{f}` is named: pass it as `{p}: …` [{at}]");
    let positional = |p: &str, f: &str, at: &str| {
        format!("`{p}` of `{f}` is positional: pass it by position [{at}]")
    };
    let cases: Vec<(&str, Vec<String>)> = vec![
        // A positional argument for a named parameter, and the reverse.
        ("y = dbl(3);", vec![named("x", "dbl", "3")]),
        ("y = sub(3, 5);", vec![named("a", "sub", "3")]),
        (
            "y = greet(\"Al\", \"?\");",
            vec![named("punct", "greet", "\"?\"")],
        ),
        ("y = 3.sub(5);", vec![named("b", "sub", "5")]),
        ("y = add(a: 1, b: 2);", vec![positional("a", "add", "1")]),
        (
            "y = greet(name: \"Al\");",
            vec![positional("name", "greet", "\"Al\"")],
        ),
        // A name no parameter has, a parameter passed twice, and one argument too many.
        (
            "y = dbl(z: 3);",
            vec!["`dbl` has no parameter `z` [3]".into()],
        ),
        (
            "y = 3.dbl(x: 4);",
            vec!["`x` is already supplied [4]".into()],
        ),
        (
            "y = add(1, 2, 3);",
            vec!["too many arguments: `add` takes 2 [3]".into()],
        ),
        (
            "y = 3.zero();",
            vec!["`zero` has no parameter for a receiver [3.zero()]".into()],
        ),
        // Parameters left out with no default, and `...` that curries no named parameter.
        (
            "y = sub(a: 1);",
            vec!["missing argument `b` of `sub` [sub(a: 1)]".into()],
        ),
        (
            "y = sub();",
            vec![
                "missing argument `a` of `sub` [sub()]".into(),
                "missing argument `b` of `sub` [sub()]".into(),
            ],
        ),
        (
            "y = dbl(x: 1, ...);",
            vec!["`...` leaves no named parameter out [dbl(x: 1, ...)]".into()],
        ),
        (
            "y = greet(punct: \"?\", ...);",
            vec![
                "`...` curries named parameters only; the positional `name` is left out \
                 [greet(punct: \"?\", ...)]"
                    .into(),
            ],
        ),
        // Through a value, the error names the value's type.
        (
            "k = dbl;\ny = k(4);",
            vec![named("x", "(x: T) -> T for T in int | f64 | rat", "4")],
        ),
        (
            "k = add;\ny = k(a: 1, b: 2);",
            vec![positional("a", "(T, T) -> T for T in int | f64 | rat", "1")],
        ),
        (
            "inc = x -> x + 1;\ny = inc(x: 3);",
            vec![positional("x", "(int) -> int", "3")],
        ),
        (
            "k = sub;\ny = k(a: 1);",
            vec![
                "missing argument `b` of `(a: T, b: T) -> T for T in int | f64 | rat` [k(a: 1)]"
                    .into(),
            ],
        ),
        (
            "t = tax;\ny = t(price: 10.0);",
            vec![
                "the default of `rate` reads the function's other parameters, so only a call \
                 of the declared function fills it: pass `rate` [t(price: 10.0)]"
                    .into(),
            ],
        ),
    ];
    for (call, want) in cases {
        let text = format!("{DECLS}{call}\n");
        assert_eq!(type_errors(&text), want, "checker: {call}");
        assert_eq!(errors(&text), want, "elaboration: {call}");
    }
}

#[test]
fn zedc_run_reports_a_misplaced_argument_once_with_the_declaration() {
    let program = |call: &str| {
        format!(
            "greet(name) = \"Hello, ${{name}}!\";\n\n\
             main(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- {call};\n}}\n"
        )
    };
    let ok = run("named_call_ok", &program("greet(name: \"Al\")"), "", &[]);
    assert_eq!(
        (ok.status, ok.stdout.as_str()),
        (0, "Hello, Al!\n"),
        "{}",
        ok.stderr
    );
    let bad = run("named_call_bad", &program("greet(\"Al\")"), "", &[]);
    assert_eq!(bad.status, 1);
    assert_eq!(bad.stdout, "");
    let message = "4:19: `name` of `greet` is named: pass it as `name: …`\n";
    assert_eq!(bad.stderr.matches(message).count(), 1, "{}", bad.stderr);
    assert!(
        bad.stderr
            .contains("`greet` is declared here, `(name: _) -> String`"),
        "{}",
        bad.stderr
    );
}
