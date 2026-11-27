//! Calls of functions with named and positional parameters: the checker accepts the calls
//! elaboration accepts and reports the errors elaboration reports, with the same message at
//! the same place, and `zedc run` reports each error once (DESIGN.md sec:values_morphisms:
//! "a parameter written `positional x` ... is passed only by position; every other parameter
//! is passed only by name, in any order").

use super::type_errors;
use zed_tests::step_helpers::l01_16_elaboration::{errors, value};
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_29_diagnostics::rejected_with_main;

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
        ("t = tax;\ny = t(price: 10.0f64, rate: 0.5f64);", "5.0"),
        // The function a value holds fills its own default, which may read its other
        // parameters (DESIGN.md sec:values_morphisms, "The function called places the
        // arguments").
        ("t = tax;\ny = t(price: 10.0);", "10.0"),
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
    let named = |p: &str, f: &str, at: &str| {
        format!(
            "this argument is passed by position, and the parameter it reaches, `{p}` of `{f}`, is a named parameter, which a call passes only by name, as `{p}: …`. [{at}]"
        )
    };
    let positional = |p: &str, f: &str, at: &str| {
        format!(
            "this argument is passed by name, as `{p}: …`, and `{p}` of `{f}` is positional, so a call passes it only by position. [{at}]"
        )
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
            vec!["this argument is passed by the name `z`, and `dbl` has no parameter of that name, so the argument has no parameter to go to. [3]".into()],
        ),
        (
            "y = 3.dbl(x: 4);",
            vec!["this argument gives `x` of `dbl` a value, and an argument before it already gave `x` one; a call gives each parameter one value. [4]".into()],
        ),
        (
            "y = add(1, 2, 3);",
            vec!["this argument is one more than `add` takes: `add` takes 2 arguments by position, and the arguments before this one already fill them all. [3]".into()],
        ),
        (
            "y = 3.zero();",
            vec!["this call passes a value before the dot to `zero`, as `x.zero(…)` does, but `zero` takes no parameters, so the value before the dot has no parameter to go to. [3.zero()]".into()],
        ),
        // Parameters left out with no default, and `...` that curries no named parameter.
        (
            "y = sub(a: 1);",
            vec!["this call of `sub` gives no value to its parameter `b`, and `b` has no default, so the call cannot be made. [sub(a: 1)]".into()],
        ),
        (
            "y = sub();",
            vec![
                "this call of `sub` gives no value to its parameter `a`, and `a` has no default, so the call cannot be made. [sub()]".into(),
                "this call of `sub` gives no value to its parameter `b`, and `b` has no default, so the call cannot be made. [sub()]".into(),
            ],
        ),
        (
            "y = dbl(x: 1, ...);",
            vec!["this call of `dbl` ends in `...`, which makes a function of the named parameters the call leaves out, and the call gives every named parameter a value, so `...` has no parameter to leave out. [dbl(x: 1, ...)]".into()],
        ),
        (
            "y = greet(punct: \"?\", ...);",
            vec![
                "this call of `greet` ends in `...`, which makes a function of the named parameters the call leaves out, and the call also leaves out `name`, a positional parameter, which `...` cannot \
                 leave out. [greet(punct: \"?\", ...)]"
                    .into(),
            ],
        ),
        // Through a value, the error names the value's type.
        (
            "k = dbl;\ny = k(4);",
            vec![named("x", "(x: T) -> T for T in int | f32 | f64 | rat", "4")],
        ),
        (
            "k = add;\ny = k(a: 1, b: 2);",
            vec![positional("a", "(T, T) -> T for T in int | f32 | f64 | rat", "1")],
        ),
        (
            "inc = x -> x + 1;\ny = inc(x: 3);",
            vec![positional("x", "T -> T for T in int | f32 | f64 | rat", "3")],
        ),
        (
            "k = sub;\ny = k(a: 1);",
            vec![
                "this call of `(a: T, b: T) -> T for T in int | f32 | f64 | rat` gives no value to its parameter `b`, and `b` has no default, so the call cannot be made. [k(a: 1)]"
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

/// A named argument that gives the receiver's parameter a second value names "an argument
/// before it"; written on another line, the receiver is shown as well, with a note at it, so
/// the two lines the message names are both in the output (QUESTIONS A111, plan row
/// MSG-multi-line-context). The parser refuses a name written twice in one call, so the
/// receiver is the first value a program reaches this error with.
#[test]
fn a_second_value_for_the_receiver_s_parameter_shows_the_receiver() {
    let text = format!("{DECLS}y = 3\n  .dbl(x: 4);\n");
    let out = rejected_with_main(&text);
    let message = "already gave `x` one; a call gives each parameter one value";
    assert_eq!(out.matches(message).count(), 1, "{out}");
    let note = (out.lines())
        .find(|l| l.contains("the first value for `x`"))
        .unwrap_or_else(|| panic!("no note at the receiver in:\n{out}"));
    assert!(
        note.contains("7:5:"),
        "the note is not at `3`, line 7: {note}\n{out}"
    );
    assert!(
        out.lines().any(|l| l.trim_end().ends_with("7 | y = 3")),
        "{out}"
    );
}

/// A parameter of a function type has no name, as the second of `(int, int) -> int`, so a call
/// that leaves it out names it by its place, and a repair's lambda binds a name the call does
/// not read: the message wrote "its parameter ``, and `` has no default", its repair "pass a
/// value for ``" and the lambda `() -> f(…, )`, and a `...` call "leaves out ``" (found by row
/// CHECK-fn-member-same-order-ambiguity).
#[test]
fn a_call_that_leaves_out_a_parameter_with_no_name_names_its_place() {
    let f = "(int, int) -> int";
    let missing = |at: &str| {
        format!(
            "this call of `{f}` gives no value to its second parameter, which has no default, \
             so the call cannot be made. [{at}]"
        )
    };
    let curried = format!(
        "this call of `{f}` ends in `...`, which makes a function of the named parameters the \
         call leaves out, and the call also leaves out its second parameter, a positional \
         parameter, which `...` cannot leave out. [k(x, ...)]"
    );
    let cases = [
        (
            "k(1)",
            missing("k(1)"),
            vec![
                "repair: pass a value for its second parameter in this call",
                "repair: make a function that takes its second parameter with a lambda, as `(x) -> f(…, x)`, where `f` is the function called here",
            ],
        ),
        (
            "k(x, ...)",
            curried,
            vec![
                "repair: remove the `...`",
                "repair: leave out its second parameter with a bracket section or a lambda, as `(x2) -> f(x, x2)`, where `f` is the function called here",
            ],
        ),
    ];
    for (call, want, repairs) in cases {
        let text = format!("{DECLS}app(k: {f}, x: int) = {call};\ny = app(k: add, x: 1);\n");
        assert_eq!(type_errors(&text), vec![want], "checker: {call}");
        let out = rejected_with_main(&text);
        for r in repairs {
            assert!(out.contains(r), "{call}: no `{r}` in:\n{out}");
        }
        assert!(!out.contains("``"), "{call}:\n{out}");
    }
}

#[test]
fn zedc_run_reports_a_misplaced_argument_once_with_the_declaration() {
    let program = |call: &str| {
        format!(
            "greet(name) = \"Hello, ${{name}}!\";\n\n\
             main(m: MainArgs) {{\n  m.stdout <- {call};\n}}\n"
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
    let message = "4:21: this argument is passed by position, and the parameter it reaches, `name` of `greet`, is a named parameter, which a call passes only by name, as `name: …`.\n";
    assert_eq!(bad.stderr.matches(message).count(), 1, "{}", bad.stderr);
    assert!(
        bad.stderr
            .contains("`greet` is declared here with no type written for `name` or its result; the type the checker found for `greet` is `(name: _) -> String`"),
        "{}",
        bad.stderr
    );
}

/// Item NUM-huge-div: a misplaced argument is the one error of an expression around the call.
/// The checker gives the rejected call no value, and an application that then refuses it,
/// directly, through an operation that passes the empty type on, or through a name defined as
/// the call, reports nothing more: it would print the call's type as `Never`, a type the
/// program never has. A call that fits still has its application refused, with its type.
#[test]
fn a_misplaced_argument_is_the_one_error_of_the_expressions_around_it() {
    let named = "this argument is passed by position, and the parameter it reaches, `x` of `dbl`, is a named parameter, which a call passes only by name, as `x: …`. [3]";
    for call in [
        "y = dbl(3) + \"a\";",
        "y = \"a\" + dbl(3);",
        "y = dbl(3) + 1.5f64 + \"a\";",
        "y = (dbl(3) + 1) * \"a\";",
        "z = dbl(3);\ny = z + \"a\";",
    ] {
        let text = format!("{DECLS}{call}\n");
        assert_eq!(type_errors(&text), vec![named.to_string()], "{call}");
    }
    let text = format!("{DECLS}y = add(1, 2) + \"a\";\n");
    let found = type_errors(&text);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].starts_with("`+` does not take (int, \"a\")"),
        "{found:?}"
    );
}

/// `n` misplaced arguments, each in an operation and in a name read once more.
pub(super) fn misplaced_arguments(n: usize) -> String {
    let mut text = DECLS.to_string();
    text.extend(
        (0..n).map(|i| {
            format!("y{i} = (dbl(3) + 1) * \"a\";\nz{i} = dbl(3);\nw{i} = z{i} + \"a\";\n")
        }),
    );
    text
}

#[test]
fn misplaced_arguments_in_operations_are_two_errors_each() {
    // A small instance of the benchmark
    // `bench::named_calls::many_misplaced_arguments_in_operations_check_in_linear_time`.
    assert_eq!(type_errors(&misplaced_arguments(3)).len(), 6);
}
