//! A call of a prelude word with the wrong number of arguments, or with an argument of a type
//! the word does not take, pinned through `zedc run` (row MSG-prelude-word-args). The message
//! names the word and its parameters as DESIGN.md writes them, `sqrt(x)` and `fma(a, b, c)`,
//! not the parameters `x0`, `x1` of its signature, and gives the call rewritten where one
//! rewriting repairs it. Each rejected call has a contrast that runs.

use zed_tests::step_helpers::l01_19a_command_line::{dir, run};

/// `main`, printing `f(arg)` as a line.
fn program(f: &str, arg: &str) -> String {
    format!("{f}\nmain(m: MainArgs) {{\n  m.stdout <- \"${{f({arg})}}\";\n}}\n")
}

/// The exit status, standard output and standard error of `zedc run` on the program `f` with
/// `main` printing `f(arg)`, the program's path removed from standard error.
fn zedc_run(name: &str, f: &str, arg: &str) -> (u8, String, String) {
    let out = run(name, &program(f, arg), &[]);
    let path = dir(name).join("prog.zed");
    let err = out.stderr.replace(&format!("{}:", path.display()), "");
    (out.status, out.stdout, err)
}

/// Asserts `zedc run` rejects the program with `stderr` and runs its contrast to `stdout`.
fn rejected_and_contrast(name: &str, (bad, stderr): (&str, &str), (good, stdout): (&str, &str)) {
    let (status, out, err) = zedc_run(name, bad, "2.0");
    assert_eq!((out.as_str(), err.as_str()), ("", stderr), "{bad}");
    assert_ne!(status, 0, "{bad}");
    let ok = zedc_run(&format!("{name}-ok"), good, "2.0");
    assert_eq!(ok, (0, format!("{stdout}\n"), String::new()), "{good}");
}

#[test]
fn too_many_arguments_name_the_word_and_rewrite_the_call() {
    rejected_and_contrast(
        "sqrt-two",
        (
            "f(positional x: f64) = sqrt(x, 2.0);",
            "1:24: `sqrt` takes one argument, `sqrt(x)`, and `sqrt(x, 2.0)` passes 2. Try `sqrt(x)` instead.
  [1] 1:24: repair: `sqrt(x)`
      1 | f(positional x: f64) = sqrt(x, 2.0);
        |                        ^^^^^^^^^^^^
",
        ),
        ("f(positional x: f64) = sqrt(x);", "1.4142135623730951"),
    );
}

#[test]
fn too_few_arguments_name_the_parameters_given_no_value() {
    rejected_and_contrast(
        "fma-two",
        (
            "f(positional x: f64) = fma(x, x);",
            "1:24: `fma` takes 3 arguments, `fma(a, b, c)`, and `fma(x, x)` passes 2.
  [1] 1:24: repair: give `c` a value, as `fma(x, x, c)`
      1 | f(positional x: f64) = fma(x, x);
        |                        ^^^^^^^^^
",
        ),
        ("f(positional x: f64) = fma(x, x, x);", "6.0"),
    );
    // No argument at all names every parameter.
    rejected_and_contrast(
        "fma-none",
        (
            "f(positional x: f64) = fma();",
            "1:24: `fma` takes 3 arguments, `fma(a, b, c)`, and `fma()` passes 0.
  [1] 1:24: repair: give `a`, `b` and `c` a value, as `fma(a, b, c)`
      1 | f(positional x: f64) = fma();
        |                        ^^^^^
",
        ),
        ("f(positional x: f64) = fma(x, 1.0, x);", "4.0"),
    );
}

#[test]
fn the_value_before_the_dot_is_counted_as_the_first_argument() {
    rejected_and_contrast(
        "sqrt-method",
        (
            "f(positional x: f64) = x.sqrt(2.0);",
            "1:24: `sqrt` takes one argument, `sqrt(x)`, and `x.sqrt(2.0)` passes 2. Try `sqrt(x)` instead.
  [1] 1:24: `x` before `.sqrt` is the first argument of `sqrt`
      1 | f(positional x: f64) = x.sqrt(2.0);
        |                        ^^^^^^^^^^^
  [2] 1:24: repair: `sqrt(x)`
",
        ),
        ("f(positional x: f64) = x.sqrt();", "1.4142135623730951"),
    );
    rejected_and_contrast(
        "fma-method",
        (
            "f(positional x: f64) = x.fma(x);",
            "1:24: `fma` takes 3 arguments, `fma(a, b, c)`, and `x.fma(x)` passes 2.
  [1] 1:24: `x` before `.fma` is the first argument of `fma`
      1 | f(positional x: f64) = x.fma(x);
        |                        ^^^^^^^^
  [2] 1:24: repair: give `c` a value, as `fma(x, x, c)`
",
        ),
        ("f(positional x: f64) = x.fma(x, x);", "6.0"),
    );
}

#[test]
fn named_arguments_and_the_rest_are_reported_by_elaboration() {
    // A prelude word has no parameter names a call could give, whatever the count.
    let named = "f(positional x: f64) = min(x, x1: 2.0);";
    let (status, out, err) = zedc_run("min-named", named, "2.0");
    assert_ne!(status, 0);
    assert_eq!(
        (out.as_str(), err.as_str()),
        (
            "",
            "1:24: named arguments and `...` need the parameter names of the function called, \
             which a prelude word and a value of unknown type do not give.\n"
        ),
        "{named}"
    );
}

#[test]
fn an_int_argument_is_rewritten_with_its_cast_where_the_cast_is_exact() {
    // Bounded within 2^53, `f64(n)` is exact: the headline gives the call rewritten.
    let bounded = "f(positional n: int) = if n >= 0 && n <= 100 { sqrt(n) } else { 0.0 };";
    let (status, out, err) = zedc_run("sqrt-int-bounded", bounded, "4");
    assert_ne!(status, 0);
    assert_eq!(
        (out.as_str(), err.as_str()),
        (
            "",
            "1:48: `sqrt` does not take (int): no arrow of `sqrt` takes these types. Try `sqrt(f64(n))` instead.
  [1] 1:53: `n` is int here
      1 | f(positional n: int) = if n >= 0 && n <= 100 { sqrt(n) } else { 0.0 };
        |   ^^^^^^^^^^^^^^^^^ [2]                        ^^^^^^^ [3, 4]
        |                                                     ^ [1, 5]
  [2] 1:3: `n` is declared `int`
  [3] 1:48: `sqrt` takes (f64) -> f64
  [4] 1:48: `sqrt` takes (f32) -> f32
  [5] 1:53: repair: write `f64(n)`; the checker accepts that
"
        ),
        "{bounded}"
    );
    let good = "f(positional n: int) = if n >= 0 && n <= 100 { sqrt(f64(n)) } else { 0.0 };";
    assert_eq!(
        zedc_run("sqrt-int-cast", good, "4"),
        (0, "2.0\n".into(), String::new())
    );
    // Unbounded, `f64(n)` would round: no cast is offered (DESIGN.md sec:diagnostics, a
    // repair never narrows), and the repair is to change the type of `n`.
    let unbounded = "f(positional n: int) = sqrt(n);";
    let (status, out, err) = zedc_run("sqrt-int", unbounded, "4");
    assert_ne!(status, 0);
    assert_eq!(
        (out.as_str(), err.as_str()),
        (
            "",
            "1:24: `sqrt` does not take (int): no arrow of `sqrt` takes these types.
  [1] 1:29: `n` is int here
      1 | f(positional n: int) = sqrt(n);
        |   ^^^^^^^^^^^^^^^^^ [2]     ^ [1, 5]
        |                        ^^^^^^^ [3, 4]
  [2] 1:3: `n` is declared `int`
  [3] 1:24: `sqrt` takes (f64) -> f64
  [4] 1:24: `sqrt` takes (f32) -> f32
  [5] 1:29: repair: change the type of `n` so that `sqrt` takes it
"
        ),
        "{unbounded}"
    );
    // A rat is never offered `f64(r)`, which rounds.
    let rat = "f(positional r: rat) = sqrt(r);";
    let (_, _, err) = zedc_run("sqrt-rat", rat, "4");
    assert!(!err.contains("Try"), "{err}");
    assert!(
        err.contains("repair: change the type of `r` so that `sqrt` takes it"),
        "{err}"
    );
}

/// `x = min(0, 1, …, n - 1);`, a call of `min` with `n` arguments.
pub(crate) fn min_of_n_arguments(n: usize) -> String {
    let args: Vec<String> = (0..n).map(|i| i.to_string()).collect();
    format!("x = min({});\n", args.join(", "))
}

#[test]
fn a_call_of_min_with_three_arguments_is_rejected() {
    // The input of `bench::word_args` at a small size. The file has no `main`, which is
    // reported only once the call is accepted.
    assert_eq!(
        zedc::run::load(min_of_n_arguments(3).as_bytes()).err(),
        Some(
            "1:5: `min` takes 2 arguments, `min(a, b)`, and `min(0, 1, 2)` passes 3. Try `min(0, 1)` instead.
  [1] 1:5: repair: `min(0, 1)`
      1 | x = min(0, 1, 2);
        |     ^^^^^^^^^^^^"
                .to_string()
        )
    );
    let two = zedc::run::load(min_of_n_arguments(2).as_bytes())
        .err()
        .unwrap();
    assert!(
        two.starts_with("1:1: This file declares no `main`"),
        "{two}"
    );
}
