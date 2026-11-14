//! Output ports passed to functions (DESIGN.md L1.19): "a function other than `main` takes a
//! port as an argument", `say(positional s, out: Lines) { out <- s; }` called as
//! `say("hi", out: m.stdout)`, "and the port's direction is the field's". Passing an output
//! port whole to a parameter the function pushes to is no read of the port; every other use of
//! an output port reads it and is rejected.

use zed_tests::deep::resolved;
use zedc::check::ports::ports;
use zedc::check::walk::check_text;
use zedc::resolve::tables::Tables;

use super::run;

/// The helper of the L1.19 example and a `main` that gives it `call`.
fn with_say(call: &str) -> String {
    format!("say(positional s, out: Lines) {{ out <- s; }}\n\nmain(m: MainArgs) {{\n  {call}\n}}\n")
}

/// The first line `zedc run` writes to standard error for `src`, which it rejects.
fn rejected(name: &str, src: &str) -> String {
    let out = run(name, src, "", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{}", out.stderr);
    let first = out.stderr.lines().next().unwrap_or_default();
    // Each message starts with the path of the program and the place.
    first
        .split_once(".zed:")
        .map_or(first, |(_, m)| m)
        .to_string()
}

/// Red before green: zedc rejected the example's call as a read of `m.stdout`, "`m.stdout` is
/// read here, and `m.stdout` is an output of the program".
#[test]
fn the_example_of_l1_19_writes_through_the_port_it_is_given() {
    let out = run("say", &with_say("_ = say(\"hi\", out: m.stdout);"), "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "hi\n", "")
    );
    let out = run(
        "say_err",
        &with_say("_ = say(\"oops\", out: m.stderr);"),
        "",
        &[],
    );
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "", "oops\n")
    );
}

/// The port reaches the push whatever the path: through a chain of helpers, by position, in
/// parentheses, from a lambda in the helper, beside a push of `main` to the other output.
#[test]
fn a_port_reaches_the_push_by_any_path() {
    let src = "say(positional s, out: Lines) { out <- s; }\n\
               shout(positional s, out: Lines) = say(s ++ \"!\", out: out);\n\
               main(m: MainArgs) {\n  _ = shout(\"hi\", out: m.stdout);\n}\n";
    assert_eq!(run("chain", src, "", &[]).stdout, "hi!\n");
    let src = "say(positional out: Lines, positional s) { out <- s; }\n\
               main(m: MainArgs) {\n  _ = say(m.stdout, \"pos\");\n}\n";
    assert_eq!(run("positional", src, "", &[]).stdout, "pos\n");
    let out = run(
        "group",
        &with_say("_ = say(\"g\", out: ((m.stdout)));"),
        "",
        &[],
    );
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "g\n"),
        "{}",
        out.stderr
    );
    let src = "say(positional s, out: Lines) {\n  g = x -> { out <- x; 0 };\n  g(s)\n}\n\
               main(m: MainArgs) {\n  _ = say(\"lam\", out: m.stdout);\n}\n";
    assert_eq!(run("lambda", src, "", &[]).stdout, "lam\n");
    let src = with_say("_ = say(\"a\", out: m.stderr);\n  m.stdout <- \"b\";");
    let out = run("both", &src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "b\n", "a\n")
    );
    // A helper that is never called is checked and costs nothing.
    let src = with_say("m.stdout <- \"b\";");
    assert_eq!(run("uncalled", &src, "", &[]).stdout, "b\n");
}

/// The contrast: a use of an output port other than as a whole argument of a parameter that
/// is pushed to reads the port, and is rejected as before.
#[test]
fn a_read_of_an_output_port_is_still_rejected() {
    let read = "`m.stdout` is read here, and `m.stdout` is an output of the program";
    for (name, call) in [
        ("index", "x = m.stdout[0] else \"\";\n  m.stderr <- x;"),
        ("bind", "x = m.stdout;\n  m.stderr <- \"z\";"),
        ("inside", "_ = say(m.stdout[0] else \"\", out: m.stderr);"),
    ] {
        let got = rejected(name, &with_say(call));
        assert!(got.contains(read), "{name}: {got}");
    }
    // Passed whole, but to a function that reads it, or to no declared function.
    let src = "count(positional s, out: Lines) = out[0] else \"\";\n\
               main(m: MainArgs) {\n  _ = count(\"x\", out: m.stdout);\n}\n";
    assert_eq!(
        rejected("reads", src),
        "3:23: `m.stdout` is an output port, pushed to and never read, and `count` reads `out`: \
         `count(\"x\", out: m.stdout)`."
    );
    let src = "main(m: MainArgs) {\n  n = len(m.stdout);\n  m.stderr <- \"x\";\n}\n";
    assert_eq!(
        rejected("prelude", src),
        "2:11: `m.stdout` is an output port, pushed to and never read, and it is read here: \
         `m.stdout`."
    );
    let src = "main(m: MainArgs) {\n  f = o -> 0;\n  n = f(m.stdout);\n  m.stderr <- \"x\";\n}\n";
    assert!(rejected("value", src).starts_with("3:9: `m.stdout` is an output port"));
    // A helper that pushes to its parameter and reads it.
    let src = "say(positional s, out: Lines) { out <- s; return out[0] else \"\"; }\n\
               main(m: MainArgs) {\n  _ = say(\"x\", out: m.stdout);\n}\n";
    assert_eq!(
        rejected("push_read", src),
        "1:50: `out` is an output port, pushed to and never read, and it is read here: `out`."
    );
}

/// What a parameter that is pushed to requires: an output port at every call, the declared
/// type `Lines`, no default, no test table, and calls by name only.
#[test]
fn a_parameter_pushed_to_takes_an_output_port_at_each_call() {
    assert_eq!(
        rejected("stdin", &with_say("_ = say(\"x\", out: m.stdin);")),
        "4:21: `say` pushes to `out`, so `out` takes an output port: `say(\"x\", out: m.stdin)`. \
         Try `say(\"x\", out: m.stdout)` instead."
    );
    let src = "say(positional s, out) { out <- s; }\n\
               main(m: MainArgs) {\n  _ = say(\"x\", out: m.stdout);\n}\n";
    let out = run("untyped", src, "", &[]);
    assert!(
        out.stderr.contains(
            "1:26: A push goes to an output port, and `out` is a parameter of `say` not declared \
             `Lines`: `out <- …;`. Try `out: Lines` instead."
        ),
        "{}",
        out.stderr
    );
    // The one error: the call is checked as a call of a function that pushes to `out`.
    assert_eq!(out.stderr.matches(".zed:").count(), 1, "{}", out.stderr);
    let src = "say(positional s, out: Lines = 1) { out <- s; }\n\
               main(m: MainArgs) {\n  _ = say(\"x\", out: m.stdout);\n}\n";
    assert_eq!(
        rejected("default", src),
        "1:32: An output port has no default: `out` of `say`, which it pushes to."
    );
    let src = "say(positional s, positional out: Lines) { out <- s; 0 } test { (\"a\", 1) -> 0 }\n\
               main(m: MainArgs) {\n  _ = say(\"x\", m.stdout);\n}\n";
    assert_eq!(
        rejected("table", src),
        "1:65: `say` pushes to its parameter `out`, and a test table gives a function values, \
         never a port."
    );
    let src = with_say("g = say;\n  m.stdout <- \"b\";");
    assert_eq!(
        rejected("function_value", &src),
        "4:7: `say` pushes to its parameter `out`, so it is called by name with the port it \
         writes to, and not used as a value: `say`."
    );
    // A value of the wrong type pushed through the parameter is rejected where it is pushed.
    let src = "say(positional s: int, out: Lines) { out <- s; }\n\
               main(m: MainArgs) {\n  _ = say(3, out: m.stdout);\n}\n";
    assert!(
        rejected("int", src).starts_with("1:45: A `Lines` port takes a `String`"),
        "{src}"
    );
}

/// A push to a name that is no output port is rejected when the program is checked; before,
/// `x <- "a";` with `x` a binding was accepted and failed when run, the run having no port `x`.
#[test]
fn a_push_to_a_name_that_is_no_port_is_rejected() {
    let src = "main(m: MainArgs) {\n  x = 1;\n  x <- \"a\";\n}\n";
    assert_eq!(
        rejected("binding", src),
        "3:3: A push goes to an output port, and `x` is a binding: `x <- …;`."
    );
}

/// The port is still pushed once per run: a helper's push and `main`'s to one port are two.
#[test]
fn a_port_given_to_a_helper_is_still_pushed_once() {
    let out = run(
        "twice",
        &with_say("_ = say(\"a\", out: m.stdout);\n  m.stdout <- \"b\";"),
        "",
        &[],
    );
    assert_eq!((out.status, out.stdout.as_str()), (1, ""));
    assert!(
        out.stderr
            .starts_with("`m.stdout` was pushed to 2 times in this run"),
        "{}",
        out.stderr
    );
}

/// A chain of `n` helpers, each passing its port to the next, the last pushing, and a `main`
/// that gives the last its `m.stdout`.
pub(super) fn helper_chain(n: usize) -> String {
    let mut text = String::from("h0(positional s, out: Lines) { out <- s; }\n");
    for i in 1..n {
        text.push_str(&format!(
            "h{i}(positional s, out: Lines) = h{}(s, out: out);\n",
            i - 1
        ));
    }
    text.push_str(&format!(
        "main(m: MainArgs) {{\n  _ = h{}(\"x\", out: m.stdout);\n}}\n",
        n - 1
    ));
    text
}

/// The output ports of a [`helper_chain`] of `n`: each parameter is an output port, decided
/// once, and none is an error.
pub(super) fn finds_the_ports(
    text: &str,
    stmts: &[zedc::ast::Stmt],
    res: &zedc::resolve::Resolution,
    n: usize,
) {
    let t = Tables::with_text(stmts, res, Some(text));
    let found = ports(&t);
    assert_eq!((found.params.len(), found.errors.len()), (n, 0));
}

/// A chain of helpers passing a port is accepted, each parameter is found an output port, and
/// the run writes once through the chain
/// (`bench::a_chain_of_helpers_passing_a_port_scales` at a small size).
#[test]
fn a_chain_of_helpers_passing_a_port_writes_once() {
    let text = helper_chain(3);
    let (stmts, res) = resolved(&text);
    let info = check_text(&stmts, &res, Some(&text));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    finds_the_ports(&text, &stmts, &res, 3);
    let out = run("helper_chain", &text, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "x\n"),
        "{}",
        out.stderr
    );
}
