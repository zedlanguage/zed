//! `main(m: MainArgs) -> int` (DESIGN.md sec:ports, QUESTIONS Q51): the header `main` may
//! have, the exit status its result gives, and the direction each field of `MainArgs` has.

use zedc::run::load;

use super::run;

#[test]
fn the_result_of_main_is_the_exit_status() {
    let src = "main(m: MainArgs) -> int {\n  m.stdout <- \"x\";\n  3\n}\n";
    let out = run("status3", src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (3, "x\n", "")
    );
    // The status may depend on the input; `-> int` may be left out.
    let src = "main(m: MainArgs) {\n  m.stdout <- \"x\";\n  \
               if (m.stdin[0] else \"\") == \"fail\" { 7 } else { 0 }\n}\n";
    let out = run("status_if", src, "fail\n", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (7, "x\n"));
    let out = run("status_if", src, "ok\n", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "x\n"));
    // 255 is the largest status.
    let src = "main(m: MainArgs) -> int {\n  255\n}\n";
    assert_eq!(run("status255", src, "", &[]).status, 255);
}

#[test]
fn a_body_that_exports_nothing_exits_with_0() {
    for (name, src) in [
        ("plain", "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n"),
        (
            "declared",
            "main(m: MainArgs) -> int {\n  m.stdout <- \"x\";\n}\n",
        ),
        ("untyped", "main(m) {\n  m.stdout <- \"x\";\n}\n"),
    ] {
        let out = run(name, src, "", &[]);
        assert_eq!(
            (out.status, out.stdout.as_str(), out.stderr.as_str()),
            (0, "x\n", ""),
            "{name}"
        );
    }
    // With no parameter there is nothing to read or write, and the program exits with 0.
    let out = run("none", "main() {\n}\n", "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "", "")
    );
}

#[test]
fn a_failure_that_bubbles_out_of_main_exits_with_1_and_writes_nothing() {
    let src = "main(m: MainArgs) -> int {\n  m.stdout <- \"x\";\n  \
               int(m.stdin[0] else \"\") mod 256\n}\n";
    let out = run("bubble", src, "4\n", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (4, "x\n"),
        "{}",
        out.stderr
    );
    let out = run("bubble", src, "four\n", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{}", out.stderr);
}

#[test]
fn a_status_not_proved_to_be_a_byte_is_rejected_with_the_menu() {
    for (name, result) in [("256", "256"), ("minus", "-1")] {
        let src = format!("main(m: MainArgs) -> int {{\n  {result}\n}}\n");
        let out = run(name, &src, "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{name}");
        assert!(
            out.stderr.contains(
                "the result of `main` is the program's exit status, a number from 0 to 255"
            ),
            "{name}: {}",
            out.stderr
        );
    }
    let read = "int(m.stdin[0] else \"\") else 1";
    let src = format!("main(m: MainArgs) -> int {{\n  {read}\n}}\n");
    let out = run("unbounded", &src, "", &[]);
    assert_eq!(out.status, 1);
    for repair in [
        "code = int(m.stdin[0] else \"\"); if code < 0 { 0 } else if code > 255 { 255 } else { code }",
        "(int(m.stdin[0] else \"\")) mod 256",
        "code = int(m.stdin[0] else \"\"); if code >= 0 && code <= 255 { code } else { 1 }",
    ] {
        assert!(out.stderr.contains(repair), "{repair}: {}", out.stderr);
    }
    // Each repair of the menu is accepted.
    for (name, repair) in [
        (
            "clamp",
            "if code < 0 { 0 } else if code > 255 { 255 } else { code }",
        ),
        ("mod", "code mod 256"),
        ("if", "if code >= 0 && code <= 255 { code } else { 1 }"),
    ] {
        let src = format!("main(m: MainArgs) -> int {{\n  code = {read};\n  {repair}\n}}\n");
        let out = run(name, &src, "300\n", &[]);
        let want = match name {
            "clamp" => 255,
            "mod" => 44,
            _ => 1,
        };
        assert_eq!(out.status, want, "{name}: {}", out.stderr);
    }
}

#[test]
fn a_header_main_may_not_have_is_rejected() {
    for (name, src, part) in [
        (
            "second",
            "main(m: MainArgs, n: int) {\n}\n",
            "1:19: Second parameter of `main`: `n: int`. Try `main(m: MainArgs)` instead.\n",
        ),
        (
            "string",
            "main(m: MainArgs) -> String {\n  \"x\"\n}\n",
            "1:22: Result of `main` that is not an `int`: `String`. Try `int` instead.\n",
        ),
        (
            "lines",
            "main(m: MainArgs) -> Lines {\n  m.stdin\n}\n",
            "1:22: Result of `main` that is not an `int`: `Lines`. Try `int` instead.\n",
        ),
        (
            "default",
            "main(m: MainArgs = 1) {\n}\n",
            "1:6: Default value on the parameter of `main`: `m: MainArgs = 1`. Try \
             `main(m: MainArgs)` instead.\n",
        ),
        (
            "elsewhere",
            "f(a: MainArgs) = 1;\nmain(m: MainArgs) {\n}\n",
            "1:6: `MainArgs` is the type of the argument of `main` only.\n",
        ),
    ] {
        let out = run(name, src, "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{name}");
        assert!(out.stderr.contains(part), "{name}: {}", out.stderr);
    }
    let out = run("int_param", "main(n: int) {\n}\n", "", &[]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr
            .contains(&zed_tests::main_param_message("n", "int")),
        "{}",
        out.stderr
    );
}

#[test]
fn a_field_is_used_only_in_its_direction() {
    let out = run(
        "push_stdin",
        "main(m: MainArgs) {\n  m.stdin <- \"x\";\n}\n",
        "",
        &[],
    );
    assert_eq!((out.status, out.stdout.as_str()), (1, ""));
    assert!(out.stderr.contains("m.stdin"), "{}", out.stderr);
    let out = run(
        "read_stdout",
        "main(m: MainArgs) {\n  m.stderr <- m.stdout[1] else \"\";\n}\n",
        "",
        &[],
    );
    assert_eq!((out.status, out.stdout.as_str()), (1, ""));
    // The builder rejects the read before the checker runs, so no derivation of the checker
    // names an output port.
    assert!(
        out.stderr.contains(
            "2:15: `m.stdout` is read here, and `m.stdout` is an output of the program: `main` \
             writes lines to it with a push, as `m.stdout <- lines;`, and never reads it."
        ),
        "{}",
        out.stderr
    );
}

/// `main` whose result is an `if` chain of `n` branches, each giving a status from 0 to 255.
pub(super) fn chain(n: usize) -> String {
    let mut src =
        String::from("main(m: MainArgs) -> int {\n  x = int(m.stdin[0] else \"\") else 0;\n  ");
    for i in 0..n {
        src.push_str(&format!("if x == {i} {{ {} }} else ", i % 256));
    }
    src.push_str("{ 0 }\n}\n");
    src
}

/// Loads a [`chain`]: its status is proved a byte, and it reads `m.stdin`.
pub(super) fn loads_the_chain(src: &str) {
    let program = load(src.as_bytes()).unwrap();
    assert!(program.inputs().iter().any(|(p, _)| p == "m.stdin"));
}

/// An `if` chain whose every branch gives a byte is a status, and the chain runs
/// (`bench::the_status_of_a_long_if_chain_is_checked_in_linear_time` at a small size).
#[test]
fn the_status_of_an_if_chain_is_checked_and_given() {
    let src = chain(3);
    loads_the_chain(&src);
    assert_eq!(run("status_chain", &src, "2\n", &[]).status, 2);
    assert_eq!(run("status_chain", &src, "9\n", &[]).status, 0);
}

/// `n` `main`s, each reading `m.stdin`, then `n` functions that each read a field of their
/// parameter: the builder asks of each read whether a `main`'s body holds it.
pub(super) fn mains_then_reads(n: usize) -> String {
    let mut src = "main(m: MainArgs) {\n  m.stdout <- m.stdin[0] else \"\";\n}\n".repeat(n);
    for i in 0..n {
        src.push_str(&format!("f{i}(positional p) = p.x;\n"));
    }
    src
}

/// Builds the syntax tree of [`mains_then_reads`] of `n`: `2n` statements. The resolver
/// rejects the second `main`; the syntax tree is built before it.
pub(super) fn builds_the_reads(text: &str, n: usize) {
    let tokens = zedc::lex::lex(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    assert_eq!(stmts.len(), 2 * n);
}

/// `bench::building_the_reads_after_n_mains_is_linear` at a small size.
#[test]
fn the_reads_after_several_mains_are_built() {
    builds_the_reads(&mains_then_reads(3), 3);
}
