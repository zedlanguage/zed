//! Where a loose atom stops (DESIGN.md sec:failure, *Where a loose atom stops*; study
//! STUDY-atom-bubble-levels, zed ATOM-BUBBLE-STUDY.md): an atom passes up through the levels
//! of one expression, and at every other crossing it is held in a type the program can name,
//! from which the next expression starts. Each test here runs one crossing zedc compiles today
//! with no arguments, so that `m.args[0]` is `#outOfBounds`, beside a negative control that
//! drops the handling and is rejected where the atom meets a place that does not take it.
//!
//! What these tests cannot catch: crossings zedc does not compile yet (a binding with a
//! declared type, a declared result type, `loop`, `for`, struct and type declarations, struct
//! grammars), whose rules the rows that build those forms carry; and calls of functions with
//! undeclared parameters, whose atom choice CHK-index-else-bubble fixes (`args[0]` in such a
//! body gives `#notFound` today where the call passes a `CommandLine`).

use zed_tests::step_helpers::l01_19a_command_line::run;

/// Runs `src` with no arguments in a test directory of its own, `name`.
fn run0(name: &str, src: &str) -> (u8, String, String) {
    let out = run(&format!("boundaries_{name}"), src, &[]);
    (out.status, out.stdout, out.stderr)
}

/// Asserts that `src` is rejected with a message holding each of `words`.
fn rejected(name: &str, src: &str, words: &[&str]) {
    let (status, stdout, stderr) = run0(name, src);
    assert_eq!(status, 1, "{src}\nstdout: {stdout}\nstderr: {stderr}");
    assert_eq!(stdout, "", "{src}");
    for w in words {
        assert!(stderr.contains(w), "{src}\nmissing {w:?} in:\n{stderr}");
    }
}

/// Asserts that `src` runs to exit status 0 and prints `want`.
fn prints(name: &str, src: &str, want: &str) {
    let (status, stdout, stderr) = run0(name, src);
    assert_eq!(
        (status, stdout.as_str()),
        (0, want),
        "{src}\nstderr: {stderr}"
    );
}

/// The port message for a value `a` that may be `#outOfBounds`.
const AT_WRITE: &str = "A `Lines` port takes a `String` or a family of strings";

#[test]
fn a_top_level_constant_holds_the_atom_in_its_type() {
    // The constant crosses into `main` as a name whose type holds the atom.
    let src = "k = #outOfBounds;\nmain(m: MainArgs) {\n  m.stdout <- \"${k else 0}\";\n}\n";
    prints("const", src, "0\n");
    // Negative control: without the `else` the atom reaches the write.
    let bad = "k = #outOfBounds;\nmain(m: MainArgs) {\n  m.stdout <- \"${k}\";\n}\n";
    rejected("const_bad", bad, &[AT_WRITE, "String | #outOfBounds"]);
}

#[test]
fn a_lambda_result_holds_the_atom_and_the_call_gives_it() {
    let src = "main(m: MainArgs) {\n  f = (i) -> m.args[i];\n  \
        a = f(0) else #outOfBounds -> \"none\";\n  m.stdout <- a;\n}\n";
    prints("lambda", src, "none\n");
    let bad = "main(m: MainArgs) {\n  f = (i) -> m.args[i];\n  a = f(0);\n  m.stdout <- a;\n}\n";
    rejected(
        "lambda_bad",
        bad,
        &[AT_WRITE, "this call of `f` gives String | #outOfBounds"],
    );
}

#[test]
fn a_block_binding_and_final_expression_pass_the_atom_to_the_block() {
    let src = "main(m: MainArgs) {\n  a = { b = m.args[0]; b ++ \"!\" } else #outOfBounds -> \"none\";\n  \
        m.stdout <- a;\n}\n";
    prints("block", src, "none\n");
    let bad = "main(m: MainArgs) {\n  a = { b = m.args[0]; b ++ \"!\" };\n  m.stdout <- a;\n}\n";
    rejected(
        "block_bad",
        bad,
        &[
            AT_WRITE,
            "`b` is String | #outOfBounds here",
            "this block gives String | #outOfBounds",
        ],
    );
}

#[test]
fn safe_member_carries_a_loose_atom_as_member_does() {
    let src = "main(m: MainArgs) {\n  w = m.args[0]?.trim() else #outOfBounds -> \"none\";\n  \
        m.stdout <- w;\n}\n";
    prints("safe", src, "none\n");
    let bad = "main(m: MainArgs) {\n  w = m.args[0]?.trim();\n  m.stdout <- w;\n}\n";
    rejected(
        "safe_bad",
        bad,
        &[AT_WRITE, "`w` is String | #outOfBounds here"],
    );
}

#[test]
fn a_parameter_default_is_checked_against_the_written_parameter_type() {
    // The written type holds the atom: the call gives it, and the caller handles it.
    let src = "h(positional xs: [String], s: String | #outOfBounds = xs[0]) = s ++ \"!\";\n\
        main(m: MainArgs) {\n  m.stdout <- h(m.args) else \"none\";\n}\n";
    prints("default", src, "none\n");
    // Negative control: a written type that does not hold the atom is a type error at the
    // default, not a failure that appears at a call that omits the argument.
    let bad = "h(positional xs: [String], s: String = xs[0]) = s ++ \"!\";\n\
        main(m: MainArgs) {\n  m.stdout <- h(m.args) else \"none\";\n}\n";
    rejected(
        "default_bad",
        bad,
        &[
            "the default of `s` is String | #outOfBounds, not String",
            "as `s: String | #outOfBounds`",
        ],
    );
}

#[test]
fn underscore_drops_only_a_failure_the_text_names() {
    let src = "main(m: MainArgs) {\n  _ = m.args[0] else #ok;\n  m.stdout <- \"done\";\n}\n";
    prints("underscore", src, "done\n");
    let bad = "main(m: MainArgs) {\n  _ = m.args[0];\n  m.stdout <- \"done\";\n}\n";
    rejected(
        "underscore_bad",
        bad,
        &[
            "`_` drops a loose failure this value may be, #outOfBounds",
            "_ = … else #ok;",
        ],
    );
}

#[test]
fn a_call_statement_that_only_writes_is_legal_and_one_with_a_value_is_not() {
    // The statement's value is `()`; a failure of the unread write would pass out of the
    // block as an unread acknowledgment does (sec:ports).
    let src = "w(o: Lines) {\n  o <- \"x\";\n}\nmain(m: MainArgs) {\n  w(o: m.stderr);\n  \
        m.stdout <- \"done\";\n}\n";
    let (status, stdout, stderr) = run0("stmt", src);
    assert_eq!(
        (status, stdout.as_str(), stderr.as_str()),
        (0, "done\n", "x\n"),
        "{src}"
    );
    // Negative control: a statement whose value is not `()` drops a result, and is rejected.
    let bad = "w(positional xs, o: Lines) {\n  o <- \"x\";\n  xs[0]\n}\nmain(m: MainArgs) {\n  \
        w(m.args, o: m.stderr);\n  m.stdout <- \"done\";\n}\n";
    rejected(
        "stmt_bad",
        bad,
        &[
            "Result of `w` is unused",
            "_ = w(m.args, o: m.stderr) else #ok;",
        ],
    );
}
