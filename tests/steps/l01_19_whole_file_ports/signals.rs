//! `main(m: MainArgs) -> int with handles(#sigint)` (DESIGN.md sec:ports, "`main` may take over
//! SIGINT, SIGTERM and SIGHUP"; plan row SPEC-sigint-override): `m.signals` exists only under
//! the declaration, and a declaration that cannot hold is rejected. Taking a signal over at run
//! time is plan row SIGNALS-rt, so a declaration that holds is a form this zedc does not compile
//! yet.

use zed_tests::scaling::{check, inputs};
use zedc::ast::Error;
use zedc::rejection::Row;

use super::run;

/// The first error of building the syntax of `text`.
fn built(text: &str) -> Error {
    let tokens = zedc::lex::lex(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    zedc::ast::unit(text, &tokens, &tree).unwrap_err()
}

#[test]
fn signals_read_without_handles_is_rejected_with_the_header_that_declares_it() {
    for (name, src, headline) in [
        (
            "result",
            "main(m: MainArgs) -> int {\n  s = m.signals[0] == #sigint else false;\n  \
             m.stdout <- if s { \"stopping\" } else { \"\" };\n}\n",
            "2:7: `m.signals` is read, and `main` takes over no signal: \
             `main(m: MainArgs) -> int with handles(#sigint)`.\n",
        ),
        // No result written: the repair writes `-> int`, which the facet needs.
        (
            "no_result",
            "main(args: MainArgs) {\n  _ = args.signals[0];\n}\n",
            "2:7: `args.signals` is read, and `main` takes over no signal: \
             `main(args: MainArgs) -> int with handles(#sigint)`.\n",
        ),
    ] {
        let out = run(name, src, "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{name}");
        assert!(out.stderr.contains(headline), "{name}: {}", out.stderr);
        for part in [
            "repair: take SIGINT over with",
            "#sigterm",
            "repair: remove the read of",
        ] {
            assert!(out.stderr.contains(part), "{name}, {part}: {}", out.stderr);
        }
        assert_eq!(
            built(src).row,
            Some(Row::SignalsReadWithoutHandles),
            "{name}"
        );
    }
}

#[test]
fn a_signal_declaration_that_cannot_hold_is_rejected() {
    let read = "{\n  _ = m.signals[0];\n}\n";
    for (name, facet, headline) in [
        (
            "sigkill",
            "handles(#sigint, #sigkill)",
            "1:48: `#sigkill` cannot be taken over: SIGKILL cannot be caught. \
             `with handles(#sigint)`.\n",
        ),
        (
            "sigstop",
            "handles(#sigstop)",
            "1:39: `#sigstop` cannot be taken over: SIGSTOP cannot be caught.",
        ),
        (
            "other_atom",
            "handles(#sigusr1)",
            "1:39: `#sigusr1` cannot be taken over: it is not a signal `handles` takes.",
        ),
        (
            "named",
            "handles(signal: #sigint)",
            "1:39: `signal: #sigint` cannot be taken over:",
        ),
        (
            "repeat",
            "handles(#sigint, #sigterm, #sigint)",
            "1:58: `#sigint` is named twice: `with handles(#sigint, #sigterm)`.\n",
        ),
        // Every argument is checked before any repeat is looked for.
        (
            "repeat_then_sigkill",
            "handles(#sigint, #sigint, #sigkill)",
            "1:57: `#sigkill` cannot be taken over: SIGKILL cannot be caught.",
        ),
        (
            "empty",
            "handles()",
            "1:26: `handles()` names no signal: `with handles(#sigint)`.\n",
        ),
        (
            "two_facets",
            "handles(#sigint) with handles(#sigterm)",
            "1:48: `handles` is written twice: `with handles(#sigint, #sigterm)`.\n",
        ),
    ] {
        let src = format!("main(m: MainArgs) -> int with {facet} {read}");
        let out = run(name, &src, "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{name}");
        assert!(out.stderr.contains(headline), "{name}: {}", out.stderr);
        assert_eq!(
            built(&src).row,
            Some(Row::SignalDeclarationCannotHold),
            "{name}"
        );
    }
}

#[test]
fn a_main_that_takes_signals_over_and_never_reads_them_is_rejected() {
    let src = "main(m: MainArgs) -> int with handles(#sigint, #sighup) {\n  0\n}\n";
    let out = run("never_read", src, "", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (1, ""));
    assert!(
        out.stderr.contains(
            "1:26: `main` takes over SIGINT and SIGHUP and never reads `m.signals`: \
             `main(m: MainArgs) -> int`.\n"
        ),
        "{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("take two to stop the run"),
        "{}",
        out.stderr
    );
    assert_eq!(built(src).row, Some(Row::SignalDeclarationCannotHold));
}

#[test]
fn a_declaration_that_holds_is_not_compiled_yet() {
    for (name, facet) in [
        ("sigint", "handles(#sigint)"),
        ("all", "handles(#sigint, #sigterm, #sighup)"),
    ] {
        let src = format!(
            "main(m: MainArgs) -> int with {facet} {{\n  \
             stopped = m.signals[0] == #sigint else false;\n  \
             m.stdout <- if stopped {{ \"stopping\" }} else {{ \"\" }};\n}}\n"
        );
        let out = run(name, &src, "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{name}");
        assert!(
            out.stderr.contains(&format!(
                "1:26: the facet `with {facet}` is part of the Zed language, and this version \
                 of zedc does not compile it yet."
            )),
            "{name}: {}",
            out.stderr
        );
        assert!(
            !out.stderr.contains("that is not an `int`"),
            "{name}: {}",
            out.stderr
        );
    }
}

#[test]
fn handles_with_another_facet_or_another_result_is_a_result_main_may_not_have() {
    for (name, result) in [
        ("other_facet", "int with handles(#sigint) with bound(3)"),
        ("string", "String with handles(#sigint)"),
    ] {
        let src = format!("main(m: MainArgs) -> {result} {{\n  _ = m.signals[0];\n}}\n");
        let out = run(name, &src, "", &[]);
        assert_eq!(out.status, 1, "{name}");
        assert!(
            out.stderr.contains(&format!(
                "1:22: Result of `main` that is not an `int`: `{result}`. Try `int` instead.\n"
            )),
            "{name}: {}",
            out.stderr
        );
    }
}

/// `main` with `handles(#sigint, #sigterm, #sighup)` and then `n` more arguments, each a repeat:
/// the repair lists the arguments once each.
fn repeats(n: usize) -> String {
    let more = ", #sigint".repeat(n);
    format!(
        "main(m: MainArgs) -> int with handles(#sigint, #sigterm, #sighup{more}) {{\n  \
         _ = m.signals[0];\n}}\n"
    )
}

#[test]
fn a_handles_with_n_repeated_arguments_is_rejected_in_linear_time() {
    let srcs = inputs(3000, repeats);
    check("rejecting handles with n repeated arguments", 3000, |n| {
        let error = built(&srcs[&n]);
        assert!(
            error
                .message
                .ends_with("`with handles(#sigint, #sigterm, #sighup)`."),
            "{}",
            error.message
        );
    });
}

/// `main` without `handles` that reads `m.signals` `n` times.
fn reads(n: usize) -> String {
    let mut src = String::from("main(m: MainArgs) {\n");
    for i in 0..n {
        src.push_str(&format!("  s{i} = m.signals[{i}];\n"));
    }
    src.push_str("}\n");
    src
}

#[test]
fn n_reads_of_signals_without_handles_are_rejected_in_linear_time() {
    let srcs = inputs(3000, reads);
    check(
        "rejecting n reads of m.signals without handles",
        3000,
        |n| {
            assert_eq!(built(&srcs[&n]).row, Some(Row::SignalsReadWithoutHandles));
        },
    );
}

#[test]
fn handles_on_a_function_other_than_main_is_rejected() {
    for (name, header, repaired) in [
        (
            "equation",
            "serve(x: int) -> int with handles(#sigint) = x;",
            "serve(x: int) -> int",
        ),
        // A facet after `handles` stays in the repair.
        (
            "facet_after",
            "serve(x: int) -> int with handles(#sigint) with bound(3) = x;",
            "serve(x: int) -> int with bound(3)",
        ),
    ] {
        let src = format!("{header}\nmain(m: MainArgs) {{\n  m.stdout <- String(serve(1));\n}}\n");
        let error = built(&src);
        assert_eq!(error.row, Some(Row::SignalDeclarationCannotHold), "{name}");
        assert_eq!(
            error.message,
            format!("`handles` on `serve`, which is not `main`: `{repaired}`."),
            "{name}"
        );
        assert_eq!(
            &src[error.span.start..error.span.end],
            "with handles(#sigint)",
            "{name}"
        );
    }
}
