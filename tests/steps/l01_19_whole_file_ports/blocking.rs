//! Which functions can block (DESIGN.md sec:ports, "Every port operation says whether it can
//! block"; QUESTIONS A68): a read of `m.stdin` or `main::files` and a push to an output port can;
//! a read of `m.args` or `m.env` cannot; a function can when any path of calls from it reaches
//! one, or calls a function value whose body the checker cannot see.

use std::collections::BTreeMap;

use zed_tests::deep::resolved;
use zedc::check::blocking::{Cause, explain, facts};
use zedc::check::walk::check_text;
use zedc::resolve::tables::Tables;

/// Each function of `text` that can block, by name, with why, as an editor shows it; the
/// program checks with no error.
fn blocking(text: &str) -> BTreeMap<String, String> {
    blocking_with(text, true)
}

/// [`blocking`], with the program checked with no error when `clean`: the fact is computed
/// for a program the checker rejects all the same, as an editor shows it while one is written.
fn blocking_with(text: &str, clean: bool) -> BTreeMap<String, String> {
    let (stmts, res) = resolved(text);
    let info = check_text(&stmts, &res, Some(text));
    assert!(
        !clean || info.errors.is_empty(),
        "{text}: {:?}",
        info.errors
    );
    (info.blocking.keys())
        .map(|&f| {
            let why = explain(&info.blocking, &res, Some(text), f).expect("a blocking function");
            (res.binders[f].name.clone(), why)
        })
        .collect()
}

/// The names of the functions of `text` that can block.
fn names(text: &str) -> Vec<String> {
    blocking(text).into_keys().collect()
}

#[test]
fn reading_standard_input_blocks_and_args_and_env_do_not() {
    let text = "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n";
    assert_eq!(
        blocking(text)["main"],
        "`main` can block: it pushes to `m.stdout`, which can wait while its reader does not read."
    );
    let text = "main(m: MainArgs) {\n  x = m.stdin[0] else \"\";\n  m.stdout <- x;\n}\n";
    assert_eq!(
        blocking(text)["main"],
        "`main` can block: it reads `m.stdin`, which can wait for its data."
    );
    for read in [
        "(m.args[0] else \"\") == \"a\"",
        "(m.env[\"N\"] else \"\") == \"a\"",
    ] {
        let text = format!("main(m: MainArgs) -> int {{\n  if {read} {{ 1 }} else {{ 0 }}\n}}\n");
        assert_eq!(names(&text), Vec::<String>::new(), "{text}");
    }
}

#[test]
fn reading_files_blocks() {
    let text = "main(m: MainArgs) {\n  fs = main::files;\n  x = fs[\"a.txt\"] else \"\";\n  \
                m.stdout <- x;\n}\n";
    assert_eq!(
        blocking(text)["main"],
        "`main` can block: it reads `fs`, which holds `main::files`, which can wait for its data."
    );
}

/// A function other than `main` reads the file port as `main::files` (QUESTIONS A68), written
/// before `main` or after it, directly or through a name bound to it, and blocks; so do the
/// functions that call it. A helper that only passes the port on reads nothing itself.
#[test]
fn reading_main_files_outside_main_blocks() {
    let text = "size(positional p) = main::files[p] else \"\";\n\
                held(positional p) = {\n  fs = main::files;\n  fs[p] else \"\"\n};\n\
                port() = main::files;\n\
                pure(positional x: int) = x + 1;\n\
                main(m: MainArgs) -> int {\n  if size(\"a\") == later(\"b\") && pure(1) == 2 { 1 } else { 0 }\n}\n\
                later(positional p) = main::files[p] else \"\";\n";
    let got = blocking(text);
    assert_eq!(
        got.keys().collect::<Vec<_>>(),
        ["held", "later", "main", "size"]
    );
    assert_eq!(
        got["size"],
        "`size` can block: it reads `main::files`, which can wait for its data."
    );
    assert_eq!(
        got["later"],
        "`later` can block: it reads `main::files`, which can wait for its data."
    );
    assert_eq!(
        got["held"],
        "`held` can block: it reads `fs`, which holds `main::files`, which can wait for its data."
    );
    assert_eq!(
        got["main"],
        "`main` can block: it calls `size`, which reads `main::files`, which can wait for its \
         data."
    );
}

/// A port passed on whole is read where it is indexed: the helper reads; `main` calls it.
#[test]
fn a_port_passed_to_a_helper_is_read_there() {
    let text = "first(positional xs) = xs[0] else \"\";\n\
                pass(positional xs) = first(xs);\n\
                pure(positional xs) = xs;\n\
                main(m: MainArgs) -> int {\n  if pass(m.stdin) == \"a\" { 1 } else { 0 }\n}\n";
    let got = blocking(text);
    assert_eq!(
        got["first"],
        "`first` can block: it reads `xs`, which holds `m.stdin`, which can wait for its data."
    );
    assert_eq!(
        got["pass"],
        "`pass` can block: it calls `first`, which reads `xs`, which holds `m.stdin`, which can \
         wait for its data."
    );
    assert_eq!(
        got["main"],
        "`main` can block: it calls `pass`, which calls `first`, which reads `xs`, which holds \
         `m.stdin`, which can wait for its data."
    );
    // `pure` returns what it is given and reads nothing; it is never given a port here.
    assert!(!got.contains_key("pure"), "{got:?}");
}

/// Blocking passes up a chain of calls, each function to its caller; a function off the chain
/// and one that only computes stay nonblocking.
#[test]
fn blocking_passes_up_a_chain_of_calls() {
    let text = "c(positional f) = f(1);\n\
                b(positional f) = c(f);\n\
                a(positional f) = b(f);\n\
                d(positional x: int) = x + 1;\n\
                e(positional x: int) = d(d(x));\n";
    let got = blocking(text);
    assert_eq!(names(text), ["a", "b", "c"]);
    assert_eq!(
        got["a"],
        "`a` can block: it calls `b`, which calls `c`, which calls `f`, a function value whose \
         body is not known where it is called, so the call may block."
    );
}

/// A cycle of calls ends: blocking reaches every function of a cycle one of them enters, and
/// a cycle that reaches no blocking operation stays nonblocking. This zedc refuses recursion
/// through two functions (until the step that compiles it), and decides the fact all the same.
#[test]
fn blocking_passes_around_a_cycle() {
    let text = "p(positional f, positional k: int) = if k <= 0 { f(k) } else { q(f, k - 1) };\n\
                q(positional f, positional k: int) = p(f, k - 1);\n\
                r(positional f) = q(f, 3);\n\
                u(positional k: int) = if k <= 0 { 0 } else { v(k - 1) };\n\
                v(positional k: int) = u(k - 1);\n";
    let got = blocking_with(text, false);
    assert_eq!(got.keys().collect::<Vec<_>>(), ["p", "q", "r"]);
    assert_eq!(
        got["r"],
        "`r` can block: it calls `q`, which calls `p`, which calls `f`, a function value whose \
         body is not known where it is called, so the call may block."
    );
}

/// A lambda's body belongs to the function that writes it; a call of a lambda or of a declared
/// function is a call of a body the checker sees.
#[test]
fn lambdas_and_declared_functions_are_seen() {
    let text = "inc(positional x: int) = x + 1;\n\
                twice(positional x: int) = {\n  g = inc;\n  h = (positional y: int) -> y * 2;\n  \
                g(h(x))\n};\n\
                main(m: MainArgs) {\n  k = (positional s) -> m.stdin[0] else s;\n  \
                m.stdout <- k(\"${twice(1)}\");\n}\n";
    assert_eq!(names(text), ["main"]);
    assert_eq!(
        blocking(text)["main"],
        "`main` can block: it reads `m.stdin`, which can wait for its data."
    );
}

/// The facts as the checker records them: the cause of each blocking function, and none for a
/// pure one.
#[test]
fn the_causes_are_recorded_by_binder() {
    let text = "c(positional f) = f(1);\nb(positional f) = c(f);\nd(positional x: int) = x;\n";
    let (stmts, res) = resolved(text);
    let t = Tables::with_text(&stmts, &res, Some(text));
    let got = facts(&t, &stmts);
    let id = |n: &str| {
        (res.binders.iter())
            .position(|b| b.name == n)
            .expect("bound")
    };
    assert!(matches!(got[&id("c")], Cause::CallsValue { .. }));
    assert_eq!(
        got[&id("b")],
        Cause::Calls {
            callee: id("c"),
            at: got[&id("b")].at()
        }
    );
    assert!(!got.contains_key(&id("d")));
}

/// A chain of `n` functions, each calling the next, the last calling a function value.
pub(super) fn call_chain(n: usize) -> String {
    let mut text = String::from("c0(positional f) = f(1);\n");
    for i in 1..n {
        text.push_str(&format!("c{i}(positional f) = c{}(f);\n", i - 1));
    }
    text
}

/// Decides which functions of a [`call_chain`] of `n` can block: all `n`, by one search
/// backward over the calls, each function visited once.
pub(super) fn decides_the_chain(
    text: &str,
    stmts: &[zedc::ast::Stmt],
    res: &zedc::resolve::Resolution,
    n: usize,
) {
    let t = Tables::with_text(stmts, res, Some(text));
    assert_eq!(facts(&t, stmts).len(), n);
}

/// Every function of a chain of calls ending in a call of a function value can block
/// (`bench::a_long_chain_of_calls_is_decided_in_linear_time` at a small size).
#[test]
fn every_function_of_a_chain_of_calls_blocks() {
    let text = call_chain(3);
    let (stmts, res) = resolved(&text);
    decides_the_chain(&text, &stmts, &res, 3);
}

/// The helper of the L1.19 example blocks, since a push can wait while its reader does not
/// read, and so does `main`, which calls it.
#[test]
fn a_helper_that_pushes_to_its_port_blocks() {
    let text = "say(positional s, out: Lines) { out <- s; }\n\
                main(m: MainArgs) {\n  _ = say(\"hi\", out: m.stdout);\n}\n";
    let got = blocking(text);
    assert_eq!(
        got["say"],
        "`say` can block: it pushes to `out`, which can wait while its reader does not read."
    );
    assert_eq!(
        got["main"],
        "`main` can block: it calls `say`, which pushes to `out`, which can wait while its reader \
         does not read."
    );
}
