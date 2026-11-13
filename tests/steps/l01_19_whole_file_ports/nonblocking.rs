//! `@nonblocking` on a function written in Zed (DESIGN.md sec:ports; sec:diagnostics,
//! "Function marked `@nonblocking` that can block"): a function so marked that can block is
//! rejected at its annotation, with the path of calls from it to the blocking operation; one
//! that cannot block checks, runs and is called as any other. The annotation stands before a
//! function or method declaration and takes no arguments; written anywhere else it is refused.

use zed_tests::deep::{resolved, statements};
use zedc::check::blocking::{facts_and_marks, marked_errors};
use zedc::check::walk::check_text;
use zedc::rejection::Row;
use zedc::resolve::tables::Tables;

use super::run;

/// The errors of checking `text`, each as its headline and then its notes, one per line.
fn errors(text: &str) -> Vec<String> {
    let (stmts, res) = resolved(text);
    let info = check_text(&stmts, &res, Some(text));
    (info.errors.iter())
        .map(|e| {
            let mut s = e.message.clone();
            for n in &e.notes {
                s.push_str(&format!(
                    "\n  {}: {}",
                    &text[n.span.start..n.span.end],
                    n.text
                ));
            }
            s
        })
        .collect()
}

/// The rows of the errors of checking `text`.
fn rows(text: &str) -> Vec<Option<Row>> {
    let (stmts, res) = resolved(text);
    let info = check_text(&stmts, &res, Some(text));
    info.errors.iter().map(|e| e.row).collect()
}

/// The resolver's messages for `text`, which it refuses.
fn refused(text: &str) -> Vec<String> {
    let stmts = statements(text);
    let errs = zedc::resolve::resolve(&stmts).expect_err(text);
    errs.into_iter().map(|e| e.message).collect()
}

const FIRST: &str = "first(positional xs) = xs[0] else \"\";\n";

/// The example of the row: a helper marked `@nonblocking` reaches a read of `m.stdin` through
/// a call; the error is at the annotation and names each step, then the repairs.
#[test]
fn a_marked_function_that_can_block_is_rejected_with_its_path() {
    let text = format!(
        "{FIRST}@nonblocking\nhelper(positional xs) = first(xs);\n\
         main(m: MainArgs) -> int {{\n  if helper(m.stdin) == \"a\" {{ 1 }} else {{ 0 }}\n}}\n"
    );
    assert_eq!(
        errors(&text),
        ["`helper` is marked `@nonblocking` but can block.\n  \
          first: `helper` calls `first`, which can block\n  \
          xs: `first` reads `xs`, which holds `m.stdin`, which can wait for its data\n  \
          @nonblocking: repair: remove `@nonblocking` before `helper`\n  \
          @nonblocking: repair: move the blocking operation to a caller of `helper`, and pass \
          in what it reads or gives"]
    );
    assert_eq!(rows(&text), [Some(Row::NonblockingCanBlock)]);
    let out = run("nonblocking_path", &text, "a\n", &[]);
    assert_eq!(out.status, 1, "{}", out.stderr);
    assert!(
        out.stderr
            .contains("`helper` is marked `@nonblocking` but can block."),
        "{}",
        out.stderr
    );
}

/// A marked function that only reads `m.args`, or computes, cannot block: it checks and runs.
#[test]
fn a_marked_function_that_cannot_block_checks_and_runs() {
    let text = "@nonblocking\nscale(positional x: int) = x * 2;\n\
                @nonblocking\nopt(positional a) = a[0] else \"\";\n\
                main(m: MainArgs) -> int {\n  if opt(m.args) == \"x\" { if scale(1) == 2 { 5 } else { 3 } } else { 0 }\n}\n";
    assert_eq!(errors(text), Vec::<String>::new());
    assert_eq!(run("nonblocking_ok", text, "", &["--", "x"]).status, 5);
    assert_eq!(run("nonblocking_ok_no", text, "", &[]).status, 0);
}

/// A call of a function value whose body the checker cannot see counts as for the fact.
#[test]
fn a_marked_function_calling_a_function_value_is_rejected() {
    let text = "@nonblocking\napply(positional f) = f(1);\nmain(m: MainArgs) -> int { 0 }\n";
    assert_eq!(
        errors(text)[0].lines().take(2).collect::<Vec<_>>(),
        [
            "`apply` is marked `@nonblocking` but can block.",
            "  f(1): `apply` calls `f`, a function value whose body is not known here, so the \
             call may block"
        ]
    );
}

/// A marked function that pushes to its output port can wait while the reader does not read.
#[test]
fn a_marked_function_that_pushes_is_rejected() {
    let text = "@nonblocking\nsay(positional s, out: Lines) { out <- s; }\n\
                main(m: MainArgs) {\n  _ = say(\"hi\", out: m.stdout);\n}\n";
    assert_eq!(
        errors(text)[0].lines().take(2).collect::<Vec<_>>(),
        [
            "`say` is marked `@nonblocking` but can block.",
            "  out <- s;: `say` pushes to `out`, which can wait while its reader does not read"
        ]
    );
}

/// Only the marked function is reported, not the unmarked caller that blocks through it.
#[test]
fn only_marked_functions_are_reported() {
    let text = format!(
        "{FIRST}@nonblocking\nmid(positional xs) = first(xs);\n\
         top(positional xs) = mid(xs);\n\
         main(m: MainArgs) -> int {{\n  if top(m.stdin) == \"a\" {{ 1 }} else {{ 0 }}\n}}\n"
    );
    let got = errors(&text);
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(got[0].starts_with("`mid` is marked"), "{got:?}");
}

/// Each function's step is shown by one error: a path stops at a marked function, which has
/// its own error, and at an unmarked one an earlier error went through, pointing at its step.
#[test]
fn a_path_stops_where_another_error_shows_the_rest() {
    let text = format!(
        "{FIRST}mid(positional xs) = first(xs);\n\
         @nonblocking\nleft(positional xs) = mid(xs);\n\
         @nonblocking\nright(positional xs) = mid(xs);\n\
         @nonblocking\ntop(positional xs) = left(xs);\n\
         main(m: MainArgs) -> int {{\n  \
         if top(m.stdin) == right(m.stdin) {{ 1 }} else {{ 0 }}\n}}\n"
    );
    let got = errors(&text);
    let path = |who: &str| -> Vec<String> {
        let e = got
            .iter()
            .find(|e| e.starts_with(&format!("`{who}` is marked")))
            .unwrap_or_else(|| panic!("{who}: {got:?}"));
        e.lines()
            .skip(1)
            .filter(|l| !l.contains("repair:"))
            .map(str::to_string)
            .collect()
    };
    assert_eq!(
        path("left"),
        [
            "  mid: `left` calls `mid`, which can block",
            "  first: `mid` calls `first`, which can block",
            "  xs: `first` reads `xs`, which holds `m.stdin`, which can wait for its data"
        ]
    );
    assert_eq!(
        path("right"),
        [
            "  mid: `right` calls `mid`, which can block",
            "  first: `mid` can block: another error shows the rest of the path from here"
        ]
    );
    assert_eq!(
        path("top"),
        [
            "  left: `top` calls `left`, which can block",
            "  @nonblocking: `left` is marked `@nonblocking` too, and its own error shows how it \
             can block"
        ]
    );
}

/// The path is followed around a cycle of calls to the operation, and ends: the checker also
/// refuses the recursion, which this zedc does not compile.
#[test]
fn the_path_ends_on_a_cycle() {
    let text = "a(positional xs, positional k: int) = \
                if k == 0 { xs[0] else \"\" } else { b(xs, k - 1) };\n\
                @nonblocking\nb(positional xs, positional k: int) = a(xs, k);\n\
                main(m: MainArgs) -> int {\n  if b(m.stdin, 3) == \"a\" { 1 } else { 0 }\n}\n";
    let got = errors(text);
    let marked: Vec<_> = got
        .iter()
        .filter(|e| e.starts_with("`b` is marked"))
        .collect();
    assert_eq!(marked.len(), 1, "{got:?}");
    assert_eq!(
        marked[0].lines().nth(2),
        Some("  xs: `a` reads `xs`, which holds `m.stdin`, which can wait for its data")
    );
}

/// The annotation takes no arguments, is written once, and stands before a function.
#[test]
fn a_misplaced_or_called_annotation_is_refused() {
    let body = "f(positional x: int) = x;\nmain(m: MainArgs) -> int { 0 }\n";
    assert_eq!(
        refused(&format!("@nonblocking()\n{body}")),
        ["`@nonblocking` takes no arguments. Write `@nonblocking` alone before the function."]
    );
    assert_eq!(
        refused(&format!("@nonblocking @nonblocking\n{body}")),
        ["`@nonblocking` is written twice before one declaration. Remove one."]
    );
    assert_eq!(
        refused("@nonblocking\nx = 3;\nmain(m: MainArgs) -> int { x }\n"),
        [
            "`@nonblocking` marks a function, and here it stands before a binding. Remove it, \
             or write it before a function declaration."
        ]
    );
    assert_eq!(
        refused("@nonblocking;\nmain(m: MainArgs) -> int { 0 }\n"),
        [
            "`@nonblocking;` is not a unit item: `@nonblocking` marks a function, written before \
             its declaration, as in `@nonblocking scale(positional x: int) = x * 2;`"
        ]
    );
}

/// A chain of n functions, each calling the next and each marked, the last reading its
/// argument passed `m.stdin`: every mark is decided by one lookup in the fact, found once, and
/// each error's path stops at the next marked function, which has its own error, so the n
/// errors are written in O(n), not the O(n²) of n whole paths.
#[test]
fn a_long_marked_chain_is_checked_in_linear_time() {
    let units = zed_tests::scaling::inputs(4_000, |n| {
        let mut text = String::from("@nonblocking\nc0(positional xs) = xs[0] else \"\";\n");
        for i in 1..n {
            text.push_str(&format!(
                "@nonblocking\nc{i}(positional xs) = c{}(xs);\n",
                i - 1
            ));
        }
        text.push_str(&format!(
            "main(m: MainArgs) -> int {{\n  if c{}(m.stdin) == \"a\" {{ 1 }} else {{ 0 }}\n}}\n",
            n - 1
        ));
        let (stmts, res) = resolved(&text);
        (text, stmts, res)
    });
    zed_tests::scaling::check_order("checking n marked functions", 4_000, 1, |n| {
        let (text, stmts, res) = &units[&n];
        let t = Tables::with_text(stmts, res, Some(text));
        let (facts, marked) = facts_and_marks(&t, stmts);
        assert_eq!(marked.len(), n);
        assert_eq!(marked_errors(&facts, &marked, res, Some(text)).len(), n);
    });
}
