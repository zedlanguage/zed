//! `sum` of a tuple is the chain of `+` over its components (DESIGN.md L1.18, the reduction
//! of `(+)`), so it accepts the programs that chain accepts, rejects those it rejects, and
//! reports a failing `+` with the same message and derivation. A component that elaboration
//! rejects, as `x.a`, gives that error alone, in `sum` as in `x.a + 1`: neither `sum` nor its
//! `+` reports it again (row FAIL-diagnostics-follow-on).

use super::{rejected, steps};
use zedc::run::load;

/// The diagnostics of `out`, each its headline without its place and the step texts below it.
fn diagnostics(out: &str) -> Vec<(&str, Vec<&str>)> {
    let mut all: Vec<(&str, Vec<&str>)> = Vec::new();
    for line in out.lines() {
        if line.starts_with(' ') {
            if let Some((_, notes)) = all.last_mut() {
                notes.extend(steps(line));
            }
        } else {
            let head = line.split_once(": ").map_or(line, |(_, rest)| rest);
            all.push((head, Vec::new()));
        }
    }
    all
}

/// The program defining `f(<params>) = <body>;` beside a `main` that does nothing.
fn program(params: &str, body: &str) -> String {
    format!("f({params}) = {body};\nmain(m: MainArgs) = 0;\n")
}

/// The rendered diagnostics of `src`, or `None` when it is accepted.
fn outcome(src: &str) -> Option<String> {
    load(src.as_bytes()).err()
}

/// The diagnostic of `out` that a `+` named `name` gave, with `name` read as `+`.
fn plus_error(out: &str, name: &str) -> Option<(String, Vec<String>)> {
    let named = |s: &str| s.replace(name, "`+`");
    diagnostics(out)
        .into_iter()
        .find(|(head, _)| head.starts_with(&format!("{name} does not take")))
        .map(|(head, notes)| (named(head), notes.into_iter().map(named).collect()))
}

#[test]
fn a_rejected_component_gives_its_own_error_alone_in_sum_as_in_the_written_plus() {
    // Written first or last, the field read gives its error and no `+` or `sum` refuses it.
    for (tuple, chain, col) in [("(x.a, 1)", "x.a + 1", 24), ("(1, x.a)", "1 + x.a", 27)] {
        let summed = rejected(&program("positional x", &format!("sum({tuple})")));
        let added = rejected(&program("positional x", chain));
        let (summed_all, added_all) = (diagnostics(&summed), diagnostics(&added));
        assert_eq!(summed_all.len(), 1, "{summed}");
        assert_eq!(summed_all[0].0, added_all[0].0, "{summed}\n{added}");
        assert_eq!(added_all.len(), 1, "{added}");
        assert!(
            summed.starts_with(&format!(
                "1:{col}: `a` is not a function in scope, and reading"
            )),
            "{summed}"
        );
    }
}

#[test]
fn sum_and_a_chain_of_plus_accept_and_reject_the_same_programs() {
    // (parameters, the tuple `sum` adds, the same components joined by `+`)
    let table = [
        ("positional x", "(x.a, 1)", "x.a + 1"),
        ("positional x", "(1, x.a)", "1 + x.a"),
        ("positional x, positional y: int", "(y, x.a)", "y + x.a"),
        (
            "positional x, positional y: int",
            "(y, x.a, 2)",
            "y + x.a + 2",
        ),
        ("positional x: int, positional y: int", "(x, y)", "x + y"),
        (
            "positional x: int, positional y: int, positional z: int",
            "(x, y, z)",
            "x + y + z",
        ),
        ("positional x: int, positional y: f64", "(x, y)", "x + y"),
        ("positional x: int, positional y: rat", "(x, y)", "x + y"),
        ("positional x: f64, positional y: rat", "(x, y)", "x + y"),
        ("positional x: f64, positional y: f64", "(x, y)", "x + y"),
        ("positional x: rat, positional y: rat", "(x, y)", "x + y"),
        (
            "positional x: int, positional y: f64 | rat",
            "(x, y)",
            "x + y",
        ),
        (
            "positional x: int | f64, positional y: int | f64",
            "(x, y)",
            "x + y",
        ),
        (
            "positional x: int, positional y: int | #a",
            "(x, y)",
            "x + y",
        ),
        ("positional x: #a, positional y: #b", "(x, y)", "x + y"),
        ("positional x: #a, positional y: int", "(x, y)", "x + y"),
        ("positional x: int", "(x, 1)", "x + 1"),
        ("positional x: f64", "(x, 1.5)", "x + 1.5"),
        ("positional x: int", "(x, 1.5)", "x + 1.5"),
        ("positional x, positional y", "(x, y)", "x + y"),
        ("positional x", "(x, 1)", "x + 1"),
    ];
    for (params, tuple, chain) in table {
        let summed = outcome(&program(params, &format!("sum({tuple})")));
        let added = outcome(&program(params, chain));
        assert_eq!(
            summed.is_some(),
            added.is_some(),
            "f({params}): sum({tuple}) and {chain} disagree\n{summed:?}\n{added:?}"
        );
        // Where the written `+` fails, the `+` in `sum` fails with the same message, except
        // for the repair the headline ends with, which rewrites the call it is in:
        // `sum((rat(x), y))` for `rat(x) + y` (row MSG-apply-try-headline).
        if let (Some(summed), Some(added)) = (&summed, &added)
            && let Some((head, _)) = plus_error(added, "`+`")
        {
            let got = plus_error(summed, "`+` in `sum`").map(|(head, _)| head);
            let bare = |h: &str| h.split_once(" Try `").map_or(h, |(h, _)| h).to_string();
            assert_eq!(
                got.as_deref().map(bare),
                Some(bare(&head)),
                "{summed}\n{added}"
            );
            assert_eq!(
                got.is_some_and(|h| h.contains(" Try `")),
                head.contains(" Try `"),
                "{summed}\n{added}"
            );
        }
    }
}

#[test]
fn int_and_f64_or_rat_in_sum_gives_only_the_plus_error() {
    let params = "positional x: int, positional y: f64 | rat";
    let summed = rejected(&program(params, "sum((x, y))"));
    let added = rejected(&program(params, "x + y"));
    let all = diagnostics(&summed);
    assert_eq!(all.len(), 1, "{summed}");
    assert_eq!(
        plus_error(&summed, "`+` in `sum`"),
        plus_error(&added, "`+`"),
        "{summed}\n{added}"
    );
}

/// `f` adding `n` (at least 2) components with `sum`: an `int`, a `rat`, then `n - 2` literals.
/// The first `+` fails on (int, rat); each later one adds a literal to its result.
pub(super) fn components_failing_at_the_first_plus(n: usize) -> String {
    let literals: String = (2..n).map(|i| format!(", {i}")).collect();
    program(
        "positional x: int, positional y: rat",
        &format!("sum((x, y{literals}))"),
    )
}

/// `src`, a [`components_failing_at_the_first_plus`], is rejected at the first `+` of its `sum`.
pub(super) fn sum_failing_at_the_first_plus_rejected(src: &str) {
    let out = rejected(src);
    assert!(out.contains("`+` in `sum` does not take"), "{out}");
}

/// `sum` of 2, 3 and 9 components, failing at the first `+` (`bench::sum_plus` times n and 8n).
#[test]
fn checking_sum_failing_at_the_first_plus() {
    for n in [2, 3, 9] {
        sum_failing_at_the_first_plus_rejected(&components_failing_at_the_first_plus(n));
    }
}

/// `f` adding `n` (at least 1) `int` parameters and an `f64` last with `sum`: every `+` but
/// the last adds two `int`s; the last fails on (int, f64), its `int` the running total.
pub(super) fn components_failing_at_the_last_plus(n: usize) -> String {
    let params: String = (0..n).map(|i| format!("positional x{i}: int, ")).collect();
    let items: String = (0..n).map(|i| format!("x{i}, ")).collect();
    program(
        &format!("{params}positional z: f64"),
        &format!("sum(({items}z))"),
    )
}

/// `src`, a [`components_failing_at_the_last_plus`] of at least 2 `int`s, is rejected at the
/// last `+` of its `sum`, whose first step says what its running total is.
pub(super) fn sum_failing_at_the_last_plus_rejected(src: &str) {
    let out = rejected(src);
    let all = diagnostics(&out);
    assert_eq!(all.len(), 1, "{out}");
    assert!(
        all[0]
            .0
            .starts_with("`+` in `sum` does not take (int, f64)"),
        "{out}"
    );
    assert_eq!(
        all[0].1.first(),
        Some(&"these components add up to int"),
        "{out}"
    );
}

/// A later `+` in `sum` adds the running total of the components before it, which has no
/// expression of its own; its first step says what that total is, at those components, as a
/// written `x + y + z` says "this `+` gives int" of its `x + y` (row
/// MSG-sum-running-total-note). The first `+` adds two components, each with its own steps,
/// and gets no such note.
#[test]
fn a_later_plus_in_sum_says_what_its_running_total_is() {
    let params = "positional x: int, positional y: int, positional z: f64";
    let src = program(params, "sum((x, y, z))");
    let summed = rejected(&src);
    let added = rejected(&program(params, "x + y + z"));
    let (s, a) = (&diagnostics(&summed)[0].1, &diagnostics(&added)[0].1);
    assert_eq!(
        s.first(),
        Some(&"these components add up to int"),
        "{summed}"
    );
    assert_eq!(a.first(), Some(&"this `+` gives int"), "{added}");
    // The total's place is the components it adds up, `x, y`, as the written chain's note
    // stands at `x + y`.
    let col = src.find("x, y, z").map_or(0, |i| i + 1);
    assert!(
        summed.contains(&format!("1:{col}: these components add up to int")),
        "{summed}"
    );
    for n in [2, 3, 9] {
        sum_failing_at_the_last_plus_rejected(&components_failing_at_the_last_plus(n));
    }
    // Failing at the first `+`, there is no running total yet.
    let first = rejected(&program(
        "positional z: f64, positional x: int, positional y: int",
        "sum((z, x, y))",
    ));
    assert!(!first.contains("add up to"), "{first}");
}

/// The headline of the first diagnostic of `out`, without its place.
fn headline(out: &str) -> String {
    diagnostics(out)
        .first()
        .map_or_else(String::new, |(head, _)| head.to_string())
}

/// The `+` in `sum` reports its error where the components it adds are written, `x, y` in
/// `sum((x, y))`, which is not an expression; its headline repair rewrites the whole call
/// (row MSG-apply-try-headline). It once wrote the components alone, "Try `rat(x), y`
/// instead." A tuple not written in the call gives no rewrite, and a call over two lines,
/// which a headline cannot show, gives none either; the repair stays in the notes.
#[test]
fn a_repair_of_the_plus_in_sum_rewrites_the_whole_call() {
    for (params, body, call) in [
        (
            "x: int, positional y: rat",
            "sum((x, y))",
            Some("sum((rat(x), y))"),
        ),
        (
            "y: rat, positional x: int",
            "sum((y, x))",
            Some("sum((y, rat(x)))"),
        ),
        (
            "x: int, positional y: rat, positional z: rat",
            "sum((x, y, z))",
            Some("sum((rat(x), y, z))"),
        ),
        ("x: int, positional y: rat", "sum((x,\n  y))", None),
        ("t: (int, rat)", "sum(t)", None),
    ] {
        let out = rejected(&program(&format!("positional {params}"), body));
        let pair = if body.starts_with("sum((y") {
            "rat, int"
        } else {
            "int, rat"
        };
        let head = format!(
            "`+` in `sum` does not take ({pair}): no arrow of `+` in `sum` takes these types."
        );
        let want = match call {
            Some(c) => format!("{head} Try `{c}` instead."),
            None => head,
        };
        assert_eq!(headline(&out), want, "{out}");
        if call.is_none() && body.contains('\n') {
            assert!(out.contains("repair: write `rat(x)`"), "{out}");
        }
    }
    // The written chain rewrites the `+` alone.
    let out = rejected(&program("positional x: int, positional y: rat", "x + y"));
    assert!(
        headline(&out).ends_with("Try `rat(x) + y` instead."),
        "{out}"
    );
}
