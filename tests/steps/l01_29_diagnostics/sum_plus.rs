//! `sum` of a tuple is the chain of `+` over its components (DESIGN.md L1.18, the reduction
//! of `(+)`), so it accepts the programs that chain accepts, rejects those it rejects, and
//! reports a failing `+` with the same message and derivation. A component the checker does
//! not track (`_`) is left to `+`, as in `x.a + 1`, rather than refused by `sum` itself.

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
fn an_untracked_component_gets_the_first_error_of_the_written_plus() {
    let summed = rejected(&program("positional x", "sum((x.a, 1))"));
    let added = rejected(&program("positional x", "x.a + 1"));
    let (summed_all, added_all) = (diagnostics(&summed), diagnostics(&added));
    // The first error is the field read, not a refusal by `sum` of the component `_`.
    assert_eq!(summed_all[0].0, added_all[0].0, "{summed}\n{added}");
    assert!(
        summed_all[0].0.contains("reading a field with `.a`"),
        "{summed}"
    );
    let refused = |(head, _): &(&str, Vec<&str>)| head.starts_with("`sum` does not take");
    assert!(!summed_all.iter().any(refused), "{summed}");
    // The `+` that adds the components fails as the written one does, with the same steps.
    assert_eq!(
        plus_error(&summed, "`+` in `sum`"),
        plus_error(&added, "`+`"),
        "{summed}\n{added}"
    );
    // The component written first is the first `+` operand, so its error comes first too.
    let summed = rejected(&program("positional x", "sum((1, x.a))"));
    let added = rejected(&program("positional x", "1 + x.a"));
    assert!(
        diagnostics(&summed)[0]
            .0
            .starts_with("`+` in `sum` does not take (1, _)")
    );
    assert!(
        diagnostics(&added)[0]
            .0
            .starts_with("`+` does not take (1, _)")
    );
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

/// `f` adding `n` components with `sum`: a field read the checker does not track, then `n - 1`
/// literals. The first `+` fails on `_`; each later one adds a literal to its result.
pub(super) fn untracked_components(n: usize) -> String {
    let literals: String = (1..n).map(|i| format!(", {i}")).collect();
    program("positional x", &format!("sum((x.a{literals}))"))
}

/// `src`, a [`untracked_components`], is rejected at the first `+` of its `sum`.
pub(super) fn sum_over_untracked_components_rejected(src: &str) {
    let out = rejected(src);
    assert!(out.contains("`+` in `sum` does not take"), "{out}");
}

/// `sum` of 2, 3 and 9 components, the first `_` (`bench::sum_plus` times 400 and 3200).
#[test]
fn checking_sum_over_untracked_components() {
    for n in [2, 3, 9] {
        sum_over_untracked_components_rejected(&untracked_components(n));
    }
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
