//! `sum` of a tuple is the chain of `+` over its components (DESIGN.md L1.18, the reduction
//! of `(+)`), so it accepts the programs that chain accepts, rejects those it rejects, and
//! reports a failing `+` with the same message and derivation. A component the checker does
//! not track (`_`) is left to `+`, as in `x.a + 1`, rather than refused by `sum` itself.

use zed_tests::scaling;

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
        // Where the written `+` fails, the `+` in `sum` fails with the same message.
        if let (Some(summed), Some(added)) = (&summed, &added)
            && let Some((head, _)) = plus_error(added, "`+`")
        {
            let got = plus_error(summed, "`+` in `sum`").map(|(head, _)| head);
            assert_eq!(got.as_deref(), Some(head.as_str()), "{summed}\n{added}");
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
fn untracked_components(n: usize) -> String {
    let literals: String = (1..n).map(|i| format!(", {i}")).collect();
    program("positional x", &format!("sum((x.a{literals}))"))
}

#[test]
fn checking_sum_over_untracked_components_scales() {
    let inputs = scaling::inputs(400, untracked_components);
    scaling::check("checking `sum` of n components, the first `_`", 400, |n| {
        let out = rejected(&inputs[&n]);
        assert!(out.contains("`+` in `sum` does not take"), "{out}");
    });
}
