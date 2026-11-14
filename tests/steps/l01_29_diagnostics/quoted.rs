//! A listing of diagnostics shows each source line once: the first diagnostic with a step on a
//! line shows it with its marks, and each later one gives its steps on that line by their
//! ranges and says the line is shown above. Before, every diagnostic showed the whole line
//! again, so n errors on one line of length O(n) printed O(n²) characters (COMPLEXITY.md
//! RENDER-line-per-error).

use zedc::front::{Diagnostic, Quoted, Step};

use super::rejected;

/// The text line 1 of [`failing_sum`] and [`failing_tuple`] starts with.
const START: &str = "f(positional x: String) = ";

/// `f` adding with `sum` `n` components, each `x + 1` with `x` a `String`, all on one line: each
/// `+` fails, with its steps on the line. (A field read the checker does not track, `x.a`, gave
/// these errors before; elaboration rejects it, and it now gives that error alone, row
/// FAIL-diagnostics-follow-on.)
pub(super) fn failing_sum(n: usize) -> String {
    let xs = vec!["x + 1"; n].join(", ");
    format!("{START}sum(({xs},));\nmain(m: MainArgs) = 0;\n")
}

/// `f` giving a tuple of `n` failing `x + 1`, all on one line.
fn failing_tuple(n: usize) -> String {
    let xs = vec!["x + 1"; n].join(", ");
    format!("{START}({xs},);\nmain(m: MainArgs) = 0;\n")
}

/// The number of times `out` shows source line 1, whose text starts with `start`.
fn shown(out: &str, start: &str) -> usize {
    out.lines()
        .filter(|l| {
            l.trim_start()
                .strip_prefix("1 | ")
                .is_some_and(|t| t.starts_with(start))
        })
        .count()
}

/// The diagnostics of `out`, each its lines.
fn diagnostics(out: &str) -> Vec<Vec<&str>> {
    let mut all: Vec<Vec<&str>> = Vec::new();
    for line in out.lines() {
        match all.last_mut() {
            Some(d) if line.starts_with(' ') => d.push(line),
            _ => all.push(vec![line]),
        }
    }
    all
}

#[test]
fn many_errors_on_one_line_show_it_once() {
    for src in [failing_sum(6), failing_tuple(6)] {
        let out = rejected(&src);
        let ds = diagnostics(&out);
        assert!(ds.len() > 2, "{out}");
        assert_eq!(shown(&out, START), 1, "{out}");
        // Every later diagnostic with a step on the line says where it is shown, and gives each
        // step there by its range.
        let mut seen = false;
        for d in &ds {
            let steps: Vec<&&str> = d
                .iter()
                .filter(|l| l.trim_start().starts_with('['))
                .collect();
            if steps.is_empty() {
                continue;
            }
            if seen {
                assert!(
                    d.iter().any(|l| l.trim_start() == "line 1 is shown above"),
                    "{}",
                    d.join("\n")
                );
                for s in steps {
                    assert!(s.contains(" to 1:"), "{s}\n{out}");
                }
            }
            seen = true;
        }
    }
}

#[test]
fn every_step_stays_when_the_line_is_shown_once() {
    // Each diagnostic keeps every step it had: the listing has as many step lines as the
    // diagnostics have steps, which the derivation fixes and the layout does not change.
    let out = rejected(&failing_sum(4));
    let n = out
        .lines()
        .filter(|l| l.trim_start().starts_with('['))
        .count();
    assert_eq!(n, super::steps(&out).len(), "{out}");
    assert!(
        out.matches("`x` is String here").count() == 4,
        "the step that places each failing operand is kept:\n{out}"
    );
}

/// The sum of [`failing_sum`]`(n)` gives one diagnostic per component, each with seven steps,
/// and its line is shown once.
pub(super) fn many_errors_rendered_on_one_line(src: &str) {
    let out = rejected(src);
    assert_eq!(shown(&out, START), 1);
}

#[test]
fn rendering_many_errors_on_one_line() {
    for n in [1, 2, 9] {
        many_errors_rendered_on_one_line(&failing_sum(n));
    }
}

fn step(line: usize, col: usize, text: &str, source: &str, width: usize) -> Step {
    Step {
        line,
        col,
        text: text.into(),
        source: source.into(),
        width,
    }
}

fn diagnostic(line: usize, col: usize, steps: Vec<Step>) -> Diagnostic {
    Diagnostic {
        row: None,
        address: zedc::address::ContentAddress([0; 32]),
        line,
        col,
        message: "the message".into(),
        steps,
        menu: String::new(),
    }
}

/// A line with a tab, a name with a combining acute accent (two characters, one column) and a
/// string of two wide characters (two columns each): 21 characters, its `;` the last.
const MIXED: &str = "\tname = \"日本\" ++ ne\u{301}e;";

#[test]
fn the_first_diagnostic_on_a_line_prints_as_it_does_alone() {
    let a = diagnostic(1, 1, vec![step(1, 1, "the tab", MIXED, 1)]);
    let b = diagnostic(
        2,
        7,
        vec![step(2, 7, "`name` is used here", "  y = name;", 4)],
    );
    let mut quoted = Quoted::default();
    assert_eq!(quoted.show(&a), a.to_string());
    assert_eq!(quoted.show(&b), b.to_string());
    assert_eq!(
        a.to_string(),
        "1:1: the message
  [1] 1:1: the tab
      1 |     name = \"日本\" ++ ne\u{301}e;
        | ^^^^"
    );
}

#[test]
fn steps_on_a_line_shown_above_are_given_by_their_ranges_and_a_new_line_is_shown() {
    // The first column, the last, a span over all but the first character, a tab, wide and
    // combining characters, and a second line not yet shown.
    let a = diagnostic(1, 1, vec![step(1, 1, "the tab", MIXED, 1)]);
    let b = diagnostic(
        1,
        2,
        vec![
            step(1, 2, "`name` is defined here", MIXED, 4),
            step(1, 9, "this expression is \"日本\"", MIXED, 4),
            step(1, 17, "`née` is int here", MIXED, 4),
            step(1, 21, "the `;`", MIXED, 1),
            step(1, 2, "most of the line", MIXED, 20),
            step(2, 7, "`name` is used here", "  y = name;", 4),
        ],
    );
    let mut quoted = Quoted::default();
    quoted.show(&a);
    assert_eq!(
        quoted.show(&b),
        "1:2: the message
  [1] 1:2 to 1:5: `name` is defined here
      line 1 is shown above
  [2] 1:9 to 1:12: this expression is \"日本\"
  [3] 1:17 to 1:20: `née` is int here
  [4] 1:21 to 1:21: the `;`
  [5] 1:2 to 1:21: most of the line
  [6] 2:7: `name` is used here
      2 |   y = name;
        |       ^^^^"
    );
    // Both lines are shown now: a third diagnostic on them shows neither.
    let c = diagnostic(
        2,
        1,
        vec![
            step(2, 1, "the indent", "  y = name;", 2),
            step(1, 1, "the tab", MIXED, 1),
        ],
    );
    assert_eq!(
        quoted.show(&c),
        "2:1: the message
  [1] 2:1 to 2:2: the indent
      line 2 is shown above
  [2] 1:1 to 1:1: the tab
      line 1 is shown above"
    );
}

/// `n` diagnostics on one line of `n` components, as the `+` of a `sum` gives them: the k-th
/// covers the first k + 1 components, and its second step the (k + 1)-th.
pub(super) fn sums(n: usize) -> Vec<Diagnostic> {
    let line = format!("f(x) = sum(({}));", vec!["x.a"; n].join(", "));
    (1..n)
        .map(|k| {
            let at = |i: usize| 13 + 5 * i;
            diagnostic(
                1,
                13,
                vec![
                    step(1, at(k), "this expression is _", &line, 3),
                    step(
                        1,
                        13,
                        "`+` in `sum` takes (int, int) -> int",
                        &line,
                        at(k) + 3 - 13,
                    ),
                ],
            )
        })
        .collect()
}

/// `n` diagnostics on one line of `n` operands of `+`, each on one operand.
pub(super) fn operands(n: usize) -> Vec<Diagnostic> {
    let line = format!("f(x) = {};", vec!["x.a"; n].join(" + "));
    (0..n)
        .map(|k| {
            let at = 8 + 6 * k;
            diagnostic(1, at, vec![step(1, at, "this expression is _", &line, 3)])
        })
        .collect()
}

/// The listing of `ds`, each line shown once.
pub(super) fn listing(ds: &[Diagnostic]) -> String {
    let mut quoted = Quoted::default();
    ds.iter()
        .map(|d| quoted.show(d))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn listing_many_diagnostics_on_one_line_shows_it_once() {
    // `bench::quoted` holds the bytes of these listings to order n; here the line they share
    // is quoted by the first diagnostic only.
    for n in [2, 3, 9] {
        for ds in [sums(n), operands(n)] {
            let out = listing(&ds);
            assert_eq!(out.matches("f(x) = ").count(), 1, "{out}");
            assert_eq!(
                out.matches("this expression is _").count(),
                ds.len(),
                "{out}"
            );
        }
    }
}
