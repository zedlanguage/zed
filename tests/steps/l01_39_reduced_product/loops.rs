//! Tests whose `||` alternatives limit each other's ranges in a loop (DESIGN.md L1.39,
//! conditions (i) and (iii); sec:diagnostics row "A test whose `||` alternatives limit each
//! other's ranges in a loop"): such a test is rejected at its `if`, through `zedc run`, with
//! its message in the program's names; a test in the class is accepted and its arms hold every
//! value that reaches them; and the classification scales.

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zed_tests::step_helpers::l01_19a_command_line::run;
use zedc::store::product::Scope;

use super::*;

/// A `main` reading `x` and `y`, which, within `-B..=B` for both, gives `body` when `test`
/// holds and `0` when it fails.
fn program(bound: i64, test: &str, body: &str) -> String {
    format!(
        "main(m: MainArgs) {{\n  x = int(m.stdin[0]) else 0;\n  y = int(m.stdin[1]) else 0;\n  \
         r = if x >= -{bound} && x <= {bound} && y >= -{bound} && y <= {bound} {{\n    \
         if {test} {{ {body} }} else {{ 0 }}\n  }} else {{ 2 }};\n  m.stdout <- \"${{r}}\";\n}}\n"
    )
}

/// What `zedc run` writes to stderr for `src`, each place written from the file name on, and
/// its exit status.
fn rejected(name: &str, src: &str) -> (u8, String) {
    let o = run(name, src, &[]);
    let text = (o.stderr.lines())
        .map(|l| match l.find("prog.zed:") {
            Some(i) => &l[i..],
            None => l,
        })
        .collect::<Vec<_>>()
        .join("\n");
    (o.status, text)
}

/// The ping-pong test: each choice bounds one name from the other.
const PING: &str = "(x - y >= 1 || x >= 0) && (y - x >= 1 || y >= 0)";

#[test]
fn a_loop_through_two_choices_is_rejected_through_zedc_run_with_its_message() {
    let (status, text) = rejected("loops_ping", &program(1000, PING, "popCount(x + 1000)"));
    let want = "\
prog.zed:5:8: The ranges of `x` and `y` inside this `if` cannot be worked out.
  [1] 5:8: the test is a list of choices joined by `&&`, each a set of alternatives joined by `||`: where it holds, at least one alternative of each choice holds, and the checker narrows each name's range to the values some combination of alternatives allows
      5 |     if (x - y >= 1 || x >= 0) && (y - x >= 1 || y >= 0) { popCount(x + 1000) } else { 0 }
        |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [2] 5:8: the choice `x - y >= 1 || x >= 0`: `x - y >= 1` makes the least possible x at least the least possible y plus 1 and makes the largest possible y at most the largest possible x minus 1; `x >= 0` makes the least possible x at least 0
  [3] 5:8: the choice `y - x >= 1 || y >= 0`: `y - x >= 1` makes the largest possible x at most the largest possible y minus 1 and makes the least possible y at least the least possible x plus 1; `y >= 0` makes the least possible y at least 0
  [4] 5:8: these choices form a loop of limits: the least y limits the least x, which limits the least y: `x - y >= 1` makes the least possible x at least the least possible y plus 1; `y - x >= 1` makes the least possible y at least the least possible x plus 1
  [5] 5:8: one time around the loop changes the least y by 2: it rises from -1,000 to -998, then -996
  [6] 5:8: the answer would take about 499 times around it, a number that grows with the ranges `x: int[-1000..=1000]` and `y: int[-1000..=1000]` and not with the program
  [7] 5:8: the checker does no work whose amount depends on the values in the ranges rather than on the program text, so it rejects this test instead of running the loop
  [8] 5:8: repair: write the choice `x - y >= 1 || x >= 0` as an `if` on its alternatives, inside an `if` on the rest of the test, so that no loop of limits passes through it, with the body of the `if` at each `…`:
if (y - x >= 1 || y >= 0) {
    if x - y >= 1 {
        …
    } else if x >= 0 {
        …
    }
}";
    assert_eq!((status, text.as_str()), (1, want));
}

#[test]
fn the_loop_is_rejected_whether_or_not_an_arm_is_read() {
    // The class is a property of the test as written: no arm here reads a range, and no
    // outer test bounds the names, so the message gives no values.
    let src = "main(m: MainArgs) {\n  x = int(m.stdin[0]) else 0;\n  y = int(m.stdin[1]) else 0;\n  \
               r = if (x - y >= 1 || x >= 0) && (y - x >= 1 || y >= 0) { 1 } else { 0 };\n  \
               m.stdout <- \"${r}\";\n}\n";
    let (status, text) = rejected("loops_unread", src);
    assert_eq!(status, 1, "{text}");
    assert!(
        text.starts_with(
            "prog.zed:4:10: The ranges of `x` and `y` inside this `if` cannot be worked out."
        ),
        "{text}"
    );
    assert!(
        text.contains(
            "each time around the loop can move these limits again, and the number of times \
             the answer would take grows with the ranges of the names and not with the program"
        ),
        "{text}"
    );
}

#[test]
fn the_repair_the_message_prints_is_accepted_and_runs() {
    // The repair above, with the body at each `…`.
    let test = "y - x >= 1 || y >= 0 {\n      if x - y >= 1 { popCount(x + 1000) } else if x >= 0 { \
                popCount(x + 1000) } else { 0 }\n    } else if false";
    let src = program(1000, test, "0");
    let o = run("loops_repair", &src, &[]);
    assert_eq!(
        (o.status, o.stdout.as_str(), o.stderr.as_str()),
        (0, "6\n", ""),
        "{src}"
    );
}

#[test]
fn a_bound_two_alternatives_set_on_a_loop_is_rejected() {
    // Both alternatives set the largest x, which lies on a loop through the base: `y <= x + 1`
    // bounds the largest y by the largest x, and `x <= y - 2` the largest x by the largest y
    // (condition (iii)).
    let test = "(x <= 3 || 2 * x <= y - 2) && y <= 2 * x + 1";
    let (status, text) = rejected("loops_three", &program(100, test, "popCount(x + 100)"));
    let want = "\
prog.zed:5:8: The ranges of `x` and `y` inside this `if` cannot be worked out.
  [1] 5:8: the test is a list of choices joined by `&&`, each a set of alternatives joined by `||`: where it holds, at least one alternative of each choice holds, and the checker narrows each name's range to the values some combination of alternatives allows
      5 |     if (x <= 3 || 2 * x <= y - 2) && y <= 2 * x + 1 { popCount(x + 100) } else { 0 }
        |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [2] 5:8: the choice `x <= 3 || 2 * x <= y - 2`: `x <= 3` makes the largest possible x at most 3; `2 * x <= y - 2` makes the largest possible x at most the largest possible y minus 2, divided by 2 and makes the least possible y at least 2 times the least possible x plus 2
  [3] 5:8: the choice `x <= 3 || 2 * x <= y - 2` sets the largest x through two of its alternatives, `x <= 3` and `2 * x <= y - 2`, so the largest x is the larger of the two
  [4] 5:8: the largest x lies on a loop of limits: the largest x limits the largest y, which limits the largest x: `y <= 2 * x + 1` makes the largest possible y at most 2 times the largest possible x plus 1; `2 * x <= y - 2` makes the largest possible x at most the largest possible y minus 2, divided by 2
  [5] 5:8: after the loop settles, `x <= 3` or `2 * x <= y - 2` would change the largest x again, so the loop would have to be run again, a number of times that grows with the ranges of the names and not with the program; the checker does no work whose amount depends on the values in the ranges rather than on the program text, so it rejects this test
  [6] 5:8: repair: write the choice `x <= 3 || 2 * x <= y - 2` as an `if` on its alternatives, inside an `if` on the rest of the test, so that no loop of limits passes through it, with the body of the `if` at each `…`:
if y <= 2 * x + 1 {
    if x <= 3 {
        …
    } else if 2 * x <= y - 2 {
        …
    }
}";
    assert_eq!((status, text.as_str()), (1, want));
}

#[test]
fn a_choice_that_holds_on_the_box_adds_no_loop_unless_it_holds_a_test_the_class_does_not_read() {
    // `x <= 8` holds wherever `x <= 3` does, so the first choice narrows nothing and the
    // ping-pong loop is not there; with `x != y` beside it, the class cannot tell, and the
    // loop is kept.
    let kept = "x <= 3 && (x - y >= 1 || x <= 8 && x != y) && (y - x >= 1 || y >= 0)";
    let (status, text) = rejected("loops_kept", &program(100, kept, "popCount(x + 100)"));
    assert_eq!(status, 1, "{text}");
    assert!(
        text.starts_with(
            "prog.zed:5:8: The ranges of `x` and `y` inside this `if` cannot be worked out."
        ),
        "{text}"
    );
}

/// Tests in the class, each with the same test as a Rust predicate: a hole and a bound from
/// the other name; one choice on no loop; a loop broken by a hole; `!=`; an offset equality
/// merged before the graph; a choice whose bound the base sets again; a test whose opposite is
/// one choice whose alternatives set the least x twice; a choice that holds on the box.
/// A test as written and as a Rust predicate.
type Written = (&'static str, fn(i64, i64) -> bool);

const IN_CLASS: [Written; 8] = [
    ("(x <= 2 || x >= 5) && x <= y", |x, y| {
        (x <= 2 || x >= 5) && x <= y
    }),
    ("x <= y || x <= 5", |x, y| x <= y || x <= 5),
    ("(x - y >= 1 || x >= 0) && (y >= 3 || y <= -3)", |x, y| {
        (x - y >= 1 || x >= 0) && (y >= 3 || y <= -3)
    }),
    ("x != y && (x <= 3 || y <= 3)", |x, y| {
        x != y && (x <= 3 || y <= 3)
    }),
    ("x - y == 2 && (x <= 5 || y >= 7)", |x, y| {
        x - y == 2 && (x <= 5 || y >= 7)
    }),
    ("(x <= y - 1 || x <= 5) && y <= x + 3", |x, y| {
        (x < y || x <= 5) && y <= x + 3
    }),
    (
        "(x <= 2 || x >= 5) && (x <= y || y <= 7) && x != 5",
        |x, y| (x <= 2 || x >= 5) && (x <= y || y <= 7) && x != 5,
    ),
    (
        "x <= 3 && (x - y >= 1 || x <= 8) && (y - x >= 1 || y >= 0)",
        |x, y| x <= 3 && (x - y >= 1 || x <= 8) && (y - x >= 1 || y >= 0),
    ),
];

#[test]
fn tests_in_the_class_are_accepted_through_zedc_run() {
    for (i, (test, _)) in IN_CLASS.iter().enumerate() {
        let src = program(20, test, "popCount(x + 20)");
        let o = run(&format!("loops_in_{i}"), &src, &[]);
        assert_eq!((o.status, o.stderr.as_str()), (0, ""), "{src}");
    }
}

#[test]
fn the_arms_of_tests_in_the_class_hold_every_value_that_reaches_them() {
    // Enumeration over `-6..=6` for both names: each arm's ranges hold every point that
    // reaches it, with the least and greatest such value as their ends, and no arm keeps a
    // refusal of the loop.
    const B: i64 = 6;
    for (test, holds) in IN_CLASS {
        let src = format!(
            "ok(x, y) = if x >= -{B} && x <= {B} && y >= -{B} && y <= {B} {{ \
             if {test} {{ 1 }} else {{ 0 }} }} else {{ 2 }};"
        );
        let (_, _, a) = arms_of(&src);
        for outcome in [true, false] {
            // The inner `if`'s arm: the one whose test is not the outer bound on both names.
            let arm = (a.iter())
                .find(|a| !a.guard.contains(&format!("-{B}")) && a.outcome == outcome)
                .unwrap_or_else(|| panic!("{test}: no inner arm among {a:?}"));
            assert!(arm.scope.looped().is_empty(), "{test} {outcome}");
            let points: Vec<(i64, i64)> = (-B..=B)
                .flat_map(|x| (-B..=B).map(move |y| (x, y)))
                .filter(|&(x, y)| holds(x, y) == outcome)
                .collect();
            assert_eq!(arm.reachable(), !points.is_empty(), "{test} {outcome}");
            for (name, at) in [("x", 0), ("y", 1)] {
                let ints = arm.scope.names.get(name).map(|p| p.ints().clone());
                for p in &points {
                    let v = if at == 0 { p.0 } else { p.1 };
                    assert!(
                        ints.as_ref().is_none_or(|s| s.contains(v)),
                        "{test} {outcome}: {name} = {v} reaches the arm, outside {ints:?}"
                    );
                }
                // And the least and greatest values are exact: the narrowing decides the
                // component, it does not only keep it sound.
                let vs = points.iter().map(|p| if at == 0 { p.0 } else { p.1 });
                if let (Some(lo), Some(hi), Some(s)) = (vs.clone().min(), vs.max(), &ints) {
                    assert!(
                        !s.contains(lo - 1) && !s.contains(hi + 1),
                        "{test} {outcome}: {name} is {lo}..={hi} by enumeration, wider in {ints:?}"
                    );
                }
            }
        }
    }
}

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

/// `a - b >= 1 || a >= 0`.
fn choice(a: &str, b: &str) -> Term {
    let step = prim(Prim::Ge, prim(Prim::Sub, var(a), var(b)), int(1));
    prim(Prim::Or, step, prim(Prim::Ge, var(a), int(0)))
}

/// The test on `x0..=xk`, each within `-1000..=1000`, of the choices
/// `x_i - x_{i+1} >= 1 || x_i >= 0`, closed by `x_k - x_0 >= 1 || x_k >= 0` into one loop of
/// `k + 1` choices when `closed`.
fn chain(k: usize, closed: bool) -> Term {
    let n: Vec<String> = (0..=k).map(|i| format!("x{i}")).collect();
    let mut sides = Vec::new();
    for x in &n {
        sides.push(prim(Prim::Ge, var(x), int(-1000)));
        sides.push(prim(Prim::Le, var(x), int(1000)));
    }
    sides.extend((0..k).map(|i| choice(&n[i], &n[i + 1])));
    if closed {
        sides.push(choice(&n[k], &n[0]));
    }
    let and = |a: Term, b: Term| prim(Prim::And, a, b);
    sides.into_iter().reduce(and).expect("a side")
}

fn chain_scope(k: usize) -> Scope {
    let n: Vec<Arc<str>> = (0..=k).map(|i| format!("x{i}").into()).collect();
    ints(&n)
}

#[test]
fn a_chain_of_choices_is_in_the_class_and_the_closed_chain_is_not() {
    for k in [1, 2, 7] {
        let s = chain_scope(k);
        assert!(
            s.looped_test(&chain(k, false), true).is_none(),
            "open chain of {k}"
        );
        assert!(
            s.looped_test(&chain(k, true), true).is_some(),
            "closed chain of {k}"
        );
        // Where the test fails it is one choice of every opposite side, whose loops are its
        // own, so even the closed chain's `else` is in the class.
        assert!(
            s.looped_test(&chain(k, true), false).is_none(),
            "else of closed chain of {k}"
        );
    }
}

#[test]
fn classifying_a_chain_of_choices_scales() {
    for (closed, outcome) in [(false, true), (true, true), (true, false)] {
        let built = scaling::inputs(200, |k| (chain_scope(k), chain(k, closed)));
        let what = match (closed, outcome) {
            (false, _) => "an open chain of choices classified",
            (true, true) => "a closed chain of choices classified, with its message",
            (true, false) => "the opposite of a closed chain, one choice, classified",
        };
        scaling::check_order(what, 200, 1, |k| {
            let (s, t) = &built[&k];
            assert_eq!(s.looped_test(t, outcome).is_some(), closed && outcome);
        });
    }
}
