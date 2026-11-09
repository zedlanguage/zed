//! Name resolution refuses each form of layer L6, naming the step that compiles it, once, and
//! binds the names such a form declares, so that a use of one is not refused as well.

use super::refused;

#[track_caller]
fn check(cases: &[(&str, &[&str])]) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = refused(text);
            (got != want).then(|| format!("{text}\n  got  {got:?}\n  want {want:?}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn each_form_names_the_step_that_compiles_it() {
    check(&[
        (
            "f(n) = loop t { while t < n; };",
            &[concat!(
                zed_tests::not_yet!("a `loop`"),
                " [loop t { while t < n; }]"
            )],
        ),
        (
            "f(c, x) = c || (break x);",
            &[concat!(zed_tests::not_yet!("a `break`"), " [(break x)]")],
        ),
        (
            "f(x) = x*.h;",
            &[concat!(
                zed_tests::not_yet!("a call `*.` that writes its receiver"),
                " [x*.h]"
            )],
        ),
        (
            "f(x) = { mutable y = x; y };",
            &[concat!(
                zed_tests::not_yet!("a `mutable` binding"),
                " [mutable y = x;]"
            )],
        ),
        (
            "f(x) = { while x; 0 };",
            &[concat!(
                zed_tests::not_yet!("a `while` guard"),
                " [while x;]"
            )],
        ),
        (
            "f(x) = { until x; 0 };",
            &[concat!(
                zed_tests::not_yet!("an `until` guard"),
                " [until x;]"
            )],
        ),
        (
            "f(x) = { g(x); 0 };",
            &[concat!(
                zed_tests::not_yet!("an expression statement"),
                " [g(x);]"
            )],
        ),
        (
            "f(x) = { out' <- x; 0 };",
            &[concat!(
                zed_tests::not_yet!("a generation push `x' <- e`"),
                " [out' <- x;]"
            )],
        ),
        (
            "cdf[i] = cdf[i - 1] + 1;",
            &[concat!(
                zed_tests::not_yet!("an indexed definition"),
                " [cdf[i] = cdf[i - 1] + 1;]"
            )],
        ),
        (
            "x = 1 with x = 0;",
            &[concat!(
                zed_tests::not_yet!("a boundary `with`"),
                " [x = 1 with x = 0;]"
            )],
        ),
        (
            "f(x) = x' + 1;",
            &[concat!(
                zed_tests::not_yet!("the primed name `x'`"),
                " [x']"
            )],
        ),
        (
            "x' = 1;",
            &[concat!(
                zed_tests::not_yet!("the primed name `x'`"),
                " [x' = 1;]"
            )],
        ),
        (
            "f(c) = c.y';",
            &[concat!(
                zed_tests::not_yet!("the primed field `y'`"),
                " [c.y']"
            )],
        ),
    ]);
}

/// The names an L6 form declares are bound, once per indexed family, so their uses resolve;
/// a primed name in a form refused whole is not reported again.
#[test]
fn declared_names_are_bound_and_refused_once() {
    check(&[
        (
            "x[i in 0..<4] = i;\nx[i in 4..<8] = 0;\ny = x;",
            &[
                concat!(
                    zed_tests::not_yet!("an indexed definition"),
                    " [x[i in 0..<4] = i;]"
                ),
                concat!(
                    zed_tests::not_yet!("an indexed definition"),
                    " [x[i in 4..<8] = 0;]"
                ),
            ],
        ),
        (
            "a', b = (1, 2) with a = 0;\nc = b;",
            &[concat!(
                zed_tests::not_yet!("a boundary `with`"),
                " [a', b = (1, 2) with a = 0;]"
            )],
        ),
        (
            "f(x) = { mutable y' = x; 0 };",
            &[concat!(
                zed_tests::not_yet!("a `mutable` binding"),
                " [mutable y' = x;]"
            )],
        ),
        (
            "x = 1;\nx[0] = 2;",
            &[
                "`x` is already bound in this scope, and a scope binds each name once [x[0] = 2;]",
                concat!(zed_tests::not_yet!("an indexed definition"), " [x[0] = 2;]"),
            ],
        ),
    ]);
}
