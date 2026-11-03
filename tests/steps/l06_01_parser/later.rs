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
            &["a `loop` is compiled from step L6.3 [loop t { while t < n; }]"],
        ),
        (
            "f(c, x) = c || (break x);",
            &["a `break` is compiled from step L6.3 [(break x)]"],
        ),
        (
            "f(x) = x*.h;",
            &["a call `*.` that writes its receiver is compiled from step L6.3 [x*.h]"],
        ),
        (
            "f(x) = { mutable y = x; y };",
            &["a `mutable` binding is compiled from step L6.3 [mutable y = x;]"],
        ),
        (
            "f(x) = { while x; 0 };",
            &["a `while` guard is compiled from step L6.3 [while x;]"],
        ),
        (
            "f(x) = { until x; 0 };",
            &["an `until` guard is compiled from step L6.3 [until x;]"],
        ),
        (
            "f(x) = { g(x); 0 };",
            &["an expression statement is compiled from step L6.3 [g(x);]"],
        ),
        (
            "f(x) = { out' <- x; 0 };",
            &["a generation push `x' <- e` is compiled from step L6.3 [out' <- x;]"],
        ),
        (
            "cdf[i] = cdf[i - 1] + 1;",
            &["an indexed definition is compiled from step L6.2 [cdf[i] = cdf[i - 1] + 1;]"],
        ),
        (
            "x = 1 with x = 0;",
            &["a boundary `with` is compiled from step L6.2 [x = 1 with x = 0;]"],
        ),
        (
            "f(x) = x' + 1;",
            &["the primed name `x'` is compiled from step L6.3 [x']"],
        ),
        (
            "x' = 1;",
            &["the primed name `x'` is compiled from step L6.3 [x' = 1;]"],
        ),
        (
            "f(c) = c.y';",
            &["the primed field `y'` is compiled from step L6.3 [c.y']"],
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
                "an indexed definition is compiled from step L6.2 [x[i in 0..<4] = i;]",
                "an indexed definition is compiled from step L6.2 [x[i in 4..<8] = 0;]",
            ],
        ),
        (
            "a', b = (1, 2) with a = 0;\nc = b;",
            &["a boundary `with` is compiled from step L6.2 [a', b = (1, 2) with a = 0;]"],
        ),
        (
            "f(x) = { mutable y' = x; 0 };",
            &["a `mutable` binding is compiled from step L6.3 [mutable y' = x;]"],
        ),
        (
            "x = 1;\nx[0] = 2;",
            &[
                "`x` is already bound in this scope [x[0] = 2;]",
                "an indexed definition is compiled from step L6.2 [x[0] = 2;]",
            ],
        ),
    ]);
}
