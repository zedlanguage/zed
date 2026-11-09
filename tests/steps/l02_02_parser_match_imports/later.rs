//! The parser builds every form of this step; name resolution refuses each one as a form this
//! zedc does not compile yet, and refuses each annotation as not compiled yet, or as no
//! annotation at all.

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
            "import geometry.shapes;",
            &[
                "the unit `geometry.shapes` cannot be imported: no manifest `zed.manifest` marks a \
                 package root at or above this unit, so it imports no unit [import geometry.shapes;]",
                concat!(zed_tests::import_not_yet!(), " [import geometry.shapes;]"),
            ],
        ),
        (
            "size(t) = match t { _ -> 0 };",
            &[concat!(
                zed_tests::not_yet!("a `match`"),
                " [match t { _ -> 0 }]"
            )],
        ),
        (
            "f(r) = r else #ok(v: n is int) -> 0;",
            &[concat!(
                zed_tests::not_yet!("a type pattern `n is T`"),
                " [n is int]"
            )],
        ),
        (
            "g(r) = r else #ok(v: -1) -> 0;",
            &[concat!(zed_tests::not_yet!("a literal pattern"), " [-1]")],
        ),
    ]);
}

#[test]
fn each_annotation_of_a_later_layer_is_not_compiled_yet() {
    check(&[
        (
            "@memoized\nfib(n) = n;",
            &[concat!(
                zed_tests::not_yet!("the annotation `@memoized`"),
                " [@memoized]"
            )],
        ),
        (
            "@log @exact @exhaustive\nf(x) = x;",
            &[
                concat!(zed_tests::not_yet!("the annotation `@log`"), " [@log]"),
                concat!(zed_tests::not_yet!("the annotation `@exact`"), " [@exact]"),
                concat!(
                    zed_tests::not_yet!("the annotation `@exhaustive`"),
                    " [@exhaustive]"
                ),
            ],
        ),
        (
            "@strict @proved\nf(x) = x;",
            &[
                "`@strict` is not an annotation [@strict]",
                "`@proved` is not an annotation [@proved]",
            ],
        ),
        (
            "@hash(\"00\")\nf(x) = x;",
            &["`@hash` pins an import and follows its unit path, as in \
                 `import geometry.shapes @hash(\"…\");`; it annotates no declaration [@hash(\"00\")]"],
        ),
        (
            "@memo\nf(x) = x;",
            &["`@memo` is not an annotation [@memo]"],
        ),
        // The annotated function is still bound: only the annotation is refused.
        (
            "@memoized\nfib(n) = fib(n);\nk = fib(3);",
            &[concat!(
                zed_tests::not_yet!("the annotation `@memoized`"),
                " [@memoized]"
            )],
        ),
        (
            "@decides(p) @require(n > 0)\nf(n) = n;",
            &[
                concat!(
                    zed_tests::not_yet!("the annotation `@decides`"),
                    " [@decides(p)]"
                ),
                concat!(
                    zed_tests::not_yet!("the annotation `@require`"),
                    " [@require(n > 0)]"
                ),
            ],
        ),
    ]);
}
