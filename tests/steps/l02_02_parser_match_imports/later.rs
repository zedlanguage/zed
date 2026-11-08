//! The parser builds every form of this step; name resolution refuses each one, with the step
//! that compiles it, and refuses each annotation with its layer, or as no annotation at all.

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
                "an import is linked from step L2.4, which ties each name it brings in to the \
                 other unit's definition [import geometry.shapes;]",
            ],
        ),
        (
            "size(t) = match t { _ -> 0 };",
            &["a `match` is compiled from step L2.4 [match t { _ -> 0 }]"],
        ),
        (
            "f(r) = r else #ok(v: n is int) -> 0;",
            &["a type pattern `n is T` is compiled from step L2.4 [n is int]"],
        ),
        (
            "g(r) = r else #ok(v: -1) -> 0;",
            &["a literal pattern is compiled from step L2.4 [-1]"],
        ),
    ]);
}

#[test]
fn each_annotation_names_its_layer() {
    check(&[
        (
            "@memoized\nfib(n) = n;",
            &["`@memoized` is an annotation of layer L18 [@memoized]"],
        ),
        (
            "@log @exact @exhaustive\nf(x) = x;",
            &[
                "`@log` is an annotation of layer L7 [@log]",
                "`@exact` is an annotation of layer L15 [@exact]",
                "`@exhaustive` is an annotation of layer L15 [@exhaustive]",
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
            &["`@memoized` is an annotation of layer L18 [@memoized]"],
        ),
        (
            "@decides(p) @require(n > 0)\nf(n) = n;",
            &[
                "`@decides` is an annotation of layer L22 [@decides(p)]",
                "`@require` is an annotation of layer L24 [@require(n > 0)]",
            ],
        ),
    ]);
}
