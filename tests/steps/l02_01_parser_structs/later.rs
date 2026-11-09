//! The parser builds every L2 form of this step; name resolution refuses each one, with the
//! step that compiles it, until that step is built. Since step L2.3 resolution also reads the
//! names in them: a method of a type no declaration names, `this` outside a method.

use super::refused;

#[test]
fn each_form_names_the_step_that_compiles_it() {
    let cases: &[(&str, &[&str])] = &[
        (
            "struct Point { x: f64, y: f64 }",
            &[concat!(
                zed_tests::not_yet!("a struct declaration"),
                " [struct Point { x: f64, y: f64 }]"
            )],
        ),
        (
            "Point.norm = 1;",
            &[
                concat!(zed_tests::not_yet!("a method"), " [Point.norm = 1;]"),
                "the type `Point` is not defined: no type in scope has this name, and the prelude has none. Correct the name if it is misspelled, or write a type of the prelude, such as `int` or `String`. [Point.norm = 1;]",
            ],
        ),
        (
            "type Pos = { x: f64 };",
            &[
                concat!(
                    zed_tests::not_yet!("a type declaration"),
                    " [type Pos = { x: f64 };]"
                ),
                concat!(zed_tests::not_yet!("a record type"), " [{ x: f64 }]"),
            ],
        ),
        (
            "p = { x: 1 };",
            &[concat!(
                zed_tests::not_yet!("a record display"),
                " [{ x: 1 }]"
            )],
        ),
        (
            "q = 1 with { x = 2 };",
            &[concat!(
                zed_tests::not_yet!("a `with` clause"),
                " [1 with { x = 2 }]"
            )],
        ),
        (
            "f(x) = this;",
            &[
                concat!(zed_tests::not_yet!("`this`"), " [this]"),
                "`this` stands outside a method: it names the receiver of a method `T.m(…) = …`, \
                 in the method's body [this]",
            ],
        ),
        (
            "f = ((a, b)) -> a;",
            &[concat!(
                zed_tests::not_yet!("a tuple-destructuring parameter"),
                " [(a, b)]"
            )],
        ),
        (
            "g(r) = r else #hit(_) -> 0;",
            &[concat!(
                zed_tests::not_yet!("a struct, name, `_` or tuple pattern"),
                " [_]"
            )],
        ),
        (
            "f(t: Tree(int)) = t;",
            &[
                "the type `Tree` is not defined: no type in scope has this name, and the prelude has none. Correct the name if it is misspelled, or write a type of the prelude, such as `int` or `String`. [Tree]",
                concat!(zed_tests::not_yet!("an applied type"), " [Tree(int)]"),
            ],
        ),
        (
            "f(t: #node(l: int)) = t;",
            &[concat!(
                zed_tests::not_yet!("an atom type with a payload"),
                " [#node(l: int)]"
            )],
        ),
        (
            "f(t: { x: int }) = t;",
            &[concat!(
                zed_tests::not_yet!("a record type"),
                " [{ x: int }]"
            )],
        ),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = refused(text);
            (got != want).then(|| format!("{text}\n  got  {got:?}\n  want {want:?}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
