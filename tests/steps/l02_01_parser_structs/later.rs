//! The parser builds every L2 form of this step; name resolution refuses each one, with the
//! step that compiles it, until that step is built. Since step L2.3 resolution also reads the
//! names in them: a method of a type no declaration names, `this` outside a method.

use super::refused;

#[test]
fn each_form_names_the_step_that_compiles_it() {
    let cases: &[(&str, &[&str])] = &[
        (
            "struct Point { x: f64, y: f64 }",
            &["a struct declaration is compiled from step L2.4 [struct Point { x: f64, y: f64 }]"],
        ),
        (
            "Point.norm = 1;",
            &[
                "a method is compiled from step L2.4 [Point.norm = 1;]",
                "the type `Point` is not defined [Point.norm = 1;]",
            ],
        ),
        (
            "type Pos = { x: f64 };",
            &[
                "a type declaration is compiled from step L2.5 [type Pos = { x: f64 };]",
                "a record type is compiled from step L2.5 [{ x: f64 }]",
            ],
        ),
        (
            "p = { x: 1 };",
            &["a record display is compiled from step L2.4 [{ x: 1 }]"],
        ),
        (
            "q = 1 with { x = 2 };",
            &["a `with` clause is compiled from step L2.4 [1 with { x = 2 }]"],
        ),
        (
            "f(x) = this;",
            &[
                "`this` is compiled from step L2.4 [this]",
                "`this` stands outside a method: it names the receiver of a method `T.m(…) = …`, \
                 in the method's body [this]",
            ],
        ),
        (
            "f = ((a, b)) -> a;",
            &["a tuple-destructuring parameter is compiled from step L2.4 [(a, b)]"],
        ),
        (
            "g(r) = r else #hit(_) -> 0;",
            &["a struct, name, `_` or tuple pattern is compiled from step L2.4 [_]"],
        ),
        (
            "f(t: Tree(int)) = t;",
            &[
                "the type `Tree` is not defined [Tree]",
                "an applied type is compiled from step L2.5 [Tree(int)]",
            ],
        ),
        (
            "f(t: #node(l: int)) = t;",
            &["an atom type with a payload is compiled from step L2.5 [#node(l: int)]"],
        ),
        (
            "f(t: { x: int }) = t;",
            &["a record type is compiled from step L2.5 [{ x: int }]"],
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
