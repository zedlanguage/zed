//! Name resolution refuses each form of layer L3, naming the step that compiles it; the parser
//! refuses the parts of a `for` and a reduction that belong to later layers.

use super::{check as check_sx, refused};

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
            "f(x) = 0..<x;",
            &[concat!(zed_tests::not_yet!("a range"), " [0..<x]")],
        ),
        (
            "f(x, s) = x not in s;",
            &[concat!(
                zed_tests::not_yet!("an `in` test"),
                " [x not in s]"
            )],
        ),
        (
            "f(m, g) = m >< g;",
            &[concat!(
                zed_tests::not_yet!("a reduction `><`"),
                " [m >< g]"
            )],
        ),
        (
            "f(x) = x::len;",
            &[concat!(
                zed_tests::not_yet!("a metadata read `::`"),
                " [x::len]"
            )],
        ),
        (
            "f(x) = (+);",
            &[concat!(
                zed_tests::not_yet!("an operator section"),
                " [(+)]"
            )],
        ),
        (
            "f(x) = [x];",
            &[concat!(zed_tests::not_yet!("an array display"), " [[x]]")],
        ),
        (
            "f(x) = { x };",
            &[concat!(zed_tests::not_yet!("a set display"), " [{ x }]")],
        ),
        (
            "f(x) = {};",
            &[concat!(zed_tests::not_yet!("a map display"), " [{}]")],
        ),
        (
            "f(x) = { x -> 1 };",
            &[concat!(
                zed_tests::not_yet!("a map display"),
                " [{ x -> 1 }]"
            )],
        ),
        (
            "f(m) = for x in m { x };",
            &[concat!(
                zed_tests::not_yet!("a `for`"),
                " [for x in m { x }]"
            )],
        ),
        (
            "f(x) = match x { 0..<10 -> 1, _ -> 0 };",
            &[concat!(
                zed_tests::not_yet!("a `match`"),
                " [match x { 0..<10 -> 1, _ -> 0 }]"
            )],
        ),
        (
            "f(r) = r else #ok(v: 0..<10) -> 0;",
            &[concat!(zed_tests::not_yet!("a range pattern"), " [0..<10]")],
        ),
        (
            "f(x: [int]) = x;",
            &[concat!(
                zed_tests::not_yet!("a family type `[T]`"),
                " [[int]]"
            )],
        ),
        (
            "f(x: [int]) = [x];",
            &[
                concat!(zed_tests::not_yet!("a family type `[T]`"), " [[int]]"),
                concat!(zed_tests::not_yet!("an array display"), " [[x]]"),
            ],
        ),
    ]);
}

#[test]
fn later_parts_are_refused_as_not_compiled_yet() {
    check_sx(&[
        (
            "f(m) = for x in m, y in m { x };",
            concat!(
                "error: ",
                zed_tests::not_yet!("the inner generator `, y in m`")
            ),
        ),
        (
            "f(m) = m >< (+) unordered;",
            concat!(
                "error: ",
                zed_tests::not_yet!("the reduction order `unordered`")
            ),
        ),
        (
            "f(m) = for x in m { g(x); };",
            "error: this block exports nothing, and a block gives a value, so it must export one. \
             End it with an expression, or with `return e;` to give the value `e`.",
        ),
    ]);
}
