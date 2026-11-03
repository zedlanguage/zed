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
            &["a range is compiled from step L3.2 [0..<x]"],
        ),
        (
            "f(x, s) = x not in s;",
            &["an `in` test is compiled from step L3.2 [x not in s]"],
        ),
        (
            "f(m) = m >< g;",
            &["a reduction `><` is compiled from step L3.2 [m >< g]"],
        ),
        (
            "f(x) = x::len;",
            &["a metadata read `::` is compiled from step L3.2 [x::len]"],
        ),
        (
            "f(x) = (+);",
            &["an operator section is compiled from step L3.2 [(+)]"],
        ),
        (
            "f(x) = [x];",
            &["an array display is compiled from step L3.2 [[x]]"],
        ),
        (
            "f(x) = { x };",
            &["a set display is compiled from step L3.2 [{ x }]"],
        ),
        (
            "f(x) = {};",
            &["a map display is compiled from step L3.2 [{}]"],
        ),
        (
            "f(x) = { x -> 1 };",
            &["a map display is compiled from step L3.2 [{ x -> 1 }]"],
        ),
        (
            "f(m) = for x in m { x };",
            &["a `for` is compiled from step L3.2 [for x in m { x }]"],
        ),
        (
            "f(x) = match x { 0..<10 -> 1, _ -> 0 };",
            &["a `match` is compiled from step L2.4 [match x { 0..<10 -> 1, _ -> 0 }]"],
        ),
        (
            "f(r) = r else #ok(v: 0..<10) -> 0;",
            &["a range pattern is compiled from step L3.2 [0..<10]"],
        ),
        (
            "f(x: [int]) = x;",
            &["a family type `[T]` is compiled from step L3.2 [[int]]"],
        ),
        (
            "f(x: [int]) = [x];",
            &[
                "a family type `[T]` is compiled from step L3.2 [[int]]",
                "an array display is compiled from step L3.2 [[x]]",
            ],
        ),
    ]);
}

#[test]
fn later_parts_name_their_layer() {
    check_sx(&[
        (
            "f(m) = for x in m, y in m { x };",
            "error: this form (MoreGen) is built from layer L5",
        ),
        (
            "f(m) = m >< (+) unordered;",
            "error: this form (Unordered) is built from layer L9",
        ),
        (
            "f(m) = for x in m { g(x); };",
            "error: this block exports nothing: end it with an expression or `return e;`",
        ),
    ]);
}
