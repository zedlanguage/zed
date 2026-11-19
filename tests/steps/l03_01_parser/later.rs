//! Name resolution refuses each form of layer L3 that zedc does not support (the displays,
//! `in`, `not in`, `><` and the operator sections are built, plan rows MAP-run and
//! MAP-run-rest; a fold by a function is the checker's to refuse or take); the parser
//! refuses the parts of a `for` and a reduction that belong to later layers.

use super::check as check_sx;
use zed_tests::step_helpers::l02_01_parser_structs::check_refused as check;

#[test]
fn each_form_names_the_step_that_compiles_it() {
    check(&[
        (
            "f(x) = x..;",
            &[concat!(
                zed_tests::not_yet!(
                    "a range with no upper end, `a ..`, read other than by a key, by `in`, \
                     or by `.first`, `.find(p)`, `.any(p)` or `.all(p)` after any number of \
                     `.map(f)` and `.where(p)`,"
                ),
                " [x..]"
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
            "f(m) = for x in m { x };",
            &[concat!(
                zed_tests::not_yet!("a `for`"),
                " [for x in m { x }]"
            )],
        ),
        (
            "f(x) = match x { (0..<10) -> 1, _ -> 0 };",
            &[concat!(
                zed_tests::not_yet!("a `match`"),
                " [match x { (0..<10) -> 1, _ -> 0 }]"
            )],
        ),
        (
            "f(r) = r else #ok(v: (0..<10)) -> 0;",
            &[concat!(
                zed_tests::not_yet!("a range pattern"),
                " [(0..<10)]"
            )],
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
