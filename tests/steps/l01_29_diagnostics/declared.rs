//! The step that shows where a function is declared (DESIGN.md sec:diagnostics,
//! MSG-declared-inferred-sig). A declaration writes no result type at L1, so its type is the one
//! the checker found: the step says so and names the parameters written with no type. A variable
//! of that type which stands in two places or more is written by name, so the type shows which
//! places have the same type at each call (UNDERSCORE-print). Before MSG-declared-inferred-sig,
//! the step for `k(x, y) = y` was "`k` is declared here, `(_, _) -> _`"; before
//! UNDERSCORE-print, it said in words that `y` and the result have the same type.

use super::tyvars::writes_back;
use super::{rejected, steps};

/// The step of the rejection of `src` that says `name` is declared there.
fn declared_step(src: &str, name: &str) -> String {
    let out = rejected(src);
    let head = format!("`{name}` is declared here");
    let found: Vec<&str> = steps(&out)
        .into_iter()
        .filter(|s| s.starts_with(&head))
        .collect();
    assert_eq!(found.len(), 1, "{out}");
    found[0].into()
}

/// The type the step `step` shows: the text between the backquotes after `is`.
fn type_shown(step: &str) -> &str {
    let (_, rest) = step.split_once("` is `").expect("the type found");
    &rest[..rest.find('`').expect("its end")]
}

#[test]
fn a_declaration_with_no_types_shows_the_type_found_with_the_places_that_share_one_named() {
    // The case reported: the call passes on "s" through `k`, which `take` refuses.
    let step = declared_step(
        "k(positional x, positional y) = y;\ntake(positional x: int) = x;\n\
         f(positional h: (int) -> Never) = take(k(h(1), \"s\"));\n",
        "k",
    );
    assert_eq!(
        step,
        "`k` is declared here with no type written for `x`, `y` or its result; the type the \
         checker found for `k` is `(_, T) -> T`"
    );
    writes_back(type_shown(&step));
    // Each variable that stands in two places or more gets its own name, in the order first
    // written.
    let step = declared_step(
        "both(positional x, positional y) = (y, x, y);\ntake(positional p: int) = p;\n\
         m = take(both(1, 2));\n",
        "both",
    );
    assert_eq!(
        step,
        "`both` is declared here with no type written for `x`, `y` or its result; the type the \
         checker found for `both` is `(T, U) -> (U, T, U)`"
    );
    writes_back(type_shown(&step));
}

#[test]
fn a_declaration_with_some_types_names_only_the_parameters_written_without_one() {
    let step = declared_step(
        "tag(positional x: int, positional label) = (x, label);\n\
         take(positional p: (int, int)) = p;\nm = take(tag(1, \"s\"));\n",
        "tag",
    );
    assert_eq!(
        step,
        "`tag` is declared here with no type written for `label` or its result; the type the \
         checker found for `tag` is `(int, T) -> (int, T)`"
    );
    writes_back(type_shown(&step));
    // Every parameter typed: only the result was not written, and the type found for it is
    // the parameter's.
    let step = declared_step("take(positional x: int) = x;\nm = take(\"s\");\n", "take");
    assert_eq!(
        step,
        "`take` is declared here with no type written for its result; the type the checker found \
         for `take` is `(int) -> int`"
    );
}

#[test]
fn a_type_found_that_relates_nothing_through_an_unbounded_variable_prints_it_as_every_value() {
    // A variable bounded by carriers is written by name, with its bounds clause, so the type
    // itself shows the places it ties.
    let step = declared_step(
        "dbl(positional x) = x * 2;\ntake(positional p: String) = p;\nm = take(dbl(3));\n",
        "dbl",
    );
    assert_eq!(
        step,
        "`dbl` is declared here with no type written for `x` or its result; the type the checker \
         found for `dbl` is `(T) -> T for T in int | f32 | f64 | rat`"
    );
    // A parameter that reaches no other place.
    let step = declared_step(
        "f(positional h) = 0;\ntake(positional p: String) = p;\nm = take(f(1));\n",
        "f",
    );
    assert_eq!(
        step,
        "`f` is declared here with no type written for `h` or its result; the type the checker \
         found for `f` is `(_) -> 0`"
    );
    // A parameter read only through a use: its variable stands in the use's need, not in
    // another place of the type.
    let step = declared_step(
        "swap(positional p) = (p[1], p[0]);\ntake(positional x: (int, int)) = x;\n\
         m(positional n: int) = take(swap((n, \"s\")));\n",
        "swap",
    );
    assert_eq!(
        step,
        "`swap` is declared here with no type written for `p` or its result; the type the \
         checker found for `swap` is `(_) -> (_, _)`"
    );
}

/// A function of `n` untyped parameters that returns them all in a tuple, and a call of it that
/// `take` refuses: its declared step names the variable of each parameter.
pub(super) fn wide(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let ps: Vec<String> = xs.iter().map(|x| format!("positional {x}")).collect();
    let args = vec!["1"; n].join(", ");
    format!(
        "all({}) = ({});\ntake(positional p: int) = p;\nm = take(all({args}));\n",
        ps.join(", "),
        xs.join(", ")
    )
}

/// The type the step of [`wide`] shows: `n` variables, named `T`, `U`, `V`, `W`, `T5`, … in
/// order, each in a parameter and in the result.
fn wide_type(n: usize) -> String {
    let names: Vec<String> = (0..n)
        .map(|i| match i {
            0..4 => ["T", "U", "V", "W"][i].to_string(),
            _ => format!("T{}", i + 1),
        })
        .collect();
    format!("({0}) -> ({0})", names.join(", "))
}

/// The rejection of [`wide`]`(n)` shows the type found for `all`: [`wide_type`]`(n)`.
pub(super) fn the_declared_step_of_wide(src: &str, n: usize) {
    let out = rejected(src);
    let want = format!("the type the checker found for `all` is `{}`", wide_type(n));
    assert!(out.contains(&want), "{n}");
}

#[test]
fn the_declared_step_of_a_function_of_many_parameters() {
    let step = declared_step(&wide(4), "all");
    assert_eq!(type_shown(&step), "(T, U, V, W) -> (T, U, V, W)");
    let step = declared_step(&wide(6), "all");
    assert_eq!(type_shown(&step), wide_type(6));
    assert_eq!(wide_type(6), "(T, U, V, W, T5, T6) -> (T, U, V, W, T5, T6)");
    writes_back(type_shown(&step));
    for n in [2, 5, 12] {
        the_declared_step_of_wide(&wide(n), n);
    }
}
