//! Plan row TYPEVAR-names (QUESTIONS Q23, author 2026-11-15): a type variable is exactly a name
//! of the form `[A-Z][0-9]*` (`T`, `X`, `T1`), decided when the tree is analyzed, not by the
//! lexer (DESIGN.md sec:type_language, rule 4). Any other capitalized name in a type that names
//! no type is a misspelling, rejected with the nearest type name as its menu, and never read
//! as a type variable; a name of the form declared as anything but a type variable is
//! rejected; a type variable written once in a signature and nowhere in the body is rejected
//! (DESIGN.md sec:diagnostics, the rows from "Type variable" on; L2.12's tests).

use crate::rejected;

/// Whether the program `src` loads with no error.
fn accepted(src: &str) {
    if let Err(e) = zedc::run::load(src.as_bytes()) {
        panic!("rejected:\n{src}\n{e}");
    }
}

/// Asserts that the rejection of `src` holds each of `parts`.
fn rejects(src: &str, parts: &[&str]) -> String {
    let out = rejected(src);
    for p in parts {
        assert!(
            out.contains(p),
            "{p:?} missing from the rejection of\n{src}\n{out}"
        );
    }
    out
}

/// The repairs name resolution offers for `src`, before the front end checks them: the menu
/// it would give were the definition shown to check with it.
fn offered(src: &str) -> Vec<String> {
    let tokens = zedc::lex::lex(src).unwrap();
    let tree = zedc::parse::parse(src, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(src, &tokens, &tree).unwrap();
    let errors = zedc::resolve::resolve_text(&stmts, Some(src))
        .err()
        .unwrap_or_default();
    (errors.iter())
        .flat_map(|e| &e.notes)
        .filter(|n| n.text.starts_with("repair: "))
        .map(|n| n.text.clone())
        .collect()
}

#[test]
fn a_misspelled_type_gets_the_nearest_type_and_is_no_type_variable() {
    let out = rejects(
        "f(c: Strng) = 0;\nmain() = 0;\n",
        &["1:6: The type `Strng` is not defined.", "repair: `String`"],
    );
    assert!(!out.contains("type variable"), "{out}");
    accepted("f(c: String) = 0;\nmain() = 0;\n");
}

/// DESIGN.md offers the nearest type name "only when the definition then checks", and the
/// front end compiles the unit with the repair made to show it (`front::menus_checked`). A
/// struct is not compiled yet, so a definition whose repair names one is not shown to check
/// and gets no menu; nor does one whose body then fails, nor one in a unit that has another
/// error, which the repair leaves.
#[test]
fn the_nearest_type_is_offered_only_when_the_definition_then_checks() {
    for src in [
        "struct Config { a: int }\nf(c: Confg) = 0;\nmain() = 0;\n",
        "f(c: Strng) = c + 1;\nmain() = 0;\n",
        "f(c: Strng) = 0;\ng = 1 + \"a\";\nmain() = 0;\n",
    ] {
        assert!(!offered(src).is_empty(), "{src}");
        let out = rejected(src);
        assert!(out.contains("is not defined."), "{out}");
        assert!(!out.contains("repair: `"), "{out}");
    }
}

/// The same for the menu of a type variable written once: the parameter with its type
/// dropped, offered only when the definition then checks.
#[test]
fn the_untyped_parameter_is_offered_only_when_the_definition_then_checks() {
    accepted("f(c) = 0;\nmain() = 0;\n");
    for src in [
        "f(c: T) = 0;\ng = 1 + \"a\";\nmain() = 0;\n",
        "struct Pt { a: int }\nf(c: T) = 0;\nmain() = 0;\n",
    ] {
        assert_eq!(offered(src), ["repair: `c`"], "{src}");
        let out = rejected(src);
        assert!(
            out.contains("The type variable `T` is written once"),
            "{out}"
        );
        assert!(!out.contains("repair: `c`"), "{out}");
    }
}

#[test]
fn a_type_variable_written_once_is_rejected_with_the_parameter_untyped() {
    rejects(
        "f(c: T) = 0;\nmain() = 0;\n",
        &[
            "1:6: The type variable `T` is written once in this signature and nowhere in its body.",
            "repair: `c`",
        ],
    );
}

#[test]
fn a_parameter_with_a_default_keeps_it_in_the_repair() {
    rejects(
        "f(c: T = 3) = 0;\nmain() = 0;\n",
        &["The type variable `T` is written once", "repair: `c = …`"],
    );
}

#[test]
fn a_type_variable_written_once_inside_a_type_gets_no_menu() {
    let out = rejects(
        "f(c: (T) -> int) = 0;\nmain() = 0;\n",
        &[
            "The type variable `T` is written once",
            "`_` in place of `T` is part of the Zed language",
        ],
    );
    assert!(!out.contains("repair:"), "{out}");
}

#[test]
fn a_type_variable_written_twice_is_accepted() {
    accepted("pair(x: T, y: T) = (x, y);\nmain() = 0;\n");
    accepted("pair(x: T, y: T) = x;\nmain() = pair(x: 1, y: 2);\n");
    accepted("f(x: (T) -> T) = 0;\nmain() = 0;\n");
}

#[test]
fn a_type_variable_the_body_reads_is_accepted() {
    accepted("f(x: T) = { g = (y: T) -> y; g(x) };\nmain() = 0;\n");
}

#[test]
fn a_value_named_like_a_type_variable_is_rejected_with_the_lowercase_name() {
    rejects(
        "R = 1;\nmain() = 0;\n",
        &[
            "1:1: The binding target `R` has the form of a type variable.",
            "repair: `r = 1;`",
        ],
    );
    rejects(
        "R' = 2;\nmain() = 0;\n",
        &[
            "1:1: The binding target `R'` has the form of a type variable.",
            "repair: `r' = 2;`",
        ],
    );
    rejects(
        "f(T1: int) = 0;\nmain() = 0;\n",
        &[
            "1:3: The parameter `T1` has the form of a type variable.",
            "repair: `t1: int`",
        ],
    );
}

#[test]
fn a_function_named_like_a_type_variable_is_rejected() {
    rejects(
        "F(x: int) = x;\nmain() = 0;\n",
        &[
            "The function `F` has the form of a type variable.",
            "repair: `f(x: int) = x;`",
        ],
    );
}

#[test]
fn the_lowercase_name_in_use_is_not_offered() {
    let out = rejects(
        "r = 0;\nR = 1;\nmain() = 0;\n",
        &[
            "2:1: The binding target `R` has the form of a type variable.",
            "repair: rename the binding target; `r` already names something in scope",
        ],
    );
    assert!(!out.contains("repair: `r = 1;`"), "{out}");
}

#[test]
fn a_struct_named_like_a_type_variable_is_rejected_and_its_name_stays_a_variable() {
    let out = rejects(
        "struct T2 { a: int }\ng(x: T2, y: T2) = x;\nmain() = 0;\n",
        &[
            "1:1: The struct `T2` has the form of a type variable.",
            "repair: give the struct a longer name",
        ],
    );
    // `T2` in `g` is a type variable, written twice, not a use of the struct.
    assert!(!out.contains("2:"), "{out}");
}

#[test]
fn names_near_the_form_are_types_or_misspellings() {
    // `Tx` and `AB` are not of the form: they name no type, so each is unknown, and no type
    // name is one slip from either, so neither gets a menu.
    for n in ["Tx", "AB"] {
        let out = rejects(
            &format!("f(c: {n}) = 0;\nmain() = 0;\n"),
            &[&format!("The type `{n}` is not defined.")],
        );
        assert!(!out.contains("repair:"), "{out}");
    }
    // `T01` is of the form: a capital letter followed only by digits.
    accepted("pair(x: T01, y: T01) = x;\nmain() = 0;\n");
}

#[test]
fn a_struct_field_names_no_type_variable_and_is_not_named_like_one() {
    rejects(
        "struct Box { a: T }\nmain() = 0;\n",
        &[
            "1:17: The type variable `T` stands in a field of a struct that declares no type parameter `T`.",
        ],
    );
    rejects(
        "struct Box { A: int }\nmain() = 0;\n",
        &[
            "1:14: The field `A` has the form of a type variable.",
            "repair: `a: int`",
        ],
    );
}

#[test]
fn a_misspelling_written_many_times_is_reported_at_each() {
    let out = rejected("f(a: Confg, b: Confg) = 0;\nmain() = 0;\n");
    assert_eq!(
        out.matches("The type `Confg` is not defined.").count(),
        2,
        "{out}"
    );
}

/// DESIGN.md step L1.29e's examples, at type names: each kind of slip offers `Config` at name
/// resolution, and `String`, a type this zedc compiles, through the front end.
#[test]
fn each_kind_of_slip_offers_the_type() {
    for n in ["Confg", "Configg", "Cinfig", "Cofnig"] {
        let src = format!("struct Config {{ a: int }}\nf(c: {n}) = 0;\nmain() = 0;\n");
        assert_eq!(offered(&src), ["repair: `Config`"], "{src}");
    }
    for n in ["Strng", "Stringg", "Sxring", "Stirng"] {
        rejects(
            &format!("f(c: {n}) = 0;\nmain() = 0;\n"),
            &[
                &format!("The type `{n}` is not defined."),
                "repair: `String`",
            ],
        );
    }
}

#[test]
fn a_name_equal_once_case_and_underscores_are_folded_is_near() {
    let src = "struct MyConfig { a: int }\nf(c: My_config) = 0;\nmain() = 0;\n";
    assert_eq!(offered(src), ["repair: `MyConfig`"]);
    rejects(
        "f(c: S_TRING) = 0;\nmain() = 0;\n",
        &["The type `S_TRING` is not defined.", "repair: `String`"],
    );
}

#[test]
fn of_two_near_types_the_first_in_name_order_is_offered() {
    let src = "struct Cat { a: int }\nstruct Bat { a: int }\nf(c: Hat) = 0;\nmain() = 0;\n";
    assert_eq!(offered(src), ["repair: `Bat`"]);
}

#[test]
fn a_type_two_slips_away_is_not_offered() {
    let out = rejects(
        "struct Config { a: int }\nf(c: Cnfgi) = 0;\nmain() = 0;\n",
        &["The type `Cnfgi` is not defined."],
    );
    assert!(!out.contains("repair:"), "{out}");
}

/// What the program with these definitions writes when `main` writes `out` to `stdout`.
fn writes(defs: &str, out: &str) -> String {
    output(&format!(
        "{defs}\nmain(m: MainArgs) {{\n  m.stdout <- {out};\n}}\n"
    ))
}

/// What the program `src` writes to `stdout`.
fn output(src: &str) -> String {
    let p = zedc::run::load(src.as_bytes()).unwrap_or_else(|e| panic!("rejected:\n{src}\n{e}"));
    let files =
        |_: &str| -> std::sync::Arc<dyn zed_kernel::Lookup> { unreachable!("no `Files` port") };
    match p.run(&std::collections::BTreeMap::new(), files) {
        Ok(w) => w
            .writes
            .iter()
            .map(|(_, b)| String::from_utf8_lossy(b).into_owned())
            .collect(),
        Err(e) => panic!("{src}: run error: {e}"),
    }
}

const MAP2: &str = "map2(xs: T, f: (T) -> T) = f(xs);";
const MAP2_F_FIRST: &str = "map2(f: (T) -> T, xs: T) = f(xs);";
const INC: &str = "inc(positional v: int) = v + 1;";

/// Row FAIL-typevar-free-in-checker: the uses of a type variable in a signature are one
/// type, which each call binds (DESIGN.md sec:type_resolution, rules 2 and 4). `T` is fixed by
/// the arguments that are not lambdas, here the literal `3`, which gives it `int`; the lambda
/// is then checked as `(int) -> int`, and the call gives `int`.
#[test]
fn a_free_type_variable_ties_its_uses_at_a_call() {
    assert_eq!(writes(MAP2, r#""${map2(xs: 3, f: (v) -> v + 1)}""#), "4\n");
    assert_eq!(
        writes(MAP2, r#""${map2(xs: 3, f: (v) -> v + 1) * 2}""#),
        "8\n"
    );
    assert_eq!(
        writes(MAP2, r#""${map2(xs: 3, f: (v: int) -> v * 5)}""#),
        "15\n"
    );
    assert_eq!(
        writes(MAP2, r#""${map2(xs: 2.5, f: (v) -> v + 1.0)}""#),
        "3.5\n"
    );
}

/// The lambda is checked after the other arguments wherever it stands, so its order in the
/// call or the signature does not matter, and a function that is not a lambda binds the same.
#[test]
fn a_free_type_variable_is_bound_in_any_argument_order() {
    let at_a = r#""${{ a = 3 + 0; map2(xs: a, f: (v) -> v * 2) }}""#;
    assert_eq!(writes(MAP2, at_a), "6\n");
    let f_first = r#""${map2(f: (v) -> v + 1, xs: 3)}""#;
    assert_eq!(writes(MAP2_F_FIRST, f_first), "4\n");
    let named = format!("{MAP2}\n{INC}");
    assert_eq!(writes(&named, r#""${map2(xs: 3, f: inc)}""#), "4\n");
    let named_first = format!("{MAP2_F_FIRST}\n{INC}");
    assert_eq!(writes(&named_first, r#""${map2(f: inc, xs: 3)}""#), "4\n");
}

/// A lambda whose result is not the type the variable took is rejected in the variable's
/// type at the call, not in `_`.
#[test]
fn a_lambda_against_a_bound_type_variable_is_checked_at_its_type() {
    let out = rejects(
        &format!("{MAP2}\nmain() = {{ _ = map2(xs: 3, f: (v) -> \"s\"); 0 }};\n"),
        &["the lambda returns \"s\", and `int -> int` returns int"],
    );
    assert!(!out.contains("`_"), "{out}");
}

/// A program whose one call passes `n` lambdas, each at a parameter `gi: (T) -> T`, and the
/// literal `3` at `x: T`; the call gives the last lambda applied to `x`.
pub(crate) fn lambdas_at_one_type_variable(n: usize) -> String {
    let params: String = (0..n).map(|i| format!(", g{i}: (T) -> T")).collect();
    let args: String = (0..n).map(|i| format!(", g{i}: (v) -> v + {i}")).collect();
    let last = n - 1;
    format!(
        "f(x: T{params}) = g{last}(x);\n\
         main(m: MainArgs) {{\n  m.stdout <- \"${{f(x: 3{args})}}\";\n}}\n"
    )
}

/// [`lambdas_at_one_type_variable`] at a small size, the check its benchmark makes besides
/// the ratio: each lambda is checked at `int`, and the call gives `3 + 3`.
#[test]
fn many_lambdas_at_one_type_variable_are_each_checked_at_its_type() {
    assert_eq!(output(&lambdas_at_one_type_variable(4)), "6\n");
}

/// A call of n functions at parameters `(T) -> T`, `T` written nowhere else: the first, a
/// lambda with its parameter's type written, fixes `T` through it, and the rest, lambdas with
/// no written types, are checked at that instance (row FAIL-typevar-fn-only-binding).
pub(crate) fn functions_fix_one_type_variable(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("g{i}: (T) -> T")).collect();
    let args: String = (1..n).map(|i| format!(", g{i}: (v) -> v + {i}")).collect();
    format!(
        "f({}) = 0;\n\
         main(m: MainArgs) {{\n  m.stdout <- \"${{f(g0: (v: int) -> v{args})}}\";\n}}\n",
        params.join(", ")
    )
}

/// [`functions_fix_one_type_variable`] at a small size, the check its benchmark makes besides
/// the ratio.
#[test]
fn many_functions_fix_one_type_variable_through_the_first() {
    assert_eq!(output(&functions_fix_one_type_variable(4)), "0\n");
}

const TO_F64: &str = "h(positional z: f64) = z;";

/// The expected type is matched against the result before the arguments (DESIGN.md
/// sec:type_resolution, rule 2): where `f64` is wanted, `T` is `f64`, the literal `3` takes
/// it and the lambda is checked as `(f64) -> f64`, as `3` alone would take `f64` there.
#[test]
fn the_expected_type_binds_a_type_variable_before_a_literal() {
    let defs = format!("{MAP2}\n{TO_F64}");
    assert_eq!(
        writes(&defs, r#""${h(map2(xs: 3, f: (v) -> v + 1.5))}""#),
        "4.5\n"
    );
    assert_eq!(
        writes(&defs, r#""${h(map2(xs: 3, f: (v) -> v))}""#),
        "3.0\n"
    );
    // Control: where nothing is wanted, the literal fixes `T` at `int`.
    assert_eq!(writes(MAP2, r#""${map2(xs: 3, f: (v) -> v)}""#), "3\n");
}

/// An argument that is not a literal and disagrees with the expected type does not bind
/// `T`; the call is rejected at that argument.
#[test]
fn an_argument_against_the_expected_type_is_rejected() {
    rejects(
        &format!(
            "{MAP2}\n{TO_F64}\nmain() = {{ a = 3 + 0; _ = h(map2(xs: a, f: (v) -> v)); 0 }};\n"
        ),
        &["`map2`"],
    );
}

/// Row FAIL-typevar-fn-only-binding: a type variable written only inside function types of
/// the parameters is fixed by the first function argument that is not a lambda without types
/// (DESIGN.md sec:type_resolution, rule 2), and the rest are checked against that instance.
#[test]
fn a_type_variable_only_inside_function_types_is_bound_by_a_function_argument() {
    const TWO: &str = "two(f: (T) -> T, g: (T) -> T) = 0;";
    let named = format!("{TWO}\n{INC}");
    assert_eq!(writes(&named, r#""${two(f: inc, g: inc)}""#), "0\n");
    assert_eq!(
        writes(TWO, r#""${two(f: (v: int) -> v, g: (v) -> v + 1)}""#),
        "0\n"
    );
}

/// Row FAIL-typevar-named-fn-message: a function whose parameter is named, passed where the
/// instance of a type variable's function type passes by position, gets the reason and the
/// repair a plain function type gives.
#[test]
fn a_named_parameter_at_a_type_variable_s_function_type_gets_the_parameter_message() {
    rejects(
        &format!("{MAP2}\ninc(v: int) = v + 1;\nmain() = {{ _ = map2(xs: 3, f: inc); 0 }};\n"),
        &[
            "the parameters of `inc` (v) do not fit `int -> int`",
            "repair: pass a lambda, `(v) -> inc(v: v)`",
        ],
    );
}

/// Row FAIL-typevar-fn-only-binding: a lambda with written parameter types binds the variable
/// through them; its body then gives what it gives at that instance, so `(v: f64) -> 1` at
/// `(f64) -> f64` gives `1.0`, and a lambda without types after it is checked at the instance.
#[test]
fn a_lambda_with_written_types_binds_a_type_variable_and_the_rest_follow() {
    let two = format!("two(f: (T) -> T, g: (T) -> T) = 0;\n{INC}");
    assert_eq!(
        writes(MAP2, r#""${map2(xs: 2.5, f: (v: f64) -> 1)}""#),
        "1.0\n"
    );
    assert_eq!(
        writes(MAP2, r#""${map2(xs: 3, f: (v: int) -> v * 5)}""#),
        "15\n"
    );
    assert_eq!(writes(&two, r#""${two(f: (v: int) -> v, g: inc)}""#), "0\n");
    assert_eq!(writes(&two, r#""${two(f: (v) -> v, g: inc)}""#), "0\n");
}

/// Row TEST-expected-type-shapes: a type variable bound only through function types, at
/// results of several shapes and with a callee that is itself a call. Where `f64` is wanted,
/// the expected type fixes `T` first (DESIGN.md sec:type_resolution, rule 2), also when the
/// callee is the result of the call `pick(0)`, whose own check came before the call it heads.
#[test]
fn a_type_variable_in_function_types_takes_results_of_each_shape() {
    let defs = format!(
        "{MAP2}\ntwo(x: T, f: (T) -> (T, T)) = f(x);\npair(x: T, f: (T) -> T) = (f(x), x);\n\
         pick(positional n: int) = map2;\nfirst(positional p: (int, int)) = p[0];\n\
         half(positional x: f64) = x / 2.0;\ngreet(positional s: String) = s;"
    );
    let cases = [
        (r#"greet(map2(xs: "b", f: (v) -> v))"#, "b\n"),
        (r#""${pair(x: 2, f: (v) -> v + 1)[0]}""#, "3\n"),
        (r#""${two(x: 1, f: (v) -> (v, v + 1))[1]}""#, "2\n"),
        (r#""${first(two(x: 7, f: (v) -> (v, 1)))}""#, "7\n"),
        (r#""${pick(0)(xs: 2, f: (v) -> v * 3)}""#, "6\n"),
        (r#""${half(map2(xs: 3, f: (v) -> v + 1))}""#, "2.0\n"),
        (r#""${half(pick(0)(xs: 3, f: (v) -> v + 1))}""#, "2.0\n"),
    ];
    for (out, want) in cases {
        assert_eq!(writes(&defs, out), want, "{out}");
    }
}
