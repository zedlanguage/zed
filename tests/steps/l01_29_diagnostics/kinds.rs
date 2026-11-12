//! The kind-wide types `#_` (every atom) and `(..)` (every tuple) of step L1.40d, checked at the
//! surface: source text through zedc, run, tested and typed as a user writes it (test audit
//! 2026-11-08, row 14). The empty tuple is the value of a block that exports nothing,
//! `nothing()` below: `()` in an expression is only a lambda's empty parameter list.

use super::rejected;
use zed_tests::step_helpers::l01_19a_command_line::run;
use zed_tests::step_helpers::l01_26_type_resolution::sig;

/// A function whose result is the empty tuple.
const NOTHING: &str = "nothing() {\n}\n";

/// A `main` for a file of definitions that `zedc run` would load.
const MAIN: &str = "main(m: MainArgs) {\n  m.stdout <- \"ok\";\n}\n";

#[test]
fn zedc_run_answers_each_kind_test() {
    // The false rows catch a check that answers true for every value.
    let src = format!(
        "{NOTHING}main(m: MainArgs) {{\n  \
         m.stdout <- \"${{#e(1) is #_}} ${{#e(1) is #e}} ${{#e(1) is (..)}} \
         ${{nothing() is (..)}} ${{nothing() is #_}} ${{(1, 2) is (..)}} ${{#e is #_}}\";\n}}\n"
    );
    let out = run("kinds", &src, &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "true false false true false true true\n", ""),
        "{src}"
    );
}

#[test]
fn zedc_test_passes_each_kind_row() {
    let src = format!(
        "{NOTHING}k(positional v) = (v is #_, v is (..))\ntest {{\n  \
         #e(1) -> (true, false),\n  #e -> (true, false),\n  nothing() -> (false, true),\n  \
         (1,) -> (false, true),\n  7 -> (false, false),\n}}\n"
    );
    let outcomes = zedc::testing::test(&src);
    assert_eq!(outcomes.len(), 5, "{src}");
    for o in outcomes {
        assert_eq!(o.failure, None, "row at {}:{}", o.line, o.col);
    }
    // A wrong row fails: the table is checked, not passed blindly.
    let wrong = format!("{NOTHING}k(positional v) = v is (..)\ntest {{\n  #e(1) -> true,\n}}\n");
    let outcomes = zedc::testing::test(&wrong);
    assert!(
        outcomes.len() == 1 && outcomes[0].failure.is_some(),
        "{outcomes:?}"
    );
}

#[test]
fn kind_tests_and_their_operands_have_pinned_types() {
    let f = |body: &str| sig(&format!("{NOTHING}f(positional x: int) = {body};\n"), "f");
    assert_eq!(f("#e(x) is #_"), "(int) -> bool");
    assert_eq!(f("nothing() is (..)"), "(int) -> bool");
    assert_eq!(f("#e(x)"), "(int) -> #e(int)");
    assert_eq!(f("nothing()"), "(int) -> ()");
    assert_eq!(
        f("if x > 0 { #e(x) } else { nothing() }"),
        "(int) -> () | #e(int)"
    );
}

#[test]
fn a_kind_test_narrows_to_its_kind() {
    // Each test keeps exactly the members of its kind: a narrowing that kept both or
    // neither would print another type.
    let f = |test: &str| {
        sig(
            &format!(
                "{NOTHING}f(positional x: int) {{\n  \
                 v = if x > 0 {{ #e(x) }} else {{ nothing() }};\n  \
                 return if v is {test} {{ v }} else {{ #no }};\n}}\n"
            ),
            "f",
        )
    };
    assert_eq!(f("#_"), "(int) -> #e(int) | #no");
    assert_eq!(f("(..)"), "(int) -> () | #no");
    assert_eq!(
        sig("f(positional v) = if v is #_ { v } else { #no };\n", "f"),
        "(_) -> #_"
    );
    assert_eq!(
        sig("f(positional v) = if v is (..) { v } else { #no };\n", "f"),
        "(_) -> (..) | #no"
    );
}

#[test]
fn an_empty_tuple_is_not_written_as_parentheses() {
    // DESIGN's grammar has no `()` expression: before `is` it can only open a lambda.
    let out = rejected("f(positional x: int) = () is (..);\n");
    assert!(out.contains("Syntax error at `is`"), "{out}");
}

#[test]
fn an_atom_with_an_empty_payload_is_refused_for_now() {
    // `#e()` and `#e` are different types, but zedc would run `#e()` as `#e`: here the
    // checker types the "bare" branch dead and the run took it. Refused, the program cannot
    // run with a wrong answer.
    let src = "f(positional n: int) {\n  x = if n > 0 { #e() } else { 7 };\n  \
               return if x is #e { \"bare\" } else { x };\n}\n";
    let out = rejected(&format!("{src}{MAIN}"));
    assert!(
        out.contains(
            "an atom with an empty payload, `#e()`, is part of the Zed language, and this \
             version of zedc does not compile it yet"
        ),
        "{out}"
    );
    // The refusal is the empty payload only: the bare atom, a payload by position or by
    // name, and `...` keep their own answers.
    for ok in [
        "f(positional n: int) = #e;\n",
        "f(positional n: int) = #e(n);\n",
        "f(positional n: int) = #e(k: n);\n",
    ] {
        let ok = format!("{ok}{MAIN}");
        assert!(zedc::run::load(ok.as_bytes()).is_ok(), "{ok}");
    }
    let curried = rejected(&format!("f(positional n: int) = #e(...);\n{MAIN}"));
    assert!(!curried.contains("empty payload"), "{curried}");
    // zedc run refuses it too, before running anything.
    let src = "main(m: MainArgs) {\n  m.stdout <- \"${#e() is #e}\";\n}\n";
    let out = run("empty-payload", src, &[]);
    assert!(
        out.status != 0 && out.stdout.is_empty() && out.stderr.contains("`#e()`"),
        "{} {} {}",
        out.status,
        out.stdout,
        out.stderr
    );
}
