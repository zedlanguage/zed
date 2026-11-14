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
    assert_eq!(f("#e(x) is #_"), "int -> bool");
    assert_eq!(f("nothing() is (..)"), "int -> bool");
    assert_eq!(f("#e(x)"), "int -> #e(int)");
    assert_eq!(f("nothing()"), "int -> ()");
    assert_eq!(
        f("if x > 0 { #e(x) } else { nothing() }"),
        "int -> () | #e(int)"
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
    assert_eq!(f("#_"), "int -> #e(int) | #no");
    assert_eq!(f("(..)"), "int -> () | #no");
    assert_eq!(
        sig("f(positional v) = if v is #_ { v } else { #no };\n", "f"),
        "_ -> #_"
    );
    assert_eq!(
        sig("f(positional v) = if v is (..) { v } else { #no };\n", "f"),
        "_ -> (..) | #no"
    );
}

#[test]
fn an_empty_tuple_is_not_written_as_parentheses() {
    // DESIGN's grammar has no `()` expression: before `is` it can only open a lambda.
    let out = rejected("f(positional x: int) = () is (..);\n");
    assert!(out.contains("Syntax error at `is`"), "{out}");
}

/// A program whose `f(1)` is `#e()` and `f(0)` is the bare `#e`, printing which branch of
/// `x is #e` each takes; the checker types `#e()` apart from `#e`, so it is not the bare one.
const EMPTY_PAYLOAD: &str = "\
f(positional n: int) {
  x = if n > 0 { #e() } else { #e };
  return if x is #e { \"bare\" } else { \"not bare\" };
}
main(m: MainArgs) {
  m.stdout <- \"${f(1)} ${f(0)} ${#e() is #e} ${#e() == #e} ${#e() == #e()} ${#e is #e} \
     ${(#e(), #e, #e(1))}\";
}
";

/// What `EMPTY_PAYLOAD` prints, under `zedc run` and built.
const EMPTY_PAYLOAD_OUT: &str = "not bare bare false false true true (#e(), #e, #e(1))\n";

#[test]
fn an_atom_with_an_empty_payload_is_a_value_of_its_own() {
    // `#e()` is not `#e`: a run that built `#e()` as `#e` took the "bare" branch and found the
    // two equal, and a printer that dropped the parentheses printed `(#e, #e, #e(1))`.
    let out = run("empty-payload", EMPTY_PAYLOAD, &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, EMPTY_PAYLOAD_OUT, ""),
        "{EMPTY_PAYLOAD}"
    );
    // The bare atom, a payload by position or by name, and `...` keep their own answers.
    for ok in [
        "f(positional n: int) = #e;\n",
        "f(positional n: int) = #e();\n",
        "f(positional n: int) = #e(n);\n",
        "f(positional n: int) = #e(k: n);\n",
    ] {
        let ok = format!("{ok}{MAIN}");
        assert!(zedc::run::load(ok.as_bytes()).is_ok(), "{ok}");
    }
    let curried = rejected(&format!("f(positional n: int) = #e(...);\n{MAIN}"));
    assert!(!curried.contains("empty payload"), "{curried}");
}

#[test]
fn zedc_test_tells_an_empty_payload_from_the_bare_atom() {
    // The passing rows catch a run that cannot build `#e()`; the failing rows catch one that
    // builds it as `#e`, and their messages print each as itself.
    let src = "g(positional n: int) = if n > 0 { #e() } else { #e }\n\
               test {\n  1 -> #e(),\n  0 -> #e,\n  1 -> #e,\n  0 -> #e(),\n}\n";
    let failures: Vec<Option<String>> = zedc::testing::test(src)
        .into_iter()
        .map(|o| o.failure)
        .collect();
    assert_eq!(failures.len(), 4, "{src}");
    assert_eq!(failures[..2], [None, None], "{src}");
    let (third, fourth) = (failures[2].as_deref(), failures[3].as_deref());
    assert!(
        third.is_some_and(|f| f.contains("the result is #e()")),
        "{third:?}"
    );
    assert!(
        fourth.is_some_and(|f| f.contains("the result is #e") && !f.contains("the result is #e()")),
        "{fourth:?}"
    );
}
