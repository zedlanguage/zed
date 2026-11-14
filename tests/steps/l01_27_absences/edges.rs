//! Completeness (row TEST-complete-staging, author P189): `else` in each place an expression
//! may stand, defaults that are themselves atoms or may fail, the pattern form on a merged
//! failure, merges through calls, tuples, unary operators and comparisons, and `_` after each
//! form that passes a loose failure on. The case list is COMPLETENESS.md.

use zedc::rejection::Row;

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{info, sig, type_errors};

/// A lookup's result: a value, a missing row, or a stored NULL.
const LOOKUP: &str = "positional x: int | #notFound | #none";

/// Two parameters, each of which may fail its own way.
const TWO: &str = "positional x: int | #notFound, positional y: int | #none";

/// Calls of `f`, each with the value it gives.
type Calls = &'static [(&'static str, &'static str)];

/// The values of `f` at each argument list of `calls`, each with its case.
fn values(defs: &str, calls: &[(&str, &str)]) {
    let mut run = defs.to_string();
    for (i, (call, _)) in calls.iter().enumerate() {
        run.push_str(&format!("v{i} = {call};\n"));
    }
    for (i, (call, want)) in calls.iter().enumerate() {
        assert_eq!(value(&run, &format!("v{i}")), *want, "{call} in\n{defs}");
    }
}

#[test]
fn else_strips_the_loose_atoms_in_each_place_an_expression_stands() {
    // (case, definition of `f`, signature, calls and their values)
    let cases: [(&str, String, &str, Calls); 7] = [
        (
            "argument",
            format!("g(positional n: int) = n * 2;\nf({LOOKUP}) = g(x else 1);\n"),
            "(int | #none | #notFound) -> int",
            &[("f(#none)", "2"), ("f(#notFound)", "2"), ("f(4)", "8")],
        ),
        (
            "operand",
            format!("f({LOOKUP}) = (x else 0) + 1;\n"),
            "(int | #none | #notFound) -> int",
            &[("f(#none)", "1"), ("f(4)", "5")],
        ),
        (
            "tuple component",
            format!("f({LOOKUP}) = (x else 0, 1);\n"),
            "",
            &[("f(#none)", "(0, 1)"), ("f(4)", "(4, 1)")],
        ),
        (
            "if branch",
            format!("f({LOOKUP}, positional c: bool) = if c {{ x else 0 }} else {{ 5 }};\n"),
            "",
            &[
                ("f(#none, true)", "0"),
                ("f(#none, false)", "5"),
                ("f(3, true)", "3"),
            ],
        ),
        (
            "if condition",
            "f(positional b: bool | #notFound) = if (b else false) { 1 } else { 2 };\n".into(),
            "(bool | #notFound) -> 1 | 2",
            &[("f(#notFound)", "2"), ("f(true)", "1"), ("f(false)", "2")],
        ),
        (
            "block statement and export",
            format!("f({LOOKUP}) = {{\n  y = x else 0;\n  y + 1\n}};\n"),
            "(int | #none | #notFound) -> int",
            &[("f(#notFound)", "1"), ("f(6)", "7")],
        ),
        (
            "nested in its own default",
            format!("f({TWO}) = x else (y else 0);\n"),
            "(int | #notFound, int | #none) -> int",
            &[
                ("f(#notFound, #none)", "0"),
                ("f(#notFound, 3)", "3"),
                ("f(2, #none)", "2"),
            ],
        ),
    ];
    for (case, defs, want, calls) in cases {
        assert!(
            type_errors(&defs).is_empty(),
            "{case}: {:?}",
            type_errors(&defs)
        );
        if !want.is_empty() {
            assert_eq!(sig(&defs, "f"), want, "{case}");
        }
        let s = sig(&defs, "f");
        let result = &s[s.rfind("->").unwrap()..];
        assert!(!result.contains('#'), "{case}: a loose atom is left: {s}");
        values(&defs, calls);
    }
}

#[test]
fn an_else_in_a_lambda_body_handles_what_the_lambda_is_passed() {
    let t = format!("f({LOOKUP}) = ((y) -> y else 0)(x);\n");
    assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
    values(
        &t,
        &[("f(#none)", "0"), ("f(#notFound)", "0"), ("f(9)", "9")],
    );
}

#[test]
fn a_default_that_may_fail_or_is_an_atom_puts_its_own_atoms_in_the_type() {
    // `e else d` strips the loose atoms of `e`; those of `d` are the default's, and stay.
    let t = format!("f({TWO}) = x else y;\n");
    assert_eq!(
        sig(&t, "f"),
        "type T1 = int | #none;\n(int | #notFound, T1) -> T1"
    );
    values(
        &t,
        &[
            ("f(#notFound, #none)", "#none"),
            ("f(#notFound, 2)", "2"),
            ("f(1, #none)", "1"),
        ],
    );
    // An atom default is the value the text names.
    let t = format!("f({LOOKUP}) = x else #missing;\n");
    assert_eq!(sig(&t, "f"), "(int | #none | #notFound) -> int | #missing");
    values(&t, &[("f(#none)", "#missing"), ("f(5)", "5")]);
    // The pattern form with an atom default keeps the atoms it does not name.
    let t = format!("f({LOOKUP}) = x else #notFound -> #missing;\n");
    assert_eq!(
        sig(&t, "f"),
        "(int | #none | #notFound) -> int | #missing | #none"
    );
    values(&t, &[("f(#none)", "#none"), ("f(#notFound)", "#missing")]);
}

#[test]
fn else_on_a_value_with_no_loose_atom_leaves_the_value() {
    // The default can never be taken; DESIGN.md warns at such an `else` from step L2.12e, and
    // it is no error.
    let t = "f(positional x: int) = x else 0;\n";
    assert!(type_errors(t).is_empty(), "{:?}", type_errors(t));
    assert_eq!(sig(t, "f"), "(int) -> int");
    values(t, &[("f(-3)", "-3")]);
}

#[test]
fn else_after_safe_navigation_strips_what_it_carried() {
    let t = "f(positional x: int | #notFound) = x?.abs else 0;\n";
    assert_eq!(sig(t, "f"), "(int | #notFound) -> int");
    values(t, &[("f(#notFound)", "0"), ("f(-4)", "4")]);
}

#[test]
fn the_pattern_form_on_a_merged_failure() {
    // Naming `#errs` handles the merge and keeps the single failures.
    let t = format!("f({TWO}) = (x + y) else #errs -> 0;\n");
    assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
    assert_eq!(
        sig(&t, "f"),
        "(int | #notFound, int | #none) -> int | #none | #notFound"
    );
    values(
        &t,
        &[
            ("f(#notFound, #none)", "0"),
            ("f(#notFound, 1)", "#notFound"),
            ("f(1, #none)", "#none"),
        ],
    );
    // Naming one member handles that member alone, never a merge that holds it.
    let t = format!("f({TWO}) = (x + y) else #notFound -> 0;\n");
    assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
    let s = sig(&t, "f");
    assert!(s.contains("#errs") && s.contains("#none"), "{s}");
    assert!(!s.ends_with("#notFound"), "{s}");
    values(
        &t,
        &[
            ("f(#notFound, #none)", "#errs({#none, #notFound})"),
            ("f(#notFound, 1)", "0"),
        ],
    );
}

#[test]
fn failures_of_two_arguments_of_a_call_merge_as_those_of_two_operands_do() {
    // DESIGN.md sec:failure, "All or the failures": the positions take the place of the
    // operands.
    let t = format!("g(positional a: int, positional b: int) = a + b;\nf({TWO}) = g(x, y);\n");
    assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
    assert_eq!(
        sig(&t, "f"),
        "type T1 = #none | #notFound;\n(int | #notFound, int | #none) -> int | #errs(T1 ->? T1) | #none | #notFound"
    );
    values(
        &t,
        &[
            ("f(#notFound, #none)", "#errs({#none, #notFound})"),
            ("f(#notFound, 1)", "#notFound"),
            ("f(1, #none)", "#none"),
            ("f(1, 2)", "3"),
        ],
    );
    // Three arguments, three failures: one flat set.
    let t = "g(positional a: int, positional b: int, positional c: int) = a + b + c;\n\
             f(positional x: int | #a, positional y: int | #b, positional z: int | #c) = g(x, y, z);\n";
    values(
        t,
        &[
            ("f(#a, #b, #c)", "#errs({#a, #b, #c})"),
            ("f(#a, 1, #a)", "#a"),
        ],
    );
}

#[test]
fn a_unary_operator_passes_its_one_operands_failures_unmerged() {
    let t = format!("f({LOOKUP}) = -x;\n");
    assert_eq!(
        sig(&t, "f"),
        "type T1 = int | #none | #notFound;\n(T1) -> T1"
    );
    values(
        &t,
        &[
            ("f(#none)", "#none"),
            ("f(#notFound)", "#notFound"),
            ("f(3)", "-3"),
        ],
    );
}

#[test]
fn a_comparison_merges_the_failures_of_its_operands() {
    let t = format!("f({TWO}) = x < y;\n");
    assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
    let s = sig(&t, "f");
    assert!(
        s.contains("-> bool | #errs(") && s.ends_with("| #none | #notFound"),
        "{s}"
    );
    values(
        &t,
        &[
            ("f(#notFound, #none)", "#errs({#none, #notFound})"),
            ("f(#notFound, 1)", "#notFound"),
            ("f(1, 2)", "true"),
        ],
    );
}

/// The one error of `text`, of the row "Statement that writes nothing", and its first note.
fn dropped(text: &str) -> (String, String) {
    let (info, _) = info(text);
    assert_eq!(info.errors.len(), 1, "{text}: {:?}", info.errors);
    let e = &info.errors[0];
    assert_eq!(e.row, Some(Row::WritesNothing), "{text}: {e:?}");
    let n = &e.notes[0];
    let first = format!("{} [{}]", n.text, &text[n.span.start..n.span.end]);
    (e.message.clone(), first)
}

#[test]
fn underscore_drops_no_failure_passed_on_by_each_form() {
    let lookup = "lookup(positional k: int) = if k > 0 { k } else { #notFound };\n";
    let in_f = |bind: String| {
        format!(
            "{lookup}g(positional n: int) = n;\nf(positional k: int) = {{\n  {bind}\n  0\n}};\n"
        )
    };
    // (case, the value `_` binds inside `f`, which may be `#notFound` unnamed)
    for (case, e) in [
        ("safe navigation", "lookup(k)?.abs"),
        ("unary operator", "-lookup(k)"),
        ("comparison", "lookup(k) < 3"),
        ("argument of a call", "g(lookup(k))"),
        ("a default that may fail", "lookup(k) else lookup(k + 1)"),
        (
            "a pattern default that may fail",
            "lookup(k) else #notFound -> lookup(2)",
        ),
    ] {
        let (message, first) = dropped(&in_f(format!("_ = {e};")));
        assert!(
            message.starts_with("`_` drops a loose failure this value may be, #notFound:"),
            "{case}: {message}"
        );
        assert!(
            first.starts_with("the loose failure #notFound enters here [lookup("),
            "{case}: {first}"
        );
        // The default of an `else` on the whole value names it, and the binding is accepted.
        let t = in_f(format!("_ = ({e}) else #ok;"));
        assert!(
            type_errors(&t).is_empty(),
            "{case}: {t}: {:?}",
            type_errors(&t)
        );
    }
}

#[test]
fn underscore_in_a_local_function_is_checked_as_in_any_body() {
    let lookup = "lookup(positional k: int) = if k > 0 { k } else { #notFound };\n";
    let t = format!(
        "{lookup}f(positional n: int) = {{\n  h(k: int) = {{\n    _ = lookup(k);\n    1\n  }};\n  h(k: n)\n}};\n"
    );
    let (message, _) = dropped(&t);
    assert!(
        message.starts_with("`_` drops a loose failure this value may be, #notFound:"),
        "{message}"
    );
    let t = t.replace("_ = lookup(k);", "_ = lookup(k) else #ok;");
    assert!(type_errors(&t).is_empty(), "{t}: {:?}", type_errors(&t));
}

#[test]
fn underscore_drops_a_value_with_no_failure() {
    for bind in ["_ = 3;", "_ = n + 1;", "_ = (n, \"a\");", "_ = n > 2;"] {
        let t = format!("f(positional n: int) = {{\n  {bind}\n  0\n}};\n");
        assert!(type_errors(&t).is_empty(), "{bind}: {:?}", type_errors(&t));
    }
}

#[test]
fn underscore_drops_no_failure_of_a_lookup_or_a_member_read() {
    // A lookup into a family may be `#notFound` (DESIGN.md sec:failure); a member read passes
    // on the failures of the value it reads.
    let lookup = "lookup(positional k: int) = if k > 0 { k } else { #notFound };\n";
    for (case, params, e) in [
        (
            "lookup",
            "positional m: int ->? int, positional k: int",
            "m[k]",
        ),
        ("member read", "positional k: int", "lookup(k).abs"),
    ] {
        let t = format!("{lookup}f({params}) = {{\n  _ = {e};\n  0\n}};\n");
        let (message, _) = dropped(&t);
        assert!(
            message.starts_with("`_` drops a loose failure this value may be, #notFound:"),
            "{case}: {message}"
        );
        let t = format!("{lookup}f({params}) = {{\n  _ = ({e}) else #ok;\n  0\n}};\n");
        assert!(
            type_errors(&t).is_empty(),
            "{case}: {t}: {:?}",
            type_errors(&t)
        );
    }
}
