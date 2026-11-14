//! Completeness of step L1.39b (row TEST-complete-reduced): a derivation is built only for a
//! unit that reports a rejection, and an exact preimage only for a scope declared `@exact`;
//! each counter counts this thread's work since it was last read. See `COMPLETENESS.md`.

use std::sync::Arc;

use zed_kernel::term::build::{lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term};
use zed_tests::scaling;
use zedc::check::derivation_steps;
use zedc::store::cell::Premises;
use zedc::store::preimage::exact_steps;
use zedc::store::product::{Product, Scope};

use super::{STACK, clean, counted, one_rejection};

/// A `main` that writes `a`, so that each program below is a whole unit.
fn with_main(defs: &str, a: &str) -> String {
    format!("{defs}main(m: MainArgs) {{\n  a = {a};\n  m.stdout <- \"a\" ++ String(a);\n}}\n")
}

#[test]
fn an_accepted_unit_of_each_construct_builds_no_derivation_and_no_preimage() {
    // Each construct whose check records origins, narrows or reads a domain: an `if` test
    // that narrows, a bit word under the tests that bound its operand, a failure handled by
    // `else`, a lambda, a tuple, a test table, a string word and a code point.
    let units = [
        with_main(
            "f(positional x: int) = if x >= 0 && x <= 10 && x mod 4 == 1 { x } else { 0 };\n",
            "f(5)",
        ),
        with_main(
            "f(positional x: int) = if x >= 0 && x < 256 { bitReverse(x, width: 8) } else { 0 };\n",
            "f(1)",
        ),
        with_main(
            "s(positional x: int) = scalar(x) else \"?\";\n",
            "s(-1) ++ s(65)",
        ),
        with_main("", "codePoint(\"a\") + len(\"ab\")"),
        with_main("g = x -> x * 2;\n", "g(3)"),
        with_main("t = (1, 2);\n", "t[0] + t[1]"),
        with_main(
            "h(positional x: int) = x + 1\ntest { 1 -> 2, 0 -> 1 }\n",
            "h(1)",
        ),
        with_main(
            "debug = false;\nmode = if debug { 1 } else { 2 };\n",
            "mode",
        ),
    ];
    scaling::on_a_thread(STACK, || {
        for src in &units {
            exact_steps();
            assert_eq!(counted(src), (Ok(()), 0), "{src}");
            assert_eq!(exact_steps(), 0, "{src}");
        }
    });
}

#[test]
fn each_kind_of_reported_rejection_builds_its_derivation() {
    // Rejections whose messages follow a value to where it came from: a condition of a
    // declared `int`, a declared parameter passed a value it does not take, a negative value
    // reaching a bit word through a name, and a value that reaches a use through a
    // parameter's default (DESIGN L1.29, MSG-flow-origin), whose notes name each default on
    // the way.
    let flow = "f(positional g) {\n  a = g(1) + 1;\n  k(positional h = g) = h(2);\n  \
                b = k(x -> \"s\");\n  return a;\n}\n\
                main(m: MainArgs) { m.stdout <- \"${f(x -> x + 1)}\"; }\n";
    let units = [
        (
            with_main("f(positional x: int) = if x { 1 } else { 2 };\n", "f(1)"),
            "`x` is declared `int`",
        ),
        (
            with_main("f(positional x: int) = x;\ny = \"a\";\n", "f(y)"),
            "`y`",
        ),
        (with_main("n = -1;\n", "bitReverse(n, width: 8)"), "-1"),
        (
            flow.to_string(),
            "the default `h = g` gives `h` the type of `g`",
        ),
    ];
    scaling::on_a_thread(STACK, || {
        for (src, note) in &units {
            let (r, built) = counted(src);
            let out = r.expect_err(src);
            assert!(out.contains(note), "{src}: {out}");
            assert!(built > 0, "{src}: {out}");
        }
    });
}

#[test]
fn one_rejection_of_a_fixed_size_builds_the_same_derivation_among_3_functions_and_24() {
    // The small instance of `bench::one_rejection_builds_the_same_derivation_among_n_functions_as_among_8n`.
    scaling::on_a_thread(STACK, || {
        let (r, small) = counted(&one_rejection(3));
        assert!(r.is_err());
        let (r, large) = counted(&one_rejection(24));
        assert!(r.is_err());
        assert!(small > 0);
        assert_eq!(small, large);
    });
}

#[test]
fn reading_a_counter_resets_it() {
    scaling::on_a_thread(STACK, || {
        let (_, built) = counted(&one_rejection(3));
        assert!(built > 0);
        assert_eq!(derivation_steps(), 0);
        // An accepted unit after a rejected one builds nothing.
        assert_eq!(counted(&clean(3)), (Ok(()), 0));
        assert!(boxes_of(&[true]) > 0);
        assert_eq!(exact_steps(), 0);
    });
}

#[test]
fn a_counter_counts_the_work_of_its_own_thread_only() {
    scaling::on_a_thread(STACK, || {
        derivation_steps();
        exact_steps();
        scaling::on_a_thread(STACK, || {
            let (r, built) = counted(&one_rejection(3));
            assert!(r.is_err());
            assert!(built > 0);
            assert!(boxes_of(&[true]) > 0);
        });
        assert_eq!(derivation_steps(), 0);
        assert_eq!(exact_steps(), 0);
    });
}

/// The scope of the integer `n` within `0..=30` with `n * n mod 10 == r` written, reduced;
/// exact or not.
fn squares_ending_in(r: i64, exact: bool) -> Scope {
    let names = [(Arc::from("n"), Product::of_type(Type::int()))];
    let s = if exact {
        Scope::exact(names)
    } else {
        Scope::new(names)
    };
    let range: Term = prim(
        Prim::And,
        vec![
            prim(Prim::Ge, vec![var("n"), lit(0)]),
            prim(Prim::Le, vec![var("n"), lit(30)]),
        ],
    );
    let mut s = s.assume(&range, true, &Premises::new());
    let nn = prim(Prim::Mul, vec![var("n"), var("n")]);
    s.write(prim(
        Prim::Eq,
        vec![prim(Prim::Mod, vec![nn, lit(10)]), lit(r)],
    ));
    s.reduce();
    s
}

/// The boxes searched for one scope of `squares_ending_in(9, _)` per entry, exact or not.
fn boxes_of(exact: &[bool]) -> u64 {
    exact_steps();
    for &e in exact {
        assert!(!squares_ending_in(9, e).bottom);
    }
    exact_steps()
}

#[test]
fn an_exact_scope_with_no_point_is_bottom_and_a_plain_one_is_not() {
    // No square ends in 7: only the exact scope finds that, by searching; the plain scope
    // keeps the interval and searches nothing (DESIGN sec:constraints, the store's `@exact`
    // test for emptiness).
    exact_steps();
    assert!(!squares_ending_in(7, false).bottom);
    assert_eq!(exact_steps(), 0);
    assert!(squares_ending_in(7, true).bottom);
    assert!(exact_steps() > 0);
}

#[test]
fn each_exact_scope_of_a_fixed_size_searches_the_same_boxes() {
    let one = boxes_of(&[true]);
    assert!(one > 0);
    assert_eq!(boxes_of(&[true, true]), 2 * one);
    assert_eq!(boxes_of(&[false, true, false, true, false]), 2 * one);
    assert_eq!(boxes_of(&[false; 8]), 0);
}

#[test]
fn source_exact_is_not_compiled_yet() {
    // The syntax of `@exact` is step L15.1; until then the source form is refused, so no
    // source unit reaches an exact search.
    for src in [
        "@exact\nf(positional x: int) = x;\n",
        "f(positional x: int) = @exact { x };\n",
    ] {
        let src = with_main(src, "f(1)");
        scaling::on_a_thread(STACK, || {
            exact_steps();
            let (r, _) = counted(&src);
            let out = r.expect_err(&src);
            assert!(out.contains("does not compile it yet"), "{src}: {out}");
            assert_eq!(exact_steps(), 0);
        });
    }
}
