//! Building units and writing their text are of order n log n in the length of the text, and
//! the depth of nested functions and `else if` chains is bounded by memory alone (DESIGN.md
//! Part G). Each text is lexed and parsed before timing, so the checks time the building, or
//! the writing, alone.

use zed_tests::scaling::{check, inputs};
use zed_tests::trees::parsed;
use zedc::ast::{ExprKind, Stmt, StmtKind, unit};

/// The statements of the unit `text`.
fn statements(text: String) -> Vec<Stmt> {
    let (text, tokens, tree) = parsed(text, "Unit");
    unit(&text, &tokens, &tree).unwrap()
}

/// `n` functions `f`, each nested in the block of the one before, around `x`.
fn nested(n: usize) -> String {
    format!("{}x{}", "f(x) { ".repeat(n), " }".repeat(n))
}

#[test]
fn many_functions_and_a_long_test_table_scale() {
    let built = inputs(200, |n| {
        let text = format!(
            "{}g(x) = x test {{ {}}}",
            "f(x) = x test { 1 -> 1 }\n".repeat(n),
            "1 -> 1, ".repeat(n)
        );
        parsed(text, "Unit")
    });
    check("building n functions and a table of n rows", 200, |n| {
        let (text, tokens, tree) = &built[&n];
        let stmts = unit(text, tokens, tree).unwrap();
        let StmtKind::Function(g) = &stmts.last().unwrap().kind else {
            panic!("a function")
        };
        assert_eq!((stmts.len(), g.tests.len()), (n + 1, n));
    });
}

#[test]
fn nested_functions_scale() {
    let built = inputs(200, |n| parsed(nested(n), "Unit"));
    check("building functions nested n deep", 200, |n| {
        let (text, tokens, tree) = &built[&n];
        let stmts = unit(text, tokens, tree).unwrap();
        let [s] = stmts.as_slice() else {
            panic!("one statement")
        };
        let (mut s, mut depth) = (s, 0);
        while let StmtKind::Function(f) = &s.kind
            && let ExprKind::Block(stmts) = &f.body.kind
            && let [inner, ..] = stmts.as_slice()
        {
            (s, depth) = (inner, depth + 1);
        }
        assert_eq!((depth, s.to_string()), (n, "(return x)".into()));
    });
}

#[test]
fn the_text_of_nested_functions_and_of_a_long_sum_scales() {
    let built = inputs(125, |n| {
        let terms: Vec<String> = (0..4 * n).map(|i| format!("a{i}")).collect();
        let sum = statements(format!("y = {};", terms.join(" + ")));
        (statements(nested(n)), sum)
    });
    check(
        "writing functions nested n deep and a sum of 4n terms",
        125,
        |n| {
            let (def, sum) = &built[&n];
            let (def, sum) = (def[0].to_string(), sum[0].to_string());
            // `(def f (x) (block ` and `))` at each level, and `(return x)` at the bottom.
            assert_eq!(def.len(), 20 * n + 10);
            let want = format!("(= (y) {}a0 a1)", "(+ ".repeat(4 * n - 1));
            assert!(
                sum.starts_with(&want),
                "{}",
                &sum[..want.len().min(sum.len())]
            );
        },
    );
}

#[test]
fn the_text_of_functions_nested_deeper_than_the_call_stack() {
    let n = 100_000;
    let text = statements(nested(n))[0].to_string();
    assert!(text.starts_with(&"(def f (x) (block ".repeat(1000)));
    assert!(text.ends_with(&format!("(block (return x))){}", "))".repeat(n - 1))));
}

#[test]
fn a_long_else_if_chain_scales() {
    let built = inputs(200, |n| {
        parsed(
            format!("f(x) = {}{{ 0 }};", "if x { 1 } else ".repeat(n)),
            "Unit",
        )
    });
    check("building an else if chain of n links", 200, |n| {
        let (text, tokens, tree) = &built[&n];
        let stmts = unit(text, tokens, tree).unwrap();
        let StmtKind::Function(f) = &stmts[0].kind else {
            panic!("a function")
        };
        let (mut e, mut length) = (&f.body, 0);
        while let ExprKind::If { otherwise, .. } = &e.kind {
            (e, length) = (otherwise, length + 1);
        }
        assert_eq!(length, n);
    });
}
