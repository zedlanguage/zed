//! The units the benchmarks of `bench.rs` build and write, and what each must give, checked
//! here at small sizes (TEST-bench-move-rest, P170), and the text of functions nested deeper
//! than the call stack.

use zed_tests::trees::parsed;
use zedc::ast::{ExprKind, Stmt, StmtKind, unit};
use zedc::lex::Token;
use zedc::parse::Tree;

/// A text, its tokens and its parse tree.
pub(super) type Parsed = (String, Vec<Token>, Tree);

/// A benchmark of building: its unit of size `n`, and what the statements built from it must
/// be.
pub(super) struct Case {
    pub(super) text: fn(usize) -> String,
    pub(super) holds: fn(&[Stmt], usize),
}

/// The statements of the unit `text`.
pub(super) fn statements(text: String) -> Vec<Stmt> {
    let (text, tokens, tree) = parsed(text, "Unit");
    unit(&text, &tokens, &tree).unwrap()
}

/// `n` functions `f`, each nested in the block of the one before, around `x`.
pub(super) fn nested(n: usize) -> String {
    format!("{}x{}", "f(x) { ".repeat(n), " }".repeat(n))
}

/// `n` functions with a test table of one row, and a function whose table has `n` rows.
pub(super) const MANY_FUNCTIONS: Case = Case {
    text: |n| {
        format!(
            "{}g(x) = x test {{ {}}}",
            "f(x) = x test { 1 -> 1 }\n".repeat(n),
            "1 -> 1, ".repeat(n)
        )
    },
    holds: |stmts, n| {
        let StmtKind::Function(g) = &stmts.last().unwrap().kind else {
            panic!("a function")
        };
        assert_eq!((stmts.len(), g.tests.len()), (n + 1, n));
    },
};

/// Functions nested `n` deep; the one statement has that depth of functions, down to
/// `(return x)`.
pub(super) const NESTED_FUNCTIONS: Case = Case {
    text: nested,
    holds: |stmts, n| {
        let [s] = stmts else { panic!("one statement") };
        let (mut s, mut depth) = (s, 0);
        while let StmtKind::Function(f) = &s.kind
            && let ExprKind::Block(stmts) = &f.body.kind
            && let [inner, ..] = stmts.as_slice()
        {
            (s, depth) = (inner, depth + 1);
        }
        assert_eq!((depth, s.to_string()), (n, "(return x)".into()));
    },
};

/// A function whose body is an `else if` chain of `n` links.
pub(super) const ELSE_IF_CHAIN: Case = Case {
    text: |n| format!("f(x) = {}{{ 0 }};", "if x { 1 } else ".repeat(n)),
    holds: |stmts, n| {
        let StmtKind::Function(f) = &stmts[0].kind else {
            panic!("a function")
        };
        let (mut e, mut length) = (&f.body, 0);
        while let ExprKind::If { otherwise, .. } = &e.kind {
            (e, length) = (otherwise, length + 1);
        }
        assert_eq!(length, n);
    },
};

/// Builds the statements of `(text, tokens, tree)`, the unit of `case` at size `n`, and checks
/// them.
pub(super) fn builds(case: &Case, (text, tokens, tree): &Parsed, n: usize) {
    (case.holds)(&unit(text, tokens, tree).unwrap(), n);
}

/// The statements of functions nested `n` deep, and of `y = a0 + a1 + … ;`, a sum of `4n`
/// terms, built before their text is written.
pub(super) fn texts(n: usize) -> (Vec<Stmt>, Vec<Stmt>) {
    let terms: Vec<String> = (0..4 * n).map(|i| format!("a{i}")).collect();
    let sum = statements(format!("y = {};", terms.join(" + ")));
    (statements(nested(n)), sum)
}

/// Writes the text of `def`, functions nested `n` deep, and of `sum`, a sum of `4n` terms, and
/// checks its length and start.
pub(super) fn texts_hold(def: &[Stmt], sum: &[Stmt], n: usize) {
    let (def, sum) = (def[0].to_string(), sum[0].to_string());
    // `(def f (x) (block ` and `))` at each level, and `(return x)` at the bottom.
    assert_eq!(def.len(), 20 * n + 10);
    let want = format!("(= (y) {}a0 a1)", "(+ ".repeat(4 * n - 1));
    assert!(
        sum.starts_with(&want),
        "{}",
        &sum[..want.len().min(sum.len())]
    );
}

/// Each benchmark's unit builds to its statements, and their text is written with its length
/// and start, at small sizes; `bench.rs` holds the timing.
#[test]
fn each_benchmark_unit_builds_and_is_written_at_small_sizes() {
    for case in [MANY_FUNCTIONS, NESTED_FUNCTIONS, ELSE_IF_CHAIN] {
        for n in [1, 2, 9] {
            builds(&case, &parsed((case.text)(n), "Unit"), n);
        }
    }
    for n in [1, 2, 9] {
        let (def, sum) = texts(n);
        texts_hold(&def, &sum, n);
    }
}

/// `main` with `n` bindings before the generation push `x' <- 1;`, which no loop holds.
pub(super) fn bindings_before_a_generation_push(n: usize) -> String {
    let lines: String = (0..n).map(|i| format!("  a{i} = {i};\n")).collect();
    format!("main(m: MainArgs) {{\n{lines}  x' <- 1;\n  m.stdout <- \"b\";\n}}\n")
}

/// `n` functions, each a loop whose body holds a generation push.
pub(super) fn loops_with_generation_pushes(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!("f{i}(n: int) = loop {{ initial x = 0; x' <- x + 1; until x' >= n; }}.x;\n")
        })
        .collect()
}

/// The row a unit is refused in by the builder, or `None` when it builds.
pub(super) fn built_row(text: String) -> Option<zedc::rejection::Row> {
    let (text, tokens, tree) = parsed(text, "Unit");
    unit(&text, &tokens, &tree).err().map(|e| e.row.unwrap())
}

/// A generation push outside a loop is found after many statements, and many inside loops
/// are taken; `bench.rs` holds the timing of each (COMPLEXITY.md, PUSH-target-rules).
#[test]
fn generation_pushes_are_placed_at_small_sizes() {
    for n in [0, 1, 2, 9] {
        assert_eq!(
            built_row(bindings_before_a_generation_push(n)),
            Some(zedc::rejection::Row::GenerationPushOutsideLoop)
        );
        assert_eq!(built_row(loops_with_generation_pushes(n)), None);
    }
}

/// The text of functions nested a few deep, each level a `def` whose block holds the next;
/// the same 100,000 deep is in `bench.rs`.
#[test]
fn the_text_of_functions_nested_a_few_deep() {
    for n in [1, 2, 9] {
        let text = statements(nested(n))[0].to_string();
        assert!(text.starts_with(&"(def f (x) (block ".repeat(n)), "{text}");
        assert!(
            text.ends_with(&format!("(block (return x))){}", "))".repeat(n - 1))),
            "{text}"
        );
    }
}
