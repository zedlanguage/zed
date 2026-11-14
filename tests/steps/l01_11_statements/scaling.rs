//! The texts the benchmarks of `bench.rs` build blocks from, and what each tree must be,
//! checked here at small sizes (TEST-bench-move-rest, P170).

use zed_tests::trees::parsed;
use zedc::ast::{Expr, ExprKind, StmtKind, build};
use zedc::lex::Token;
use zedc::parse::Tree;

/// A text, its tokens and its parse tree.
pub(super) type Parsed = (String, Vec<Token>, Tree);

/// A benchmark: its text of size `n`, and what the syntax tree built from it must be.
pub(super) struct Case {
    pub(super) text: fn(usize) -> String,
    pub(super) holds: fn(&Expr, usize),
}

/// A lambda whose block holds `n` destructuring bindings; the block has `n` bindings and
/// returns `x`.
pub(super) const LONG_BLOCK: Case = Case {
    text: |n| format!("x -> {{ {}x }}", "a, _ = x; ".repeat(n)),
    holds: |e, n| {
        let ExprKind::Lambda { body, .. } = &e.kind else {
            panic!("a lambda")
        };
        let ExprKind::Block(stmts) = &body.kind else {
            panic!("a block")
        };
        let binds = stmts
            .iter()
            .filter(|s| matches!(s.kind, StmtKind::Bind { .. }))
            .count();
        assert_eq!(
            (binds, stmts.last().unwrap().to_string()),
            (n, "(return x)".into())
        );
    },
};

/// Lambdas nested `n` deep, each a block of one binding and the next lambda; the tree has
/// that shape `n` deep, down to `x`.
pub(super) const NESTED_BLOCKS: Case = Case {
    text: |n| format!("{}x{}", "x -> { y = 1; ".repeat(n), " }".repeat(n)),
    holds: |e, n| {
        let (mut e, mut depth) = (e, 0);
        while let ExprKind::Lambda { body, .. } = &e.kind
            && let ExprKind::Block(stmts) = &body.kind
            && let [bind, ret] = stmts.as_slice()
            && let StmtKind::Bind { .. } = bind.kind
            && let StmtKind::Return(values) = &ret.kind
            && let [v] = values.as_slice()
        {
            (e, depth) = (v, depth + 1);
        }
        assert_eq!((depth, e.to_string()), (n, "x".into()));
    },
};

/// Builds the syntax tree of `(text, tokens, tree)`, the text of `case` at size `n`, and checks
/// it.
pub(super) fn builds(case: &Case, (text, tokens, tree): &Parsed, n: usize) {
    (case.holds)(&build(text, tokens, tree).unwrap(), n);
}

/// The tree of each benchmark's text is built and has its shape at small sizes; `bench.rs`
/// holds the timing.
#[test]
fn each_benchmark_text_builds_its_tree_at_small_sizes() {
    for case in [LONG_BLOCK, NESTED_BLOCKS] {
        for n in [1, 2, 9] {
            builds(&case, &parsed((case.text)(n), "Expr"), n);
        }
    }
}
