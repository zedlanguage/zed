//! The texts the benchmarks of `bench.rs` build syntax trees from, and what each tree must be,
//! checked here at small sizes (TEST-bench-move-rest, P170).

use zed_tests::trees::parsed;
use zedc::ast::{Expr, ExprKind, UnaryOp, build};
use zedc::lex::Token;
use zedc::parse::Tree;

/// A text, its tokens and its parse tree.
pub(super) type Parsed = (String, Vec<Token>, Tree);

/// A benchmark: its text of size `n`, and what the syntax tree built from it must be.
pub(super) struct Case {
    pub(super) text: fn(usize) -> String,
    pub(super) holds: fn(&Expr, usize),
}

/// A chain of `4n` links; the tree is a member access at the top.
pub(super) const CHAIN: Case = Case {
    text: |n| format!("x{}", ".f(a, b: c)[i]?.g".repeat(n)),
    holds: |e, _| assert!(matches!(e.kind, ExprKind::Member { .. })),
};

/// `f((-` nested `n` deep around `1`; the tree is `n` calls of one negated argument each,
/// down to the integer `1`.
pub(super) const NEGATIONS: Case = Case {
    text: |n| format!("{}1{}", "f((-".repeat(n), "))".repeat(n)),
    holds: |e, n| {
        let (mut e, mut depth) = (e, 0);
        while let ExprKind::Call { positional, .. } = &e.kind
            && let [arg] = positional.as_slice()
            && let ExprKind::Unary(UnaryOp::Neg, inner) = &arg.kind
        {
            (e, depth) = (inner, depth + 1);
        }
        assert_eq!(depth, n);
        assert!(matches!(&e.kind, ExprKind::Int { digits, .. } if digits.as_str() == "1"));
    },
};

/// String holes nested `n` deep around `1`; the tree is a string.
pub(super) const HOLES: Case = Case {
    text: |n| format!("{}1{}", "\"${".repeat(n), "}\"".repeat(n)),
    holds: |e, _| assert!(matches!(e.kind, ExprKind::Str(_))),
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
    for case in [CHAIN, NEGATIONS, HOLES] {
        for n in [1, 2, 9] {
            builds(&case, &parsed((case.text)(n), "Expr"), n);
        }
    }
}
