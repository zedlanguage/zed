//! Helpers of step L1.39 (tests/steps/l01_39_reduced_product) shared with the hand-run probes of
//! PERF-negated-chain-unsolved (`benches/src/bin/pncx_probe.rs`): the scope of integer
//! parameters, and the approval of `named_test.rs` whose tiers stand side by side.

use std::sync::Arc;

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term};
use zedc::store::product::{Product, Scope};

/// The scope of integer parameters `ps`, known only when the program runs.
pub fn ints(ps: &[Arc<str>]) -> Scope {
    Scope::new(
        ps.iter()
            .map(|p| (p.clone(), Product::of_type(Type::int()))),
    )
}

/// The comparison `p` of the name `n` with the number `v`.
pub fn cmp(p: Prim, n: &str, v: i64) -> Term {
    prim(p, vec![var(n), lit(v)])
}

/// `n >= v`.
pub fn ge(n: &str, v: i64) -> Term {
    cmp(Prim::Ge, n, v)
}

/// `n <= v`.
pub fn le(n: &str, v: i64) -> Term {
    cmp(Prim::Le, n, v)
}

/// The conjunction of `ts`, of which there is at least one.
pub fn all(ts: Vec<Term>) -> Term {
    ts.into_iter()
        .reduce(|a, b| prim(Prim::And, vec![a, b]))
        .expect("a part")
}

/// `a || b`.
pub fn either(a: Term, b: Term) -> Term {
    prim(Prim::Or, vec![a, b])
}

/// The names of the approval: the balance `x`, the credit `y`, the limits `u` and `q`, the size
/// `z` and the waiting time `w`.
pub fn names() -> Vec<Arc<str>> {
    ["x", "y", "u", "q", "z", "w"].map(Into::into).into()
}

/// The credit limits, `k` of them: `x + j y >= j` for each `j` below `k`, one for each kind of
/// account, on the balance `x` and the credit `y`.
pub fn limits(k: usize) -> Vec<Term> {
    (0..k as i64)
        .map(|j| {
            let line = prim(
                Prim::Add,
                vec![var("x"), prim(Prim::Mul, vec![lit(j), var("y")])],
            );
            prim(Prim::Ge, vec![line, lit(j)])
        })
        .collect()
}

/// The approval where any of `d` tiers approves, tier `i` a request of size `z` at most `i`
/// that waited at least `i`, each tier needing every one of `k` credit limits, named once.
/// The tiers are side by side, so the limits are a conjunct of each disjunct.
pub fn approval_any_tier(d: usize, k: usize, named: bool) -> Term {
    let tiers = |t: &dyn Fn() -> Term| {
        (0..d as i64)
            .map(|i| all(vec![t(), ge("w", i), le("z", i)]))
            .reduce(either)
            .expect("a tier")
    };
    if named {
        let_("t", all(limits(k)), tiers(&|| var("t")))
    } else {
        tiers(&|| all(limits(k)))
    }
}
