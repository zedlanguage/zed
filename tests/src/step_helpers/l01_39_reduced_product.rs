//! Helpers of step L1.39 (tests/steps/l01_39_reduced_product and l01_39_scope_relations), some
//! shared with the hand-run probes of PERF-negated-chain-unsolved (`benches/src/bin/pncx_probe.rs`):
//! the scope of integer parameters, the arms of a function and the approval of `named_test.rs`
//! whose tiers stand side by side.

use std::sync::Arc;

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term};
use zedc::store::product::{Arm, Product, Scope, arms};

use crate::step_helpers::l01_16_elaboration::elab;
use crate::step_helpers::l01_25_preimage_catalog::{function, int_defs};

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

/// The arms of the function `ok` that `src` defines, its parameters integers: each written
/// without a type is declared `int` ([`int_defs`]), as a bare literal no longer fixes it
/// (L1.26a).
pub fn arms_of(src: &str) -> (Vec<Arc<str>>, Term, Vec<Arm>) {
    generic_arms_of(&int_defs(src))
}

/// [`arms_of`] with the parameters as written, integers in the scope: a literal compared with
/// one whose type is not written follows its carrier, by a `match` on it (L1.26a).
pub fn generic_arms_of(src: &str) -> (Vec<Arc<str>>, Term, Vec<Arm>) {
    let (ps, body) = function(src);
    let a = arms(&body, &ints(&ps));
    (ps, body, a)
}

/// The arm of `arms` whose test prints as containing `guard`, taken by `outcome`.
pub fn arm<'a>(arms: &'a [Arm], guard: &str, outcome: bool) -> &'a Arm {
    arms.iter()
        .find(|a| a.guard.contains(guard) && a.outcome == outcome)
        .unwrap_or_else(|| {
            let all: Vec<String> = arms.iter().map(|a| a.guard.clone()).collect();
            panic!("no arm with test `{guard}` and outcome {outcome} among {all:?}")
        })
}

/// The top-level binding `name` of the unit `src`, as a chain of `let` bindings.
pub fn binding(src: &str, name: &str) -> Term {
    elab(src)
        .unwrap_or_else(|e| panic!("{src}: {e:?}"))
        .get(name)
        .unwrap_or_else(|| panic!("{src}: no binding `{name}`"))
}
