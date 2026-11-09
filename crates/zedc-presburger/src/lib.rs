//! The Presburger arithmetic of the compiler `zedc`'s constraint store (DESIGN.md
//! sec:constraints, step L1.38): formulas over integer variables and the Omega test that decides
//! them, the conjunctions they are split into, and the convex hull of their pieces. `zedc`
//! re-exports each module at its old path (`zedc::store::presburger`, ...).

pub mod conjuncts;
pub mod hull;
pub mod presburger;

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/scaling.rs"]
#[expect(
    dead_code,
    reason = "presburger's tests hold no radix conversion or gcd to the log-squared limit (`check_log_squared`)"
)]
mod scaling;
