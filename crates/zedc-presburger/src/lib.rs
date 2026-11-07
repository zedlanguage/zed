//! The Presburger arithmetic of the compiler `zedc`'s constraint store (DESIGN.md
//! sec:constraints, step L1.38): formulas over integer variables and the Omega test that decides
//! them, the conjunctions they are split into, and the convex hull of their pieces. `zedc`
//! re-exports each module at its old path (`zedc::store::presburger`, ...).

pub mod conjuncts;
pub mod hull;
pub mod presburger;
