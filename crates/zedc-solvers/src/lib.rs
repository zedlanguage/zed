//! The linear solvers of the compiler `zedc`'s constraint store (DESIGN.md sec:constraints):
//! linear terms over the rationals, the two-variable and three-variable deciders, the
//! negative-cycle search and the unit two-variable-per-inequality closure. `zedc` re-exports each
//! module at its old path (`zedc::store::linear`, ...).

pub mod linear;
pub mod live3;
pub mod negsssp;
pub mod twovar;
pub mod utvpi;

/// The seed of a random test, new on each run and printed, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
mod seed;
