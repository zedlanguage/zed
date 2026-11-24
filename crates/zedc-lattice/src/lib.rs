//! The per-cell domains of the compiler `zedc`'s constraint store (DESIGN.md sec:domains):
//! integer interval unions with their landmarks, the congruence and finite-set lattices, affine
//! and float facts, the revision tables, the cell, the weak topological order and iteration
//! that widen loops, and the scheduler of a build's checks, evaluations and compilations
//! (`schedule`). `zedc` re-exports each module at its old path (`zedc::store::interval`, ...).

pub mod affine;
pub mod cell;
pub mod classed;
pub mod float;
pub mod float_kinds;
pub mod grade;
pub mod interval;
pub mod iterate;
pub mod landmarks;
pub mod lattice;
pub mod revision;
pub mod schedule;
pub mod wto;

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;
