//! The integers of the compiler `zedc`'s constraint store: [`int::Int`], a machine word until it
//! overflows, then a big integer. `zedc` re-exports the module at its old path (`zedc::store::int`).

pub mod int;

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
#[path = "../../../tests/src/seed.rs"]
#[allow(
    dead_code,
    reason = "each crate's tests use only some of the generator's draws"
)]
mod seed;
