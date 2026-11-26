//! The integers of the compiler `zedc`'s constraint store: [`int::Int`], a machine word until it
//! overflows, then a big integer. `zedc` re-exports the module at its old path
//! (`zedc::store::int`).

pub mod int;
pub mod q;

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
use zed_testkit::seed;
