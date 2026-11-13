//! The backward transfer of the compiler `zedc`'s store (DESIGN.md sec:domains): the preimage of a
//! test's condition, the reference transfer it is compared with, and the reduced product of the
//! domains. `zedc` re-exports each module at its old path (`zedc::store::preimage`, ...).

pub mod address;
mod divisors;
mod holes;
pub mod images;
pub mod loops;
pub mod preimage;
/// The backward transfer before S22a, which tests compare [`preimage`] with. Built only with
/// the feature `preimage-ref`, which only zed-tests enables (through zedc).
#[cfg(feature = "preimage-ref")]
#[doc(hidden)]
pub mod preimage_ref;
pub mod product;
mod shared_ints;
pub mod threshold;

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
#[path = "../../../tests/src/scaling.rs"]
#[expect(
    dead_code,
    reason = "preimage's tests build no input before a timed run (`inputs`)"
)]
mod scaling;
