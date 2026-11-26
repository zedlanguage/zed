//! The types of the compiler `zedc`'s checker (DESIGN.md sec:types): the checker's type, its
//! signatures and classes, its printing, and the kernel type a written type denotes. `zedc`
//! re-exports each module at its old path (`zedc::check::ty`, ...).

pub mod forms;
pub mod kernel_type;
pub mod ty;

/// The seed and generator of a random test, new on each run and printed, shared with the step
/// tests.
#[cfg(test)]
use zed_testkit::seed;

/// The scaling test of the rule of low complexity, shared with the step tests.
#[cfg(test)]
use zed_testkit::scaling;

// The meter's `malloc` in this crate's test binary, which `scaling` measures each run with
// (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
#[cfg(test)]
zed_alloc_count::meter_entry_points!();
